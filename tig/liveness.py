"""Registers and flags a timing proof can ignore.

Picinae's ignore_vars replaces each value assigned to a listed variable with a
fresh opaque one, which keeps symbolic states small. A variable can be ignored
if it is dead after every instruction that writes it. Liveness is computed
backwards over the CFG from P-Code def/use information, starting from:

  * registers that instruction times depend on,
  * registers in the loop invariant,
  * conditions of branches whose direction the proof needs: those whose taken
    and not-taken times differ, and those the iteration count comes from.

The stepper follows both directions of any other branch. If the result is
wrong, the generated proof fails to check.
"""
from typing import Dict, Iterable, List, Optional, Set, Tuple

import pypcode

from tig.bininfo import Function

MEM = "MEM"

# Picinae names of Ghidra's flag registers
_FLAGS = {
    "armv6m": {"NG": "F_N", "ZR": "F_Z", "CY": "F_C", "OV": "F_V"},
    "amd64": {f: "R_" + f for f in ("CF", "PF", "AF", "ZF", "SF", "OF", "DF")},
    "riscv": {},
}


class InstrEffect:
    """What an instruction reads and writes, in Picinae variable names."""

    def __init__(self):
        self.writes: Dict[str, Set[str]] = {}   # variable -> what its new value depends on
        self.kills: Set[str] = set()            # variables fully overwritten
        self.uses: Set[str] = set()             # read by control flow or timing
        self.call = False                       # callee may read anything


class Liveness:
    def __init__(self, arch, project, func: Function, branches: Optional[Set[int]] = None):
        """branches: addresses of branches whose conditions the proof needs,
        besides those whose taken and not-taken times differ. None means all."""
        self.arch, self.func = arch, func
        self.branches = branches
        self.ctx = pypcode.Context(project.arch.name)
        self.mem = project.loader.memory
        self.flags = _FLAGS[arch.name]

    def _var(self, vn) -> Tuple[Optional[str], bool]:
        """(Picinae variable, whether the varnode covers all of it), or
        (None, False) for a register Picinae does not model."""
        name = self.ctx.getRegisterName(vn.space, vn.offset, vn.size)
        if name in self.flags:
            return self.flags[name], True
        if not name:
            # part of a register
            for size in (8, 4, 2):
                base = vn.offset - vn.offset % size
                name = self.ctx.getRegisterName(vn.space, base, size)
                if name:
                    break
            full = False
        else:
            full = True
        reg = self.arch.canon(name) if name else None
        if not isinstance(reg, str) or reg not in self.arch.gprs:
            return None, False
        if self.arch.name == "amd64":
            full = full and vn.size >= 4  # 32-bit writes zero-extend
        return self.arch.reg(reg), full

    def effect(self, addr: int, size: int) -> InstrEffect:
        eff = InstrEffect()
        code = self.mem.load(addr, size)
        local: Dict[Tuple, Set[str]] = {}   # temporaries and unmodeled registers

        def deps(vn) -> Set[str]:
            sp = vn.space.name
            if sp == "const":
                return set()
            if sp == "register":
                var, _ = self._var(vn)
                if var is None:
                    return set(local.get(("register", vn.offset, vn.size), set()))
                return set(eff.writes[var]) if var in eff.writes else {var}
            if sp == "unique":
                return set(local.get(("unique", vn.offset, vn.size), set()))
            return {MEM}

        def write(vn, d: Set[str]):
            sp = vn.space.name
            if sp == "register":
                var, full = self._var(vn)
                if var is None:
                    local[("register", vn.offset, vn.size)] = d
                    return
                if not full:
                    d = d | ({var} if var not in eff.writes else eff.writes[var])
                eff.writes[var] = d
                if full:
                    eff.kills.add(var)
            elif sp == "unique":
                local[("unique", vn.offset, vn.size)] = d
            else:
                eff.writes[MEM] = eff.writes.get(MEM, {MEM}) | d

        try:
            tr = self.ctx.translate(code, addr, max_instructions=1)
        except Exception:
            # not in pypcode's spec (Zbb andn, which TIG hooks): assume it
            # writes its first operand from all of them
            ins = next(i for b in self.func.blocks for i in b.instructions if i.offset == addr)
            regs = [self.arch.reg(r) for r in self.arch.operand_regs(ins)]
            if regs:
                eff.writes[regs[0]] = set(regs)
                eff.uses |= set(regs)
            return eff
        O = pypcode.OpCode
        for op in tr.ops:
            oc = op.opcode
            if oc == O.IMARK:
                continue
            ins = list(op.inputs)
            if oc == O.LOAD:
                write(op.output, deps(ins[1]) | {MEM})
            elif oc == O.STORE:
                eff.writes[MEM] = eff.writes.get(MEM, {MEM}) | deps(ins[1]) | deps(ins[2])
            elif oc == O.CBRANCH:
                if self._needed(addr):
                    eff.uses |= deps(ins[1])
            elif oc == O.BRANCHIND:
                eff.uses |= deps(ins[0])
            elif oc in (O.CALL, O.CALLIND):
                eff.call = True
            elif oc in (O.BRANCH, O.RETURN):
                pass
            elif op.output is not None:
                d = set()
                for v in ins:
                    d |= deps(v)
                write(op.output, d)
        return eff

    def _needed(self, addr: int) -> bool:
        if self.branches is None or addr in self.branches:
            return True
        b = next((b for b in self.func.blocks if b.instructions[-1].offset == addr), None)
        if b is None:
            return True
        tt, tf = self.arch.branch_times(b.instructions[-1])
        return tt != tf

    def ignorable(self, roots: Dict[int, Set[str]] = None) -> List[str]:
        """Variables dead after every write. roots maps a block address to
        variables live at its start."""
        from tig.loops import successors
        roots = roots or {}
        blocks = {b.start_vaddr: b for b in self.func.blocks}
        succ = successors(self.func)
        effects = {}
        for b in blocks.values():
            for i in b.instructions:
                e = self.effect(i.offset, i.size)
                for r in self.arch.state_args(i):
                    e.uses.add(self.arch.reg(r))
                effects[i.offset] = e

        live_in = {a: set() for a in blocks}
        changed = True
        while changed:
            changed = False
            for a, b in blocks.items():
                live = set()
                for s in succ.get(a, ()):
                    live |= live_in.get(s, set())
                for i in reversed(b.instructions):
                    live = self._transfer(effects[i.offset], live, self.everything)
                live |= roots.get(a, set())
                if live != live_in[a]:
                    live_in[a], changed = live, True

        written, needed = set(), set()
        for a, b in blocks.items():
            live = set()
            for s in succ.get(a, ()):
                live |= live_in.get(s, set())
            for i in reversed(b.instructions):
                e = effects[i.offset]
                for v in e.writes:
                    written.add(v)
                    if v in live:
                        needed.add(v)
                live = self._transfer(e, live, self.everything)
        return sorted(v for v in written - needed if v != MEM)

    @property
    def everything(self) -> Set[str]:
        return {self.arch.reg(r) for r in self.arch.gprs} | set(self.flags.values()) | {MEM}

    @staticmethod
    def _transfer(e: InstrEffect, live: Set[str], everything: Set[str]) -> Set[str]:
        """Variables live before an instruction, given those live after it."""
        out = set(live) - e.kills
        for v, d in e.writes.items():
            if v in live:
                out |= d
        if e.call:
            out |= everything
        return out | e.uses


def ignore_vars_ltac(arch, ignored: Iterable[str]) -> str:
    """ignore_vars override for a generated proof."""
    ignored = list(ignored)
    if not ignored:
        return ""
    return (f"    (* TIG: variables that do not affect timing *)\n"
            f"    Ltac {arch.proof['isa']}.ignore_vars v ::= constr:(match v with\n"
            f"        {' | '.join(ignored)} => true | _ => false end).\n")
