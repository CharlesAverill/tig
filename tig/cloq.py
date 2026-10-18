"""Cloq backend: emit timing postconditions and proofs for the current Cloq API.

The legacy synthesizer (tig.proof_synthesis) targets an older Picinae timing
API with hard-coded NEORV32 cycle counts.  This backend instead

  * names instruction times after the CPUTimingBehavior parameters that Cloq's
    timing modules use (taddi, ttbne, tldr_imm, ...), so proofs stay CPU-agnostic;
  * prints branch conditions and state-dependent timing arguments directly from
    angr's ASTs as Rocq terms over the function's inputs (initial registers and
    memory), using Picinae's modular-arithmetic notation;
  * distinguishes taken from not-taken branches by comparing the successor with
    the branch's fall-through address;
  * emits a complete proof file (entry/exit invariants plus a generic
    `repeat step; hammer` script) that can be checked by Rocq.
"""
import re
from typing import Dict, List, Optional, Tuple

import claripy

from tig.bininfo import Function, Instruction


class Unsupported(Exception):
    """Raised for programs or expressions the backend cannot express."""


# --------------------------------------------------------------------------
# Architecture descriptions
# --------------------------------------------------------------------------

def _riscv_imm(op: str) -> int:
    return int(op, 0)


class RISCV:
    name = "riscv"
    lang = "RISCV:LE:32:default"
    width = 32
    mem_var = "V_MEM32"
    branch_mnems = {"beq", "bne", "blt", "bge", "bltu", "bgeu"}
    # Instructions whose Cloq time depends on a register's pre-instruction
    # value (RISCVTiming.v: R5_Sll rd _ _ => tsll (regvalue s rd), etc.).
    state_dep = {"sll": "tsll", "srl": "tsrl", "sra": "tsra", "clz": "tclz"}
    simple = {m: "t" + m for m in
              "add addi slt slti sltu sltiu xor xori or ori and andi sub lui auipc "
              "jal jalr lb lh lw lbu lhu sb sh sw mul mulh mulhu div divu rem remu "
              "andn csrrw csrrs csrrc csrrwi csrrsi csrrci".split()}
    simple.update({"mulhsu": "tmulhsu", "fence": "tfence", "fence.i": "tfence"})

    @staticmethod
    def reg(name: str) -> str:
        return "R_" + name.upper()

    def state_args(self, instr: Instruction) -> List[str]:
        if instr.mnem in self.state_dep:
            rd = instr.operands[0]
            return [] if rd == "zero" else [rd]
        return []

    def instr_time(self, instr: Instruction, args: Tuple[str, ...]) -> str:
        m = instr.mnem
        if m in self.state_dep:
            return f"{self.state_dep[m]} ({args[0] if args else '0'})"
        if m in ("slli", "srli", "srai"):
            return f"t{m} {_riscv_imm(instr.operands[2])}"
        if m in self.simple:
            return self.simple[m]
        return "time_inf"  # decodes to an instruction Cloq does not time

    def is_branch(self, instr: Instruction) -> bool:
        return instr.mnem in self.branch_mnems

    def branch_times(self, instr: Instruction) -> Tuple[str, str]:
        m = instr.mnem
        return f"ttb{m[1:]}", f"tfb{m[1:]}"

    def is_return(self, instr: Instruction) -> bool:
        return instr.mnem == "jalr" and instr.operands[:2] == ["zero", "ra"]


def _split_operands(ops: str) -> List[str]:
    """Split a Ghidra operand string on commas outside brackets/braces."""
    out, depth, cur = [], 0, ""
    for c in ops:
        if c in "[{":
            depth += 1
        elif c in "]}":
            depth -= 1
        if c == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += c
    if cur.strip():
        out.append(cur.strip())
    return out


def _ghidra_ops(instr: Instruction) -> List[str]:
    parts = instr.instr_str.strip().split(None, 1)
    return _split_operands(parts[1]) if len(parts) > 1 else []


class ARMv6M:
    """Cortex-M0 (ARMv6-M Thumb), timed by ARMv6MTiming.v's decoder."""
    name = "armv6m"
    lang = "ARM:LE:32:Cortex"
    width = 32
    mem_var = "V_MEM32"
    conds = "eq ne cs cc hs lo mi pl vs vc hi ls ge lt gt le".split()
    branch_mnems = {"b" + c for c in conds}

    @staticmethod
    def reg(name: str) -> str:
        return "R_" + name.upper()

    def state_args(self, instr: Instruction) -> List[str]:
        return []

    @staticmethod
    def _norm(m: str) -> str:
        return m.lower().split(".")[0]

    def is_branch(self, instr: Instruction) -> bool:
        return self._norm(instr.mnem) in self.branch_mnems

    def instr_time(self, instr: Instruction, args) -> str:
        m = self._norm(instr.mnem)
        ops = [o.lower() for o in _ghidra_ops(instr)]
        imm = lambda o: o.startswith("#")
        reglist = lambda l: [r.strip() for r in re.sub(r"[{}]", "", l).split(",") if r.strip()]
        if m in ("push", "pop"):
            rl = reglist(",".join(ops))
            if m == "push":
                n = len([r for r in rl if r != "lr"])
                return f"(tpush_base + {n}{' + 1' if 'lr' in rl else ''})"
            n = len([r for r in rl if r != "pc"])
            # ARMv6MTiming: (if pc then tpop_pc_base + 1 else tpop_base) + #regs
            return f"(tpop_pc_base + 1 + {n})" if "pc" in rl else f"(tpop_base + {n})"
        if m in ("ldmia", "ldm", "stmia", "stm"):
            base = "tldm_base" if m.startswith("ld") else "tstm_base"
            return f"({base} + {len(reglist(','.join(ops[1:])))})"
        if m in ("ldr", "ldrb", "ldrh", "ldrsb", "ldrsh", "str", "strb", "strh"):
            mem = ",".join(ops[1:])
            # Ghidra prints PC-relative literal loads with the resolved address
            # (`ldr r0,[0x08000028]`), i.e. without a base register.
            if m == "ldr" and ("pc" in mem or not mem.startswith("[") or re.fullmatch(r"\[0x[0-9a-f]+\]", mem)):
                return "tldr_pc"
            if mem.startswith("[sp") and m in ("ldr", "str"):
                return f"t{m}_sp"
            inner = mem.strip("[]").split(",")
            form = "reg" if len(inner) > 1 and not inner[1].strip().startswith("#") else "imm"
            return f"t{m}_{form}"
        if m in ("adds", "subs"):
            if len(ops) == 3 and imm(ops[2]):
                return f"t{m}_imm3"
            if len(ops) == 2 and imm(ops[1]):
                return f"t{m}_imm8"
            return f"t{m}_3reg"
        if m == "add":
            if "sp" in ops and any(imm(o) for o in ops):
                return "tadd_sp_imm"
            return "tadd_pc" if ops and ops[0] == "pc" else "tadd_reg"
        if m == "sub" and ops and ops[0] == "sp":
            return "tsub_sp_imm"
        if m == "movs":
            return "tmovs_imm" if imm(ops[-1]) else "tmovs_reg"
        if m in ("mov", "cpy"):
            return "tmov_pc" if ops and ops[0] == "pc" else "tmov_reg"
        if m == "cmp":
            return "tcmp_imm" if imm(ops[-1]) else "tcmp_reg"
        if m in ("lsls", "lsrs", "asrs"):
            return f"t{m}_imm" if imm(ops[-1]) else f"t{m}_reg"
        if m in ("negs", "rsbs"):
            return "trsbs"
        if m in ("b", "bl", "bx", "blx", "muls", "ands", "eors", "orrs", "bics", "mvns", "tst",
                 "cmn", "adcs", "sbcs", "rors", "sxth", "sxtb", "uxth", "uxtb", "rev", "rev16",
                 "revsh", "nop", "sev", "wfe", "wfi", "yield", "dmb", "dsb", "isb", "cpsid",
                 "cpsie", "mrs", "msr", "adr"):
            return "t" + m
        return "time_inf"

    def branch_times(self, instr: Instruction) -> Tuple[str, str]:
        return "tb_taken", "tb_not_taken"

    def is_return(self, instr: Instruction) -> bool:
        m, ops = self._norm(instr.mnem), [o.lower() for o in _ghidra_ops(instr)]
        return (m == "bx" and ops == ["lr"]) or (m == "pop" and "pc" in ",".join(ops))


class AMD64:
    """x86-64.  Cloq's x86 proofs time each address with an operand-form name
    (mov_r64_m64, cmp_r64_i, jz_addr, ...) from amd64CPUTimingBehavior."""
    name = "amd64"
    lang = "x86:LE:64:default"
    width = 64
    mem_var = "V_MEM64"
    branch_mnems = {"jo", "jno", "jc", "jnc", "jb", "jnb", "jae", "jnae", "jz", "jnz", "je", "jne",
                    "jbe", "jnbe", "ja", "jna", "js", "jns", "jp", "jnp", "jpe", "jpo", "jl", "jnl",
                    "jge", "jnge", "jle", "jnle", "jg", "jng"}
    _ptr = {"byte": 8, "word": 16, "dword": 32, "qword": 64, "xmmword": 128}

    def __init__(self):
        w = {}
        for r in "rax rbx rcx rdx rsi rdi rbp rsp rip".split():
            w[r], w["e" + r[1:]], w[r[1:]] = 64, 32, 16
        for r in "al bl cl dl sil dil bpl spl ah bh ch dh".split():
            w[r] = 8
        for i in range(8, 16):
            w[f"r{i}"], w[f"r{i}d"], w[f"r{i}w"], w[f"r{i}b"] = 64, 32, 16, 8
        self._w = w

    @staticmethod
    def reg(name: str) -> str:
        return "R_" + name.upper()

    def state_args(self, instr: Instruction) -> List[str]:
        return []

    def is_branch(self, instr: Instruction) -> bool:
        return instr.mnem.lower() in self.branch_mnems

    def operand_kinds(self, instr: Instruction) -> List[str]:
        m = instr.mnem.lower()
        ops = [o.lower() for o in _ghidra_ops(instr)]
        regw = [self._w[o] for o in ops if o in self._w]
        kinds = []
        for o in ops:
            if o in self._w:
                kinds.append(f"r{self._w[o]}")
            elif "[" in o:
                if m == "lea":
                    kinds.append("addr")
                    continue
                size = next((w for p, w in self._ptr.items() if o.startswith(p + " ptr")), None)
                kinds.append(f"m{size or (regw[0] if regw else 64)}")
            elif m.startswith("j") or m == "call":
                kinds.append("addr")
            else:
                kinds.append("i")
        return kinds

    # Names that amd64CPUTimingBehavior declares (set from the model file when
    # available); a name the model lacks falls back to the reversed operand
    # order, which the model uses for both directions (cmp m64,r64 -> cmp_r64_m64).
    model_names: set = set()

    @classmethod
    def load_model(cls, path: str):
        src = open(path).read()
        cls.model_names = set(re.findall(r"\b[a-z][a-z0-9]*(?:_[a-z0-9]+)+\b", src))

    def instr_time(self, instr: Instruction, args) -> str:
        m = instr.mnem.lower()
        if m in ("ret", "nop", "leave", "hlt"):
            return m
        kinds = self.operand_kinds(instr)
        name = "_".join([m] + kinds)
        if self.model_names and name not in self.model_names:
            swapped = "_".join([m] + kinds[::-1])
            if swapped in self.model_names:
                return swapped
        return name

    def branch_times(self, instr: Instruction) -> Tuple[str, str]:
        t = self.instr_time(instr, ())
        return t, t  # Cloq's x86 timing does not distinguish taken branches

    def is_return(self, instr: Instruction) -> bool:
        return instr.mnem.lower() == "ret"


ARCHS = {"riscv": RISCV(), "armv6m": ARMv6M(), "amd64": AMD64()}


# --------------------------------------------------------------------------
# Expression printing
# --------------------------------------------------------------------------

class Printer:
    """Prints claripy ASTs as Rocq terms over the function's inputs."""

    def __init__(self, arch, mem_reads: Dict[str, Tuple[object, int]]):
        self.arch = arch
        self.mem_reads = mem_reads
        self.regs = set()       # initial registers referenced
        self.uses_mem = False   # initial memory referenced

    # -- leaves ------------------------------------------------------------
    def _getmem(self, addr: str, nbytes: int) -> str:
        self.uses_mem = True
        sym = {1: "Ⓑ", 2: "Ⓦ", 4: "Ⓓ", 8: "Ⓠ"}.get(nbytes)
        if sym is None:
            raise Unsupported(f"{nbytes}-byte load")
        return f"mem {sym}[{addr}]"

    def addr(self, e) -> str:
        """Print a load/store address the way Picinae's lifter leaves it:
        getmem reduces addresses modulo 2^w itself, so offsets stay unreduced
        (`16 + a0`), and negative offsets use modular subtraction (`gp ⊖ 1900`)."""
        if isinstance(e, int):
            return str(e)  # concrete address
        w = e.size()
        if e.op == "__add__":
            # getmem reduces the address mod 2^w, so nested sums flatten into
            # Picinae's left-associated form (92 + a0 + a1).
            def flat(x):
                return [y for a in x.args for y in flat(a)] if x.op == "__add__" else [x]
            terms = flat(e)
            consts = [x.args[0] for x in terms if x.op == "BVV"]
            others = [x for x in terms if x.op != "BVV"]
            c = sum(consts) % (1 << w)
            body = " + ".join(self.bv(x) for x in others) if others else "0"
            if c >= 1 << (w - 1) and len(others) > 1:
                body = f"({body})"
            if c == 0:
                return body
            if c >= 1 << (w - 1):
                return f"{body} ⊖ {(1 << w) - c}"
            return f"{c} + {body}"
        return self.bv(e)

    def _leaf_load(self, name: str) -> Optional[Tuple[str, int]]:
        """(address term, length) if `name` is the value of a load from the
        initial memory, else None."""
        # TIG's extension override (tig.memory_mixins) replaces an extended
        # load `v` with a wider variable named `v_<id>_<bits>`; it denotes the
        # same (zero-extended) value.
        while name not in self.mem_reads and re.search(r"_\d+_\d+$", name):
            base = name.rsplit("_", 2)[0]
            if base in self.mem_reads or re.match(r"(?:data|bss)_init_", base):
                name = base
                break
            name = base
        if name in self.mem_reads:
            addr, length = self.mem_reads[name]
            return self.addr(addr), length
        m = re.match(r"(?:data|bss)_init_(0x[0-9a-f]+)_", name)
        if m:
            return str(int(m.group(1), 16)), 4
        return None

    def _bvs(self, e) -> str:
        name = e.args[0]
        if name.startswith("reg_"):
            reg = name[len("reg_"):].rsplit("_", 2)[0].lower()
            self.regs.add(reg)
            return reg
        if name.startswith("CLZ_{"):
            inner = re.match(r"CLZ_\{(.+)\}", name).group(1)
            return f"(clz ({self._name(inner)}) {self.arch.width})"
        load = self._leaf_load(name)
        if load is not None:
            return self._getmem(load[0], load[1])
        raise Unsupported(f"unknown symbolic value {name}")

    def _name(self, name: str) -> str:
        if name.startswith("reg_"):
            reg = name[len("reg_"):].rsplit("_", 2)[0].lower()
            self.regs.add(reg)
            return reg
        load = self._leaf_load(name)
        if load is None:
            raise Unsupported(f"unknown symbolic value {name}")
        return self._getmem(load[0], load[1])

    # -- bit-vectors -------------------------------------------------------
    def bv(self, e) -> str:
        if isinstance(e, int):
            return str(e)
        w = e.size()
        op = e.op
        a = e.args
        if op == "BVV":
            return str(a[0])
        if op == "BVS":
            return self._bvs(e)
        if op == "__add__":
            # Picinae's normal form: x ⊖ k for a negative constant offset.
            consts = [x.args[0] for x in a if x.op == "BVV"]
            others = [x for x in a if x.op != "BVV"]
            c = sum(consts) % (1 << w)
            body = " + ".join(self.bv(x) for x in others) if others else "0"
            if c >= 1 << (w - 1) and others:
                inner = body if len(others) == 1 else f"(({body}) mod 2^{w})"
                return f"(msub {w} {inner} {(1 << w) - c})"
            terms = ([str(c)] if c else []) + [self.bv(x) for x in others]
            return f"(({' + '.join(terms)}) mod 2^{w})"
        if op == "__sub__":
            out = self.bv(a[0])
            for x in a[1:]:
                out = f"(msub {w} {out} {self.bv(x)})"
            return out
        if op == "__mul__":
            return f"(({' * '.join(self.bv(x) for x in a)}) mod 2^{w})"
        if op in ("__and__", "__or__", "__xor__"):
            f = {"__and__": "N.land", "__or__": "N.lor", "__xor__": "N.lxor"}[op]
            out = self.bv(a[0])
            for x in a[1:]:
                out = f"({f} {out} {self.bv(x)})"
            return out
        if op == "__neg__":
            return f"(msub {w} 0 {self.bv(a[0])})"
        if op == "__invert__":
            return f"(N.lnot {self.bv(a[0])} {w})"
        if op == "__lshift__":
            return f"((N.shiftl {self.bv(a[0])} {self.bv(a[1])}) mod 2^{w})"
        if op == "LShR":
            return f"(N.shiftr {self.bv(a[0])} {self.bv(a[1])})"
        if op == "__rshift__":
            return f"(ashiftr {w} {self.bv(a[0])} {self.bv(a[1])})"
        if op == "ZeroExt":
            return self.bv(a[1])
        if op == "SignExt":
            w0 = a[1].size()
            return f"(ofZ {w} (toZ {w0} {self.bv(a[1])}))"
        if op == "Extract":
            hi, lo, x = a
            # Byte-aligned slices of a load are narrower loads (little-endian).
            if x.op == "BVS" and lo % 8 == 0 and (hi + 1) % 8 == 0:
                load = self._leaf_load(x.args[0])
                if load is not None:
                    off = lo // 8
                    addr = load[0] if off == 0 else f"{off} + {load[0]}"
                    return self._getmem(addr, (hi - lo + 1) // 8)
            if lo == 0:
                return f"({self.bv(x)} mod 2^{hi + 1})"
            return f"(xbits {self.bv(x)} {lo} {hi + 1})"
        if op == "Concat":
            out, shift = "", 0
            for x in reversed(a):
                part = self.bv(x) if shift == 0 else f"(N.shiftl {self.bv(x)} {shift})"
                out = part if not out else f"(N.lor {part} {out})"
                shift += x.size()
            return out
        if op == "If":
            return f"(if {self.bool(a[0])} then {self.bv(a[1])} else {self.bv(a[2])})"
        raise Unsupported(f"bit-vector operator {op}")

    # -- booleans ----------------------------------------------------------
    def bool(self, e) -> str:
        op = e.op
        a = e.args
        if op == "BoolV":
            return "true" if a[0] else "false"
        if op == "Not":
            return f"(negb {self.bool(a[0])})"
        if op in ("And", "Or"):
            f = "andb" if op == "And" else "orb"
            out = self.bool(a[0])
            for x in a[1:]:
                out = f"({f} {out} {self.bool(x)})"
            return out
        if op == "__eq__":
            return f"({self.bv(a[0])} =? {self.bv(a[1])})"
        if op == "__ne__":
            return f"(negb ({self.bv(a[0])} =? {self.bv(a[1])}))"
        unsigned = {"ULT": "<?", "ULE": "<=?"}
        if op in unsigned:
            return f"({self.bv(a[0])} {unsigned[op]} {self.bv(a[1])})"
        if op in ("UGT", "UGE"):
            o = "<?" if op == "UGT" else "<=?"
            return f"({self.bv(a[1])} {o} {self.bv(a[0])})"
        signed = {"SLT": "Z.ltb", "SLE": "Z.leb", "SGT": "Z.gtb", "SGE": "Z.geb"}
        if op in signed:
            w = a[0].size()
            return f"({signed[op]} (toZ {w} {self.bv(a[0])}) (toZ {w} {self.bv(a[1])}))"
        if op == "If":
            return f"(if {self.bool(a[0])} then {self.bool(a[1])} else {self.bool(a[2])})"
        raise Unsupported(f"boolean operator {op}")


# --------------------------------------------------------------------------
# Postcondition from symbolic traces
# --------------------------------------------------------------------------

class Formula:
    def __init__(self, arch, func: Function, result: Dict):
        self.arch = arch
        self.func = func
        self.func = func
        if self._cfg_has_cycle():
            raise Unsupported("loop (TIG unrolls loops; it generates no loop invariant)")
        if not result["results"]:
            raise Unsupported("symbolic execution found no path to an exit")
        self.traces = [t["bb_history"] for t in result["results"]]
        self.state_args = [t["state_args"] for t in result["results"]]
        self.guards = {tuple(cn.bbl_history): cn for cn in result["info"]["branch_constraints"]}
        self.printer = Printer(arch, result["info"]["mem_reads"])
        self.has_loop = any(len(set(t)) != len(t) for t in self.traces) or self._cfg_has_cycle()

    def _cfg_has_cycle(self) -> bool:
        """A back edge in the function's CFG (depth-first search).  Paths alone
        can miss loops whose iterations angr did not explore."""
        # Ghidra's exit lists omit some edges (self-loops, jumps); its source
        # lists have them, so take the union of both directions.
        succ = {b.start_vaddr: {x for x in b.exit_vaddrs if x in self.func.block_dict}
                for b in self.func.blocks}
        for b in self.func.blocks:
            for src in b.source_vaddrs:
                if src in succ:
                    succ[src].add(b.start_vaddr)
        state = {}
        def dfs(n):
            state[n] = 1
            for m in succ.get(n, []):
                if state.get(m) == 1 or (m not in state and dfs(m)):
                    return True
            state[n] = 2
            return False
        return dfs(self.func.entry_point)

    def _time(self, instr: Instruction, prefix: Tuple[int, ...]) -> str:
        regs = self.arch.state_args(instr)
        args: Tuple[str, ...] = ()
        if regs:
            key = (prefix, instr.offset)
            for sa in self.state_args:
                if key in sa:
                    args = tuple(self.printer.bv(v) for v in sa[key])
                    break
            else:
                raise Unsupported(f"no recorded state for {instr}")
        return self.arch.instr_time(instr, args)

    def build(self) -> str:
        if not self.traces:
            raise Unsupported("symbolic execution found no path to an exit")
        if self.has_loop:
            raise Unsupported("loop (TIG unrolls loops; it generates no loop invariant)")
        return self._node((self.traces[0][0],))

    def _node(self, prefix: Tuple[int, ...]) -> str:
        block = self.func.get_block(prefix[-1])
        if block is None:
            raise Unsupported(f"path leaves the function at {prefix[-1]:#x}")
        bprefix = prefix  # bbl history including this block
        times = [self._time(i, bprefix) for i in block.instructions[:-1]]
        last = block.instructions[-1]
        succs = sorted({t[len(prefix)] for t in self.traces
                        if tuple(t[:len(prefix)]) == prefix and len(t) > len(prefix)})
        ends_here = any(tuple(t) == prefix for t in self.traces)

        if self.arch.is_branch(last):
            fall = last.offset + last.size
            tt, tf = self.arch.branch_times(last)
            cn = self.guards.get(prefix)
            taken = [s for s in succs if s != fall]
            nottaken = [s for s in succs if s == fall]
            if cn is None:
                raise Unsupported(f"no branch guard recorded at {prefix[-1]:#x}")
            guard = cn.bvv
            taken_target = cn.true_jmp_target if cn.true_jmp_target != fall else cn.false_jmp_target
            cond = guard if cn.true_jmp_target == taken_target else claripy.Not(guard)
            c = self.printer.bool(cond)
            t_side = f"{tt} + {self._node(prefix + (taken[0],))}" if taken else f"{tt} + time_inf"
            f_side = f"{tf} + {self._node(prefix + (nottaken[0],))}" if nottaken else f"{tf} + time_inf"
            body = f"(if {c} then {t_side} else {f_side})"
            return " + ".join(times + [body]) if times else body

        times.append(self._time(last, bprefix))
        if not succs:
            if not ends_here:
                times.append("time_inf")
            return "(" + " + ".join(times) + ")"
        if len(succs) > 1:
            raise Unsupported(f"multiple successors after {last}")
        return "(" + " + ".join(times) + f" + {self._node(prefix + (succs[0],))})"


# --------------------------------------------------------------------------
# Proof file
# --------------------------------------------------------------------------

def emit_riscv_proof(func: Function, formula: str, printer: Printer, exits: List[int],
                     header: str, binary: str) -> str:
    name = func.name
    params = (["mem"] if printer.uses_mem else []) + sorted(printer.regs)
    binders = ""
    if printer.uses_mem:
        binders += " (mem : memory)"
    regs = sorted(printer.regs)
    if regs:
        binders += " (" + " ".join(regs) + " : N)"
    args = " ".join(params)
    eqs = (["s V_MEM32 = mem"] if printer.uses_mem else []) + [f"s {RISCV.reg(r)} = {r}" for r in regs]
    entry_inv = " /\\ ".join(eqs + ["cycle_count_of_trace t' = 0"])
    hyps = "".join([f"\n         (MEM: s V_MEM32 = mem)"] if printer.uses_mem else []) + \
        "".join(f"\n         ({r.upper()}: s {RISCV.reg(r)} = {r})" for r in regs)
    names = (["MEM"] if printer.uses_mem else []) + [r.upper() for r in regs] + ["Cycles"]
    destr = f"destruct PRE as ({' & '.join(names)})." if len(names) > 1 else ""
    ex = " | ".join(f"{e:#x}" for e in exits)
    return f"""(* Generated by TIG (Cloq backend) *)
{header}

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_{name} <: ProgramInformation.
    Definition entry_addr : N := {func.entry_point:#x}.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | {ex} => true
        | _ => false
    end | _ => false end.

    Definition binary := {binary}.
End Program_{name}.

Module RISCVTiming := RISCVTiming cpu Program_{name}.
Module {name}Auto := RISCVTimingAutomation RISCVTiming.
Import Program_{name} {name}Auto.

Definition time_of_{name}{binders} (t : trace) :=
    cycle_count_of_trace t =
        {formula}.

Definition {name}_timing_invs{binders}
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| {func.entry_point:#x} => Some ({entry_inv})
| {ex} => Some (time_of_{name}{(' ' + args) if args else ''} t)
| _ => None end | _ => None end.

Theorem {name}_timing:
  forall s t s' x'{(' ' + args) if args else ''}
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s){hyps},
  satisfies_all
    lifted_prog
    ({name}_timing_invs{(' ' + args) if args else ''})
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. {'auto' if args else 'reflexivity'}.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    {destr}
    repeat step; hammer.
    (* decide any remaining conditionals and solve the arithmetic *)
    all: repeat (cbn [negb] in *; match goal with |- context[if ?c then _ else _] =>
           lazymatch c with true => fail | false => fail
           | negb ?c' => destruct c' | _ => destruct c end end);
         cbn [negb] in *; try lia.
Qed.

End TimingProof.
"""
