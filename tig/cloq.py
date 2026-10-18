"""Cloq backend: timing postconditions and proofs for the current Cloq API.

The legacy synthesizer (tig.proof_synthesis) targets an older Picinae timing
API with hard-coded NEORV32 cycle counts. This backend names instruction times
after Cloq's CPUTimingBehavior parameters (taddi, ttbne, tldr_imm, ...), prints
branch conditions as Rocq terms over the function's inputs, and emits a
complete proof file.
"""
import re
from typing import Dict, List, Optional, Tuple

import claripy

from tig.bininfo import Function, Instruction


class Unsupported(Exception):
    """Raised for programs or expressions the backend cannot express."""


# Architecture descriptions

def _riscv_imm(op: str) -> int:
    return int(op, 0)


class RISCV:
    name = "riscv"
    lang = "RISCV:LE:32:default"
    width = 32
    mem_var = "V_MEM32"
    branch_mnems = {"beq", "bne", "blt", "bge", "bltu", "bgeu"}
    # Instructions whose time depends on a register's value before the
    # instruction (RISCVTiming.v: R5_Sll rd _ _ => tsll (regvalue s rd)).
    state_dep = {"sll": "tsll", "srl": "tsrl", "sra": "tsra", "clz": "tclz"}
    simple = {m: "t" + m for m in
              "add addi slt slti sltu sltiu xor xori or ori and andi sub lui auipc "
              "jal jalr lb lh lw lbu lhu sb sh sw mul mulh mulhu div divu rem remu "
              "andn csrrw csrrs csrrc csrrwi csrrsi csrrci".split()}
    simple.update({"mulhsu": "tmulhsu", "fence": "tfence", "fence.i": "tfence"})
    gprs = ("ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 "
            "s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6").split()
    proof = dict(behavior="RVCPUTimingBehavior", timing="RISCVTiming", auto="RISCVTimingAutomation",
                 step="r5_step", typctx="rvtypctx", welltyped="lift_riscv_welltyped", isa="Picinae_riscv.ISA_RISCV",
                 program="binary", relative=False)

    def canon(self, op: str):
        """Register name, immediate value, or None."""
        if op == "zero":
            return 0
        return op if op in self.gprs else None

    def operand_regs(self, instr: Instruction) -> List[str]:
        return [r for op in instr.operands for r in re.findall(r"[a-z][a-z0-9]*", op) if r in self.gprs]

    def exit_compare(self, block) -> list:
        """Operands compared by the branch that ends `block`."""
        last = block.instructions[-1]
        return [self.canon(o) for o in last.operands[:2]] if self.is_branch(last) else []

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
        return "time_inf"  # not timed by Cloq

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
    gprs = "r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 sp lr".split()
    proof = dict(behavior="ARMv6MCPUTimingBehavior", timing="ARMv6MTiming", auto="ARMv6MTimingAutomation",
                 step="armv6m_step", typctx="armv6mtypctx", welltyped="welltyped_lift_armv6m", isa="Picinae_armv6m.ISA_ARMv6M",
                 program="binary", relative=False)

    def canon(self, op: str):
        op = op.lower().strip()
        if op in self.gprs:
            return op
        if op.startswith("#"):
            return int(op[1:], 0)
        return None

    def operand_regs(self, instr: Instruction) -> List[str]:
        return [r for op in _ghidra_ops(instr) for r in re.findall(r"\b(r\d+|sp|lr)\b", op.lower())
                if r in self.gprs]

    def exit_compare(self, block) -> list:
        """Operands of the cmp that sets the flags for the block's branch."""
        if not self.is_branch(block.instructions[-1]):
            return []
        for ins in reversed(block.instructions[:-1]):
            if self._norm(ins.mnem) in ("cmp", "cmn"):
                return [self.canon(o) for o in _ghidra_ops(ins)[:2]]
        return []

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
            # Ghidra prints PC-relative loads with the resolved address
            # (ldr r0,[0x08000028]), without a base register.
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
    """x86-64. Cloq's x86 proofs time each address with an operand-form name
    (mov_r64_m64, cmp_r64_i, jz_addr, ...) from amd64CPUTimingBehavior."""
    name = "amd64"
    lang = "x86:LE:64:default"
    width = 64
    mem_var = "V_MEM64"
    branch_mnems = {"jo", "jno", "jc", "jnc", "jb", "jnb", "jae", "jnae", "jz", "jnz", "je", "jne",
                    "jbe", "jnbe", "ja", "jna", "js", "jns", "jp", "jnp", "jpe", "jpo", "jl", "jnl",
                    "jge", "jnge", "jle", "jnle", "jg", "jng"}
    _ptr = {"byte": 8, "word": 16, "dword": 32, "qword": 64, "xmmword": 128}

    gprs = "rax rbx rcx rdx rsi rdi rbp rsp r8 r9 r10 r11 r12 r13 r14 r15".split()
    proof = dict(behavior="amd64CPUTimingBehavior", timing="AMD64Timing", auto="AMD64TimingAutomation",
                 step="x64_step", typctx="x64typctx", welltyped="welltyped", isa="Picinae_amd64.ISA_amd64",
                 program="lifted", relative=True)

    def __init__(self):
        w, parent = {}, {}
        for r in "rax rbx rcx rdx rsi rdi rbp rsp rip".split():
            w[r], w["e" + r[1:]], w[r[1:]] = 64, 32, 16
            parent[r] = parent["e" + r[1:]] = parent[r[1:]] = r
        for r, p in zip("al bl cl dl sil dil bpl spl ah bh ch dh".split(),
                        "rax rbx rcx rdx rsi rdi rbp rsp rax rbx rcx rdx".split()):
            w[r], parent[r] = 8, p
        for i in range(8, 16):
            w[f"r{i}"], w[f"r{i}d"], w[f"r{i}w"], w[f"r{i}b"] = 64, 32, 16, 8
            for suf in ("", "d", "w", "b"):
                parent[f"r{i}{suf}"] = f"r{i}"
        self._w, self._parent = w, parent

    def canon(self, op: str):
        """64-bit register name, immediate value, or None."""
        op = op.lower().strip()
        if op in self._parent:
            return self._parent[op]
        try:
            return int(op, 0)
        except ValueError:
            return None

    def operand_regs(self, instr: Instruction) -> List[str]:
        return [self._parent[r] for op in _ghidra_ops(instr)
                for r in re.findall(r"[a-z][a-z0-9]*", op.lower()) if r in self._parent]

    def exit_compare(self, block) -> list:
        if not self.is_branch(block.instructions[-1]):
            return []
        for ins in reversed(block.instructions[:-1]):
            m, ops = ins.mnem.lower(), _ghidra_ops(ins)
            if m == "cmp":
                return [self.canon(o) for o in ops[:2]]
            if m == "test" and len(ops) == 2 and ops[0].lower() == ops[1].lower():
                return [self.canon(ops[0]), 0]
        return []

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

    # Names declared by amd64CPUTimingBehavior, if the model file is given.
    # A missing name falls back to the reversed operand order, which the model
    # uses for both directions (cmp m64,r64 -> cmp_r64_m64).
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
        return t, t  # same time taken or not

    def is_return(self, instr: Instruction) -> bool:
        return instr.mnem.lower() == "ret"


ARCHS = {"riscv": RISCV(), "armv6m": ARMv6M(), "amd64": AMD64()}


# Expression printing

def _reg_name(sym: str) -> str:
    """Register of an initial-register symbol reg_<name>_<id>_<bits>, which
    may have more _<id>_<bits> suffixes (x86 sub-registers)."""
    return re.sub(r"(_\d+_\d+)+$", "", sym[len("reg_"):]).lower()


class Printer:
    """Prints claripy ASTs as Rocq terms over the function's inputs."""

    def __init__(self, arch, mem_reads: Dict[str, Tuple[object, int]]):
        self.arch = arch
        self.mem_reads = mem_reads
        self.regs = set()       # initial registers referenced
        self.uses_mem = False   # initial memory referenced

    def _getmem(self, addr: str, nbytes: int) -> str:
        self.uses_mem = True
        sym = {1: "Ⓑ", 2: "Ⓦ", 4: "Ⓓ", 8: "Ⓠ"}.get(nbytes)
        if sym is None:
            raise Unsupported(f"{nbytes}-byte load")
        return f"mem {sym}[{addr}]"

    def addr(self, e) -> str:
        """Print an address the way Picinae's lifter leaves it. getmem reduces
        addresses mod 2^w, so offsets stay unreduced (16 + a0) and negative
        offsets use modular subtraction (gp ⊖ 1900)."""
        if isinstance(e, int):
            return str(e)  # concrete address
        w = e.size()
        if e.op == "__add__":
            # flatten nested sums into Picinae's form (92 + a0 + a1)
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
        """(address, length) if `name` is a load from the initial memory."""
        # tig.memory_mixins renames an extended load v to v_<id>_<bits>,
        # with the same (zero-extended) value.
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
            reg = _reg_name(name)
            parent = getattr(self.arch, "_parent", {}).get(reg, reg)
            self.regs.add(parent)
            if parent == reg:
                return reg
            # x86 sub-register
            if reg in ("ah", "bh", "ch", "dh"):
                return f"(xbits {parent} 8 16)"
            return f"({parent} mod 2^{self.arch._w[reg]})"
        if name.startswith("CLZ_{"):
            inner = re.match(r"CLZ_\{(.+)\}", name).group(1)
            return f"(clz ({self._name(inner)}) {self.arch.width})"
        load = self._leaf_load(name)
        if load is not None:
            return self._getmem(load[0], load[1])
        raise Unsupported(f"unknown symbolic value {name}")

    def _name(self, name: str) -> str:
        if name.startswith("reg_"):
            reg = _reg_name(name)
            self.regs.add(reg)
            return reg
        load = self._leaf_load(name)
        if load is None:
            raise Unsupported(f"unknown symbolic value {name}")
        return self._getmem(load[0], load[1])

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
            # Picinae writes negative offsets as x ⊖ k
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
            # byte-aligned slices of a load are narrower loads (little-endian)
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


# Postcondition from symbolic traces

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
        """Whether the function's CFG has a back edge. Explored paths alone can
        miss loops."""
        # Ghidra's exit lists miss some edges (self-loops, jumps) that its
        # source lists have, so use both.
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
        bprefix = prefix
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


# Proof file

def loc(arch, func: Function):
    """Address as numbered in the Rocq program. x86 lifted programs start at
    0 at the function's entry."""
    base = func.entry_point if arch.proof["relative"] else 0
    return lambda a: a - base


def proof_preamble(arch, func: Function, exits: List[int], header: str, binary: str) -> str:
    """Proof file header, through the timing modules."""
    P, at, name = arch.proof, loc(arch, func), func.name
    ex = " | ".join(f"{at(e):#x}" for e in exits)
    if P["program"] == "binary":
        prog = f"    Definition binary := {binary}."
    else:
        rows = []
        for b in sorted(func.blocks, key=lambda b: b.start_vaddr):
            for i in b.instructions:
                t = arch.branch_times(i)[0] if arch.is_branch(i) else arch.instr_time(i, ())
                rows.append(f"        (* {i.instr_str} *)\n        | {at(i.offset):#x} => {t}")
        prog = ("    Definition time_of_addr (s : store) (a : addr) : N :=\n        match a with\n"
                + "\n".join(rows) + "\n        | _ => time_inf\n        end.\n\n"
                + f"    Definition lifted_prog := {binary}.")
    return f"""{header}

Module TimingProof (cpu : {P["behavior"]}).
Import cpu.

Module Program_{name} <: ProgramInformation.
    Definition entry_addr : N := {at(func.entry_point):#x}.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | {ex} => true
        | _ => false
    end | _ => false end.

{prog}
End Program_{name}.

Module {P["timing"]} := {P["timing"]} cpu Program_{name}.
Module {name}Auto := {P["auto"]} {P["timing"]}.
Import Program_{name} {name}Auto."""


def proof_setup(arch) -> str:
    """Inductive-step setup."""
    P = arch.proof
    return f"""    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply {P["welltyped"]}].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv {arch.width} PRE."""


def emit_proof(arch, func: Function, formula: str, printer: Printer, exits: List[int],
               header: str, binary: str, ignore: str = "") -> str:
    name, P, at = func.name, arch.proof, loc(arch, func)
    params = (["mem"] if printer.uses_mem else []) + sorted(printer.regs)
    binders = ""
    if printer.uses_mem:
        binders += " (mem : memory)"
    regs = sorted(printer.regs)
    if regs:
        binders += " (" + " ".join(regs) + " : N)"
    args = " ".join(params)
    eqs = ([f"s {arch.mem_var} = mem"] if printer.uses_mem else []) + [f"s {arch.reg(r)} = {r}" for r in regs]
    entry_inv = " /\\ ".join(eqs + ["cycle_count_of_trace t' = 0"])
    hyps = "".join([f"\n         (MEM: s {arch.mem_var} = mem)"] if printer.uses_mem else []) + \
        "".join(f"\n         ({r.upper()}: s {arch.reg(r)} = {r})" for r in regs)
    names = (["MEM"] if printer.uses_mem else []) + [r.upper() for r in regs] + ["Cycles"]
    destr = f"destruct PRE as ({' & '.join(names)})." if len(names) > 1 else ""
    ex = " | ".join(f"{at(e):#x}" for e in exits)
    return f"""(* Generated by TIG (Cloq backend) *)
{proof_preamble(arch, func, exits, header, binary)}

Definition time_of_{name}{binders} (t : trace) :=
    cycle_count_of_trace t =
        {formula}.

Definition {name}_timing_invs{binders}
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| {at(func.entry_point):#x} => Some ({entry_inv})
| {ex} => Some (time_of_{name}{(' ' + args) if args else ''} t)
| _ => None end | _ => None end.

Theorem {name}_timing:
  forall s t s' x'{(' ' + args) if args else ''}
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models {P["typctx"]} s){hyps},
  satisfies_all
    lifted_prog
    ({name}_timing_invs{(' ' + args) if args else ''})
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep {P["step"]}.
{ignore}
    simpl. rewrite ENTRY. unfold entry_addr. step. {'auto' if args else 'reflexivity'}.

    intros.
{proof_setup(arch)}

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


def emit_riscv_proof(func, formula, printer, exits, header, binary):
    return emit_proof(RISCV(), func, formula, printer, exits, header, binary)
