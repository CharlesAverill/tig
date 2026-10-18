"""Heuristic loop invariants for the Cloq backend.

TIG explores each loop a few times (LoopSeer) and records the register file at
every visit of the loop header -- the CFG join point where the entry edge and
the back edge meet.  From those snapshots we guess

  * induction registers:  value at visit k+1 minus value at visit k is the same
    constant c on every visit (so the register equals  init ⊕ c*i);
  * invariant registers:  the value does not change between visits;
  * the iteration count:  an expression E over the function's inputs, built
    from the loop-exit comparison (bound - init) / c, and kept only if every
    explored path that leaves through that exit satisfies  E = iterations
    under its path constraints.

The header invariant is then

    exists i, i <= E /\\ s X = init ⊕ c*i /\\ s Y = bound /\\
      cycle_count_of_trace t' = PRE + i * BODY

where PRE is the time from the entry to the first header visit and BODY the
time of one trip around the loop.  None of this is checked here; Rocq checks
the generated proof.  When explored trips differ in time (a branch inside the
body), BODY is the N.max of the trips and the invariant becomes an upper bound.
"""
import re
from typing import Dict, List, Optional, Tuple

import claripy

from tig.bininfo import Function
from tig.cloq import Printer, RISCV, Unsupported

W = 32
M = 1 << W

RISCV_GPRS = ("ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 "
              "s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6").split()


# --------------------------------------------------------------------------
# CFG
# --------------------------------------------------------------------------

def successors(func: Function) -> Dict[int, set]:
    # Ghidra's exit lists omit some edges; its source lists have them.
    succ = {b.start_vaddr: {x for x in b.exit_vaddrs if x in func.block_dict}
            for b in func.blocks}
    for b in func.blocks:
        for src in b.source_vaddrs:
            if src in succ:
                succ[src].add(b.start_vaddr)
    return succ


def find_loops(func: Function) -> Dict[int, set]:
    """Natural loops: header -> blocks of the loop (back edges by DFS)."""
    succ = successors(func)
    preds = {n: set() for n in succ}
    for n, ms in succ.items():
        for m in ms:
            preds[m].add(n)
    state, back = {}, []

    def dfs(n):
        state[n] = 1
        for m in sorted(succ.get(n, ())):
            if state.get(m) == 1:
                back.append((n, m))
            elif m not in state:
                dfs(m)
        state[n] = 2
    dfs(func.entry_point)
    loops: Dict[int, set] = {}
    for latch, h in back:
        body, work = {h, latch}, [latch]
        while work:
            n = work.pop()
            for p in preds.get(n, ()):
                if p not in body:
                    body.add(p)
                    work.append(p)
        loops.setdefault(h, set()).update(body)
    return loops


# --------------------------------------------------------------------------
# Symbolic helpers
# --------------------------------------------------------------------------

def _equal(a, b) -> bool:
    if a is b:
        return True
    return not claripy.Solver().satisfiable(extra_constraints=[a != b])


def _const(e) -> Optional[int]:
    s = claripy.Solver()
    vals = s.eval(e, 2)
    return vals[0] if len(vals) == 1 else None


def _implied(constraints, goal) -> bool:
    s = claripy.Solver()
    s.add(constraints)
    return s.satisfiable() and not s.satisfiable(extra_constraints=[claripy.Not(goal)])


def _strip_shift(d, k: int):
    """d == e << k  ->  (e, assumption e < 2^(W-k)); else None."""
    d = claripy.simplify(d)
    if d.op == "__lshift__" and d.args[1].op == "BVV" and d.args[1].args[0] == k:
        return d.args[0]
    if (d.op == "Concat" and len(d.args) == 2 and d.args[1].op == "BVV"
            and d.args[1].args[0] == 0 and d.args[1].size() == k):
        x = d.args[0]
        if x.op == "Extract" and x.args[1] == 0 and x.args[2].size() == W:
            return x.args[2]
        return claripy.ZeroExt(k, x)
    if d.op == "__mul__" and len(d.args) == 2:
        for x, y in (d.args, d.args[::-1]):
            if x.op == "BVV" and x.args[0] == 1 << k:
                return y
    return None


# --------------------------------------------------------------------------
# Loop formula
# --------------------------------------------------------------------------

class Induction:
    def __init__(self, reg, init, step):
        self.reg, self.init, self.step = reg, init, step


class LoopFormula:
    """Postcondition and header invariant for a function with one loop."""

    def __init__(self, arch, func: Function, result: Dict, header: int, body: set,
                 extra_exits: List[int]):
        if arch is not RISCV and type(arch).__name__ != "RISCV":
            raise Unsupported("loop invariants are only implemented for RISC-V")
        self.arch, self.func, self.h, self.body = arch, func, header, body
        self.extra_exits = set(extra_exits)
        rs = result["results"]
        if not rs:
            raise Unsupported("symbolic execution found no path to an exit")
        self.paths = [r["bb_history"] for r in rs]
        self.ends = [r["end_address"] for r in rs]
        self.cons = [r["constraints"] for r in rs]
        self.state_args = [r["state_args"] for r in rs]
        self.snaps = [r["snapshots"] for r in rs]
        self.printer = Printer(arch, result["info"]["mem_reads"])
        self.assumptions: List[str] = []
        self.rel = "="  # "<=" once any time is over-approximated

    # -- timing of a path segment ---------------------------------------
    def _instr_time(self, pi: int, prefix: Tuple[int, ...], instr) -> str:
        regs = self.arch.state_args(instr)
        args: Tuple[str, ...] = ()
        if regs:
            vals = self.state_args[pi].get((prefix, instr.offset))
            if vals is None:
                raise Unsupported(f"no recorded state for {instr}")
            args = tuple(self.printer.bv(v) for v in vals)
            # a state-dependent time inside the loop changes per iteration;
            # keeping iteration 0's value would be wrong, so give up.
            if prefix[-1] in self.body:
                raise Unsupported(f"state-dependent instruction time in the loop: {instr}")
        return self.arch.instr_time(instr, args)

    def _seg_time(self, pi: int, lo: int, hi: int) -> List[str]:
        """Times of the blocks path[lo:hi] (the successor of the last block is
        path[hi], or the path's end address)."""
        path = self.paths[pi]
        out = []
        for k in range(lo, hi):
            b = self.func.get_block(path[k])
            if b is None:
                raise Unsupported(f"path leaves the function at {path[k]:#x}")
            prefix = tuple(path[:k + 1])
            for ins in b.instructions[:-1]:
                out.append(self._instr_time(pi, prefix, ins))
            last = b.instructions[-1]
            if self.arch.is_branch(last):
                nxt = path[k + 1] if k + 1 < len(path) else self.ends[pi]
                tt, tf = self.arch.branch_times(last)
                out.append(tf if nxt == last.offset + last.size else tt)
            else:
                out.append(self._instr_time(pi, prefix, last))
        return out

    @staticmethod
    def _sum(ts: List[str]) -> str:
        return " + ".join(ts) if ts else "0"

    def _join(self, alts: List[List[str]]) -> str:
        uniq = []
        for a in alts:
            if sorted(a) not in [sorted(u) for u in uniq]:
                uniq.append(a)
        if len(uniq) == 1:
            return self._sum(uniq[0])
        self.rel = "<="
        out = f"({self._sum(uniq[0])})"
        for u in uniq[1:]:
            out = f"(N.max {out} ({self._sum(u)}))"
        return out

    def _exit_addr(self, pi: int) -> int:
        path = self.paths[pi]
        last = self.func.get_block(path[-1]).instructions[-1]
        if self.arch.is_return(last):
            return last.offset
        return self.ends[pi]

    # -- induction variables ---------------------------------------------
    def _inductions(self):
        """(inductions, invariants) from the header snapshots."""
        best = None
        for pi, sn in enumerate(self.snaps):
            visits = sorted((k for k in sn if k[-1] == self.h), key=len)
            if best is None or len(visits) > len(best):
                best = [sn[k] for k in visits]
        if not best or len(best) < 2:
            raise Unsupported("explored no complete loop iteration")
        ind, inv = {}, {}
        for r in RISCV_GPRS:
            vs = [s[r] for s in best]
            if all(_equal(vs[0], v) for v in vs[1:]):
                inv[r] = vs[0]
                continue
            d = _const(claripy.simplify(vs[1] - vs[0]))
            if d is None or d == 0:
                continue
            if all(_const(claripy.simplify(vs[k + 1] - vs[k])) == d for k in range(1, len(vs) - 1)):
                ind[r] = Induction(r, vs[0], d)
        return ind, inv

    def _exit_branches(self):
        """Branches in the loop through which an explored path leaves it:
        [(instr, compared registers)]."""
        exiting = set()
        for path in self.paths:
            for k, a in enumerate(path):
                if a in self.body and (k + 1 == len(path) or path[k + 1] not in self.body):
                    exiting.add(a)
        out = []
        for a in sorted(exiting):
            last = self.func.get_block(a).instructions[-1]
            if self.arch.is_branch(last):
                out.append((last, list(last.operands[:2])))
        return out

    def _count_candidates(self, ind, inv):
        """Iteration-count expressions (claripy ASTs over the inputs)."""
        cands = []
        for _, ops in self._exit_branches():
            for x, y in (ops, ops[::-1]):
                if x not in ind:
                    continue
                if y == "zero":
                    bound = claripy.BVV(0, W)
                elif y in inv:
                    bound = inv[y]
                else:
                    continue
                iv = ind[x]
                c = iv.step if iv.step < M // 2 else iv.step - M
                d = claripy.simplify(bound - iv.init) if c > 0 else claripy.simplify(iv.init - bound)
                c = abs(c)
                if c == 1:
                    e, assume = d, None
                elif c & (c - 1) == 0:
                    k = c.bit_length() - 1
                    e = _strip_shift(d, k)
                    assume = (e, k) if e is not None else None
                    if e is None:
                        e = claripy.LShR(d, k)
                else:
                    e, assume = d // c, None
                for off in (0, -1, 1):
                    cands.append((claripy.simplify(e + off) if off else e, assume, (x, y)))
        return cands

    # -- build -------------------------------------------------------------
    def build(self):
        h = self.h
        ind, inv = self._inductions()
        groups: Dict[Tuple, Dict] = {}   # exit kind -> paths
        pre_alts, body_alts, noloop = [], [], {}
        for pi, path in enumerate(self.paths):
            visits = [k for k, a in enumerate(path) if a == h]
            ex = self._exit_addr(pi)
            if not visits:
                noloop.setdefault(ex, []).append(self._seg_time(pi, 0, len(path)))
                continue
            pre_alts.append(self._seg_time(pi, 0, visits[0]))
            for k in range(len(visits) - 1):
                body_alts.append(self._seg_time(pi, visits[k], visits[k + 1]))
            tail = self._seg_time(pi, visits[-1], len(path))
            key = (ex, " + ".join(tail))
            g = groups.setdefault(key, {"tail": tail, "paths": []})
            g["paths"].append((pi, len(visits) - 1))
        if not pre_alts:
            raise Unsupported("no explored path reaches the loop header")
        if not body_alts:
            raise Unsupported("explored no complete loop iteration")
        pre = self._join(pre_alts)
        body = self._join(body_alts)

        # iteration count: a candidate implied on every path of some exit kind
        cands = self._count_candidates(ind, inv)
        count, count_regs = None, None
        for g in groups.values():
            for e, assume, regs in cands:
                extra = []
                if assume is not None:
                    a, k = assume
                    extra = [claripy.ULT(a, claripy.BVV(1 << (W - k), W))]
                if all(_implied(list(self.cons[pi]) + extra, e == claripy.BVV(n, W))
                       for pi, n in g["paths"]):
                    g["count"] = e
                    if count is None:
                        count, count_regs = e, regs
                        if assume is not None:
                            a, k = assume
                            self.assumptions.append(f"{2 ** k} * {self.printer.bv(a)} < 2^{W}")
                    break

        # header invariant
        regs_used = set()
        for _, ops in self._exit_branches():
            regs_used.update(o for o in ops if o != "zero")
        # invariant registers the body reads (e.g. a step or bound kept in a register)
        for a in self.body:
            for ins in self.func.get_block(a).instructions:
                for op in ins.operands:
                    regs_used.update(r for r in re.findall(r"[a-z][a-z0-9]*", op) if r in inv)
        conj = []
        n_str = self.printer.bv(count) if count is not None else None
        if n_str is not None:
            conj.append(f"i <= {n_str}")
        for r in sorted(regs_used):
            if r in ind:
                iv = ind[r]
                conj.append(f"s {self.arch.reg(r)} = {self.printer.bv(iv.init)} ⊕ {iv.step} * i")
            elif r in inv:
                conj.append(f"s {self.arch.reg(r)} = {self.printer.bv(inv[r])}")
        self.header_conj = conj
        self.header_time = f"{pre} + i * ({body})"

        # postcondition, per exit address
        posts: Dict[int, List[str]] = {}
        # At a return the trace head is the return instruction, whose time the
        # tail includes; an exit outside the function is not executed (t').
        ct = lambda ex: "cycle_count_of_trace t'" if ex in self.extra_exits else "cycle_count_of_trace t"
        for (ex, _), g in groups.items():
            tail = self._sum(g["tail"])
            if "count" in g:
                t = f"{pre} + {self.printer.bv(g['count'])} * ({body}) + {tail}"
                posts.setdefault(ex, []).append(f"{ct(ex)} {self.rel} {t}")
            else:
                bound = f"j <= {n_str} /\\ " if n_str is not None else ""
                posts.setdefault(ex, []).append(
                    f"(exists j, {bound}{ct(ex)} {self.rel} {pre} + j * ({body}) + {tail})")
        for ex, alts in noloop.items():
            posts.setdefault(ex, []).append(f"{ct(ex)} {self.rel} {self._join(alts)}")
        # (relation may have become "<=" while joining; restate uniformly)
        self.posts = {ex: [re.sub(r"(cycle_count_of_trace t'?) = ", r"\1 " + self.rel + " ", p)
                           for p in ps] for ex, ps in posts.items()}
        self.count = n_str
        return self


# --------------------------------------------------------------------------
# Proof file
# --------------------------------------------------------------------------

LTAC = r"""
(* TIG: generic closing tactics for loop proofs *)
Local Ltac tig_bc :=
  unfold slt, sle in *;
  repeat match goal with
  | H: Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H
  | H: Z.ltb _ _ = false |- _ => apply Z.ltb_ge in H
  | H: Z.leb _ _ = true |- _ => apply Z.leb_le in H
  | H: Z.leb _ _ = false |- _ => apply Z.leb_gt in H
  | H: Z.geb _ _ = true |- _ => apply Z.geb_le in H
  | H: Z.geb _ _ = false |- _ => rewrite Z.geb_leb in H; apply Z.leb_gt in H
  | H: Z.gtb _ _ = true |- _ => apply Z.gtb_lt in H
  | H: Z.gtb _ _ = false |- _ => rewrite Z.gtb_ltb in H; apply Z.ltb_ge in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ <=? _) = true |- _ => apply N.leb_le in H
  | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
  | H: negb _ = true |- _ => apply Bool.negb_true_iff in H
  | H: negb _ = false |- _ => apply Bool.negb_false_iff in H
  end.
Local Ltac tig_split_if c :=
  lazymatch c with true => fail | false => fail
  | negb ?c' => destruct c' eqn:? | _ => destruct c eqn:? end.
Local Ltac tig_ifs :=
  repeat (cbn [negb] in *; match goal with
    | |- context[if ?c then _ else _] => tig_split_if c
    | H: context[if ?c then _ else _] |- _ => tig_split_if c
    end); cbn [negb] in *.
(* modular arithmetic: eliminate mod/div into linear constraints *)
Local Ltac tig_pow :=
  repeat match goal with
  | |- context[2 ^ ?n] => let v := eval vm_compute in (2 ^ n) in change (2 ^ n) with v
  | H: context[2 ^ ?n] |- _ => let v := eval vm_compute in (2 ^ n) in change (2 ^ n) with v in H
  end.
Local Ltac tig_arith :=
  tig_bc; unfold msub in *;
  rewrite ?N.shiftl_mul_pow2, ?N.shiftr_div_pow2 in *; tig_pow;
  zify; Z.div_mod_to_equations; Z.quot_rem_to_equations; lia.
Local Ltac tig_leaf w :=
  first [ assumption | reflexivity
        | (try lazymatch goal with H: w <= ?n |- _ =>
             replace w with n in * by tig_arith end);
          hammer; tig_ifs; solve [ lia | tig_arith ] ].
(* choose disjuncts and iteration witnesses (w, the current iteration, or w+1) *)
Local Ltac tig_try w :=
  lazymatch goal with
  | |- _ \/ _ => first [ left; tig_try w | right; tig_try w ]
  | |- exists _, _ => first [ exists w; tig_try w | exists (w + 1); tig_try w ]
  | |- _ /\ _ => split; [ tig_try w | tig_try w ]
  | |- _ => solve [ tig_leaf w ]
  end.
"""


def _destruct(names):
    return f"destruct PRE as ({' & '.join(names)})." if len(names) > 1 else f"rename PRE into {names[0]}."


def emit_riscv_loop_proof(func, lf: LoopFormula, header: str, binary: str) -> str:
    name = func.name
    pr = lf.printer
    regs = sorted(pr.regs)
    params = (["mem"] if pr.uses_mem else []) + regs
    binders = (" (mem : memory)" if pr.uses_mem else "") + (f" ({' '.join(regs)} : N)" if regs else "")
    args = (" " + " ".join(params)) if params else ""
    bounds = [f"{r} < 2^32" for r in regs]
    assumes = lf.assumptions
    eqs = (["s V_MEM32 = mem"] if pr.uses_mem else []) + [f"s {RISCV.reg(r)} = {r}" for r in regs]
    entry = func.entry_point
    hconj = lf.header_conj + bounds + assumes + [f"cycle_count_of_trace t' {lf.rel} {lf.header_time}"]
    header_inv = "exists i, " + " /\\\n        ".join(hconj)
    arms = []
    if entry != lf.h:
        arms.append(f"| {entry:#x} => Some ({' /\\ '.join(eqs + bounds + assumes + ['cycle_count_of_trace t' + chr(39) + ' = 0'])})")
    arms.append(f"| {lf.h:#x} => Some ({header_inv})")
    for ex, ps in sorted(lf.posts.items()):
        arms.append(f"| {ex:#x} => Some ({' \\/'.join(chr(10) + '        ' + p for p in ps)})")
    exits = sorted(lf.posts)
    ex = " | ".join(f"{e:#x}" for e in exits)

    hyps = ("\n         (MEM: s V_MEM32 = mem)" if pr.uses_mem else "") + \
        "".join(f"\n         ({r.upper()}: s {RISCV.reg(r)} = {r})" for r in regs) + \
        "".join(f"\n         (ASSUME{k}: {a})" for k, a in enumerate(assumes))
    poses = "".join(f"\n    pose proof (models_var {RISCV.reg(r)} MDL) as B_{r.upper()}; simpl in B_{r.upper()};"
                    f" rewrite {r.upper()} in B_{r.upper()}." for r in regs)
    entry_names = (["MEM"] if pr.uses_mem else []) + [r.upper() for r in regs] + \
        [f"B_{r.upper()}" for r in regs] + [f"ASSUME{k}" for k in range(len(assumes))] + ["Cycles"]
    head_names = ["i"] + [f"L{k}" for k in range(len(lf.header_conj))] + \
        [f"B_{r.upper()}" for r in regs] + [f"ASSUME{k}" for k in range(len(assumes))] + ["Cycles"]
    cases = []
    if entry != lf.h:
        cases.append(f"""    (* {entry:#x}: entry -> loop header *)
    {{ {_destruct(entry_names)}
      repeat step. all: tig_try 0. }}""")
    cases.append(f"""    (* {lf.h:#x}: loop header -> loop header / exit *)
    {{ {_destruct(head_names)}
      repeat step. all: tig_try i. }}""")
    cases = "\n\n".join(cases)
    return f"""(* Generated by TIG (Cloq backend, heuristic loop invariants) *)
{header}
From Stdlib Require Import ZArith Lia.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_{name} <: ProgramInformation.
    Definition entry_addr : N := {entry:#x}.

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
{LTAC}
Definition {name}_timing_invs{binders}
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
{chr(10).join(arms)}
| _ => None end | _ => None end.

Theorem {name}_timing:
  forall s t s' x'{args}
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s){hyps},
  satisfies_all
    lifted_prog
    ({name}_timing_invs{args})
    exits
  ((x',s')::t).
Proof using.
    intros.{poses}
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. tig_try 0.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

{cases}
Qed.

End TimingProof.
"""
