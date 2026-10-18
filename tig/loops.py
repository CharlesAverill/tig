"""Heuristic loop invariants for the Cloq backend.

TIG explores the loop a few times and records the registers at each visit of
the loop header. A register that changes by the same constant c on every visit
is an induction variable (init ⊕ c*i); one that does not change is invariant.
The iteration count is guessed from the loop-exit comparison as
(bound - init) / c, and kept only if every explored path leaving through that
exit agrees with it. The header invariant is

    i < E /\\ s X = init ⊕ c*i /\\ s Y = bound /\\
    cycle_count_of_trace t' = PRE + i * BODY

where PRE is the time to reach the header and BODY the time of one iteration.
If iterations differ in time, BODY is their N.max and the invariant becomes an
upper bound. Nothing here is checked; Rocq checks the generated proof.
"""
import re
from typing import Dict, List, Optional, Tuple

import claripy

from tig.bininfo import Function
from tig.cloq import Printer, RISCV, Unsupported, loc, proof_preamble, proof_setup

RISCV_GPRS = RISCV.gprs


# CFG

def successors(func: Function) -> Dict[int, set]:
    # Ghidra's exit lists miss some edges that its source lists have
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
        # for a self-loop, walking back from the header would leave the loop
        body, work = {h, latch}, ([latch] if latch != h else [])
        while work:
            n = work.pop()
            for p in preds.get(n, ()):
                if p not in body:
                    body.add(p)
                    work.append(p)
        loops.setdefault(h, set()).update(body)
    return loops


# Symbolic helpers

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
    W = d.size()
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


def _minus_one(e):
    """X if e is X - 1 (mod 2^w), else None."""
    e = claripy.simplify(e)
    if e.op == "__add__" and len(e.args) == 2:
        for x, y in (e.args, e.args[::-1]):
            if y.op == "BVV" and y.args[0] == (1 << e.size()) - 1:
                return x
    if e.op == "__sub__" and len(e.args) == 2 and e.args[1].op == "BVV" and e.args[1].args[0] == 1:
        return e.args[0]
    return None


# Loop formula

class Induction:
    def __init__(self, reg, init, step):
        self.reg, self.init, self.step = reg, init, step


class LoopFormula:
    """Postcondition and header invariant for a function with one loop."""

    def __init__(self, arch, func: Function, result: Dict, header: int, body: set,
                 extra_exits: List[int]):
        self.arch, self.func, self.h, self.body = arch, func, header, body
        self.W = arch.width
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
        self.count_branches = set()  # exit branches the iteration count comes from
        self.rel = "="  # "<=" if a time is over-approximated

    def _instr_time(self, pi: int, prefix: Tuple[int, ...], instr) -> str:
        regs = self.arch.state_args(instr)
        args: Tuple[str, ...] = ()
        if regs:
            vals = self.state_args[pi].get((prefix, instr.offset))
            if vals is None:
                raise Unsupported(f"no recorded state for {instr}")
            args = tuple(self.printer.bv(v) for v in vals)
            # a state-dependent time in the loop changes per iteration
            if prefix[-1] in self.body:
                raise Unsupported(f"state-dependent instruction time in the loop: {instr}")
        return self.arch.instr_time(instr, args)

    def _seg_time(self, pi: int, lo: int, hi: int) -> List[str]:
        """Times of the blocks path[lo:hi]."""
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
        for r in self.arch.gprs:
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
        """[(branch, compared operands)] for the branches through which an
        explored path leaves the loop."""
        exiting = set()
        for path in self.paths:
            for k, a in enumerate(path):
                if a in self.body and (k + 1 == len(path) or path[k + 1] not in self.body):
                    exiting.add(a)
        out = []
        for a in sorted(exiting):
            b = self.func.get_block(a)
            ops = self.arch.exit_compare(b)
            if ops:
                out.append((b.instructions[-1], ops))
        return out

    def _count_candidates(self, ind, inv):
        """Candidate iteration counts, as claripy ASTs over the inputs."""
        W, M = self.W, 1 << self.W
        cands = []
        for _, ops in self._exit_branches():
            for x, y in (ops, ops[::-1]):
                if x not in ind:
                    continue
                if isinstance(y, int):
                    bound = claripy.BVV(y, W)
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

    def build(self):
        h = self.h
        ind, inv = self._inductions()
        groups: Dict[Tuple, Dict] = {}   # (exit, tail time) -> paths
        pre_alts, body_alts, noloop = [], [], {}
        for pi, path in enumerate(self.paths):
            visits = [k for k, a in enumerate(path) if a == h]
            ex = self._exit_addr(pi)
            if not visits:
                noloop.setdefault(ex, []).append((pi, self._seg_time(pi, 0, len(path))))
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

        # iteration count: a candidate implied on every path of an exit group
        W = self.W
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
                    self.count_branches = {b.offset for b, _ in self._exit_branches()}
                    if count is None:
                        count, count_regs = e, regs
                        if assume is not None:
                            a, k = assume
                            self.assumptions.append(f"{2 ** k} * {self.printer.bv(a)} < 2^{W}")
                    break

        # header invariant
        regs_used = set()
        for _, ops in self._exit_branches():
            regs_used.update(o for o in ops if isinstance(o, str))
        # and invariant registers the body reads (a step or bound in a register)
        for a in self.body:
            for ins in self.func.get_block(a).instructions:
                regs_used.update(r for r in self.arch.operand_regs(ins) if r in inv)
        conj = []
        n_str = self.printer.bv(count) if count is not None else None
        if n_str is not None:
            # i <= X - 1 wraps around when X = 0, i < X does not
            x = _minus_one(count)
            conj.append(f"i < {self.printer.bv(x)}" if x is not None else f"i <= {n_str}")
        for r in sorted(regs_used):
            if r in ind:
                iv = ind[r]
                conj.append(f"s {self.arch.reg(r)} = {self.printer.bv(iv.init)} ⊕ {iv.step} * i")
            elif r in inv:
                conj.append(f"s {self.arch.reg(r)} = {self.printer.bv(inv[r])}")
        self.header_conj = conj
        self.header_regs = sorted(r for r in regs_used if r in ind or r in inv)
        self.header_time = f"{pre} + i * ({body})"

        # Postcondition: one disjunct per exit group. Each records the proof case
        # that reaches it ("header" after the loop, "entry" when the loop is
        # skipped), its witness, and the addresses that end its traces, which
        # the generated proof uses to pick it.
        # At a return the trace head is the return instruction, which the tail
        # time includes; an exit outside the function is not executed (t').
        ct = lambda ex: "cycle_count_of_trace t'" if ex in self.extra_exits else "cycle_count_of_trace t"
        items = []
        for (ex, _), g in groups.items():
            tail = self._sum(g["tail"])
            ends = {self._trace_end(pi, ex, "header") for pi, _ in g["paths"]}
            if "count" in g:
                t = f"{pre} + {self.printer.bv(g['count'])} * ({body}) + {tail}"
                items.append(dict(ex=ex, text=f"{ct(ex)} {self.rel} {t}", case="header",
                                  witness=None, count=self.printer.bv(g["count"]), ends=ends))
            else:
                bound = f"j <= {n_str} /\\ " if n_str is not None else ""
                items.append(dict(ex=ex, text=f"(exists j, {bound}{ct(ex)} {self.rel} {pre} + j * ({body}) + {tail})",
                                  case="header", witness="i", count=None, ends=ends))
        for ex, alts in noloop.items():
            items.append(dict(ex=ex, text=f"{ct(ex)} {self.rel} {self._join([a for _, a in alts])}",
                              case="entry", witness=None, count=None,
                              ends={self._trace_end(pi, ex, "entry") for pi, _ in alts}))
        # _join may have changed the relation to "<="
        for it in items:
            it["text"] = re.sub(r"(cycle_count_of_trace t'?) = ", r"\1 " + self.rel + " ", it["text"])
        self.items = items
        self.posts = {}
        for it in items:
            self.posts.setdefault(it["ex"], []).append(it["text"])
        self.count = n_str
        return self

    def static_ends(self, case: str) -> List[Tuple[int, int]]:
        """(exit, previous instruction) pairs the CFG allows in a proof case:
        from the entry, or from the header without passing it again."""
        succ = successors(self.func)
        start = self.func.entry_point if case == "entry" else self.h
        region, work = {start}, [start]
        while work:
            for m in succ.get(work.pop(), ()):
                if m != self.h and m not in region:
                    region.add(m)
                    work.append(m)
        out = []
        for b in self.func.blocks:
            if b.start_vaddr not in region:
                continue
            ins = b.instructions
            for k, i in enumerate(ins):
                if i.offset not in self.posts or i.offset in self.extra_exits:
                    continue
                if k > 0:
                    out.append((i.offset, ins[k - 1].offset))
                elif b.start_vaddr == start:
                    out.append((i.offset,))
                else:
                    out += [(i.offset, p.instructions[-1].offset) for p in self.func.blocks
                            if p.start_vaddr in region and b.start_vaddr in succ.get(p.start_vaddr, ())]
        return out

    def _trace_end(self, pi: int, ex: int, case: str) -> Tuple[int, ...]:
        """Last two addresses of path pi's trace at exit ex, newest first. For an
        exit outside the function the trace ends at the jump that leaves it."""
        path = self.paths[pi]
        if case == "header":
            # the trace before the last header visit is generalized away
            path = path[max(k for k, a in enumerate(path) if a == self.h):]
        addrs = [i.offset for a in path for i in self.func.get_block(a).instructions]
        if ex not in self.extra_exits:
            addrs = addrs[:addrs.index(ex) + 1] if ex in addrs else addrs + [ex]
        return tuple(reversed(addrs[-2:]))


# Proof file

LTAC = r"""
(* TIG: the loop invariant after i iterations. An inductive, so that the
   stepper does not unfold it. *)
Inductive tig_loop_inv (P : N -> Prop) : Prop := tig_inv (i : N) (_ : P i).
(* postcondition of an exit no explored path reached *)
Inductive tig_unexplored : Prop := .
(* TIG: closing tactics *)
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
(* turn mod and div into linear constraints *)
Local Ltac tig_pow :=
  repeat match goal with
  | |- context[2 ^ ?n] => let v := eval vm_compute in (2 ^ n) in change (2 ^ n) with v
  | H: context[2 ^ ?n] |- _ => let v := eval vm_compute in (2 ^ n) in change (2 ^ n) with v in H
  end.
Local Ltac tig_arith :=
  tig_bc; unfold msub in *;
  rewrite ?N.shiftl_mul_pow2, ?N.shiftr_div_pow2 in *; tig_pow;
  zify; Z.div_mod_to_equations; Z.quot_rem_to_equations; lia.
(* what psimpl leaves: x xor x (x86 xor eax, eax) and casts of 0 *)
Local Ltac tig_norm :=
  rewrite ?N.lxor_nilpotent, ?N.Div0.mod_0_l in *;
  repeat match goal with
  | |- context[scast ?a ?b 0] =>
      let v := eval vm_compute in (scast a b 0) in change (scast a b 0) with v
  end.
(* Split conjunctions and solve each one. On a path that leaves the loop, the
   iteration i equals the count n. *)
Local Ltac tig_close i n :=
  lazymatch goal with
  | |- _ /\ _ => split; [ tig_close i n | tig_close i n ]
  | |- _ => first [ assumption | reflexivity
                  | tig_norm;
                    (tryif constr_eq i n then idtac else replace i with n in * by tig_arith);
                    hammer; tig_ifs; solve [ lia | tig_arith ] ]
  end.
"""


def _dispatch(lf: LoopFormula, at, case: str, w: str):
    """Tactic for the goals of a proof case, and the exits it admits. A goal is
    the loop invariant (witness w + 1 after an iteration, 0 from the entry) or
    a postcondition disjunct, picked by the addresses that end its trace."""
    arms, admitted = [], []
    nxt = "(i + 1)" if case == "header" else w
    arms.append(f"| |- tig_loop_inv _ => apply (tig_inv _ {nxt}); cbv beta; tig_close {w} {w}")
    by_end: Dict[Tuple[int, ...], List[Tuple[int, Dict]]] = {}
    for it in lf.items:
        if it["case"] != case:
            continue
        k = [x["text"] for x in lf.items if x["ex"] == it["ex"]].index(it["text"])
        for e in it["ends"]:
            by_end.setdefault(e, []).append((k, it))
    for e in sorted(by_end, key=len, reverse=True):
        pat = " :: ".join(f"(Addr {at(a):#x}, _)" for a in e) + " :: _"
        its = by_end[e]
        if len({k for k, _ in its}) > 1:
            admitted.append(e[0])
            arms.append(f"| |- context[ {pat} ] => admit")
            continue
        k, it = its[0]
        m = len(lf.posts[it["ex"]])
        pick = "right; " * k + ("left; " if k < m - 1 else "")
        inst = f"exists {w}; " if it["witness"] else ""
        n = f"({it['count']})" if it["count"] else w
        arms.append(f"| |- context[ {pat} ] => {pick}{inst}tig_close {w} {n}")
    # trace endings the CFG allows but no explored path took
    for e in sorted(set(lf.static_ends(case)) - set(by_end)):
        pat = " :: ".join(f"(Addr {at(a):#x}, _)" for a in e) + " :: _"
        admitted.append(e[0])
        arms.append(f"| |- context[ {pat} ] => admit")
    if lf.unexplored:
        admitted += lf.unexplored
        arms.append("| |- tig_unexplored => admit")
    arms.append('| |- ?g => idtac "TIG: unexpected goal:" g; fail "TIG: unexpected goal"')
    return "      all: lazymatch goal with\n      " + "\n      ".join(arms) + "\n      end.", admitted


def _destruct(names):
    return f"destruct PRE as ({' & '.join(names)})." if len(names) > 1 else f"rename PRE into {names[0]}."


def emit_loop_proof(arch, func, lf: LoopFormula, header: str, binary: str, ignore: str = "") -> str:
    name, P, at, W = func.name, arch.proof, loc(arch, func), arch.width
    pr = lf.printer
    regs = sorted(pr.regs)
    params = (["mem"] if pr.uses_mem else []) + regs
    binders = (" (mem : memory)" if pr.uses_mem else "") + (f" ({' '.join(regs)} : N)" if regs else "")
    args = (" " + " ".join(params)) if params else ""
    bounds = [f"{r} < 2^{W}" for r in regs]
    assumes = lf.assumptions
    eqs = ([f"s {arch.mem_var} = mem"] if pr.uses_mem else []) + [f"s {arch.reg(r)} = {r}" for r in regs]
    entry = func.entry_point
    hconj = lf.header_conj + bounds + assumes + [f"cycle_count_of_trace t' {lf.rel} {lf.header_time}"]
    header_inv = "tig_loop_inv (fun i => " + " /\\\n        ".join(hconj) + ")"
    arms = []
    if entry != lf.h:
        arms.append(f"| {at(entry):#x} => Some ({' /\\ '.join(eqs + bounds + assumes + ['cycle_count_of_trace t' + chr(39) + ' = 0'])})")
    arms.append(f"| {at(lf.h):#x} => Some ({header_inv})")
    for ex, ps in sorted(lf.posts.items()):
        arms.append(f"| {at(ex):#x} => Some ({' \\/'.join(chr(10) + '        ' + p for p in ps)})")
    # returns no explored path reached
    unexplored = sorted({i.offset for b in func.blocks for i in b.instructions
                         if arch.is_return(i)} - set(lf.posts))
    for ex in unexplored:
        arms.append(f"| {at(ex):#x} => Some tig_unexplored")
    exits = sorted(set(lf.posts) | set(unexplored))

    hyps = (f"\n         (MEM: s {arch.mem_var} = mem)" if pr.uses_mem else "") + \
        "".join(f"\n         ({r.upper()}: s {arch.reg(r)} = {r})" for r in regs) + \
        "".join(f"\n         (ASSUME{k}: {a})" for k, a in enumerate(assumes))
    poses = "".join(f"\n    pose proof (models_var {arch.reg(r)} MDL) as B_{r.upper()}; simpl in B_{r.upper()};"
                    f" rewrite {r.upper()} in B_{r.upper()}." for r in regs)
    entry_names = (["MEM"] if pr.uses_mem else []) + [r.upper() for r in regs] + \
        [f"B_{r.upper()}" for r in regs] + [f"ASSUME{k}" for k in range(len(assumes))] + ["Cycles"]
    head_names = ["i"] + [f"L{k}" for k in range(len(lf.header_conj))] + \
        [f"B_{r.upper()}" for r in regs] + [f"ASSUME{k}" for k in range(len(assumes))] + ["Cycles"]
    lf.unexplored = unexplored
    cases, admitted = [], []
    if entry != lf.h:
        tac, adm = _dispatch(lf, at, "entry", "0")
        admitted += adm
        cases.append(f"""    (* {at(entry):#x}: entry -> loop header / exit *)
    {{ {_destruct(entry_names)}
      repeat step.
{tac} }}""")
    tac, adm = _dispatch(lf, at, "header", "i")
    admitted += adm
    cases.append(f"""    (* {at(lf.h):#x}: loop header -> loop header / exit *)
    {{ destruct PRE as [i PRE]; cbv beta in PRE. {_destruct(head_names[1:])}
      repeat step.
{tac} }}""")
    cases = "\n\n".join(cases)
    lf.admitted = admitted
    return f"""(* Generated by TIG (Cloq backend, heuristic loop invariants) *)
{proof_preamble(arch, func, exits, header + chr(10) + "From Stdlib Require Import ZArith Lia.", binary)}
{LTAC}
Definition {name}_timing_invs{binders}
    (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
{chr(10).join(arms)}
| _ => None end | _ => None end.

Theorem {name}_timing:
  forall s t s' x'{args}
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models {P["typctx"]} s){hyps},
  satisfies_all
    lifted_prog
    ({name}_timing_invs{args})
    exits
  ((x',s')::t).
Proof using.
    intros.{poses}
    apply prove_invs.
    Local Ltac step := tstep {P["step"]}.
{ignore}
    simpl. rewrite ENTRY. unfold entry_addr. step.
    lazymatch goal with
    | |- tig_loop_inv _ => apply (tig_inv _ 0); cbv beta; tig_close 0 0
    | |- _ => tig_close 0 0
    end.

    intros.
{proof_setup(arch)}

{cases}
{"Admitted." if admitted else "Qed."}

End TimingProof.
"""


def emit_riscv_loop_proof(func, lf, header, binary):
    return emit_loop_proof(RISCV(), func, lf, header, binary)
