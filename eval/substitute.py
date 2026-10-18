"""Substitute a TIG-generated postcondition into a hand-written Cloq proof.

The hand proof's `time_of_<f>` keeps its own binders; only the right-hand side
of `cycle_count_of_trace t = ...` is replaced.  TIG's parameters (mem and
initial registers) are renamed to the hand proof's names, recovered from the
entry invariant (`s V_MEM32 = base_mem`, `s R_A0 = xTask`, ...).

    python eval/substitute.py HAND.v GENERATED.v OUT.v
"""
import re
import sys

FINISHER = """    all: repeat (cbn [negb] in *; match goal with |- context[if ?c then _ else _] =>
           lazymatch c with true => fail | false => fail
           | negb ?c' => destruct c' | _ => destruct c end end);
         cbn [negb] in *; try lia.
"""


def rhs_span(src: str, func: str):
    m = re.search(r"Definition time_of_" + re.escape(func) + r"\b.*?:=\s*cycle_count_of_trace t\s*=", src, re.S)
    if m is None:
        raise SystemExit(f"time_of_{func} not found")
    start = m.end()
    # The definition ends at the first "." followed by whitespace/newline at depth 0.
    depth, i = 0, start
    while i < len(src):
        c = src[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif c == "." and depth == 0 and (i + 1 == len(src) or src[i + 1].isspace()):
            return start, i
        i += 1
    raise SystemExit("unterminated definition")


def entry_names(src: str):
    """Map TIG parameter names to the hand proof's (from its entry invariant)."""
    names = {}
    inv = re.search(r"_timing_invs.*?Some\s*\((.*?)cycle_count_of_trace t'", src, re.S)
    body = inv.group(1) if inv else ""
    m = re.search(r"s V_MEM32 = (\w+)", body)
    if m:
        names["mem"] = m.group(1)
    for r, v in re.findall(r"s R_(\w+) = (\w+)", body):
        names[r.lower()] = v
    return names


def def_names(src: str, func: str, inv_names: dict):
    """Translate invariant-level names to time_of's own binder names, by
    matching argument positions at the call site in the exit invariant."""
    m = re.search(r"Definition time_of_" + re.escape(func) + r"\b(.*?):=", src, re.S)
    binders = []
    for group in re.findall(r"\(([^():]+):", m.group(1)):
        binders += group.split()
    call = re.search(r"time_of_" + re.escape(func) + r"((?:\s+[\w']+)+)\s*\)", src[m.end():])
    args = call.group(1).split() if call else []
    pos = dict(zip(args, binders))
    return {k: pos.get(v, v) for k, v in inv_names.items()}


def main():
    hand, gen, out = sys.argv[1:4]
    hsrc, gsrc = open(hand).read(), open(gen).read()
    gfunc = re.search(r"Definition time_of_(\w+)", gsrc).group(1)
    # The hand proof may name its function differently (e.g. after the file).
    hfuncs = re.findall(r"Definition time_of_(\w+)", hsrc)
    func = gfunc if gfunc in hfuncs else (hfuncs[0] if len(hfuncs) == 1 else gfunc)
    gs, ge = rhs_span(gsrc, gfunc)
    formula = gsrc[gs:ge]
    names = def_names(hsrc, func, entry_names(hsrc))
    params = re.search(r"Definition time_of_\w+((?: \([^)]*\))*) \(t : trace\)", gsrc).group(1)
    for p in re.findall(r"\(([\w ]+) :", params):
        for v in p.split():
            if v not in names:
                raise SystemExit(f"hand proof has no binding for TIG parameter {v}")
            formula = re.sub(r"\b" + v + r"\b", "@@" + names[v], formula)
    formula = formula.replace("@@", "")
    hs, he = rhs_span(hsrc, func)
    res = hsrc[:hs] + "\n        (* TIG *) " + formula.strip() + hsrc[he:]
    # Hand scripts are tuned to their own formula's shape; let a generic case
    # split finish goals that differ only by how conditionals are arranged.
    # Keep only the timing module: trailing CPU instantiations restate the
    # hand formula's concrete shape and are not part of the timing theorem.
    end = res.find("End TimingProof.")
    if end >= 0:
        res = res[:end + len("End TimingProof.")] + "\n"
    thm = res.find(f"Theorem {func}_timing")
    i = res.find("Qed.", thm)
    res = res[:i] + FINISHER + res[i:]
    open(out, "w").write(res)


if __name__ == "__main__":
    main()
