"""Evaluate TIG against the hand-written Cloq timing proofs.

For every proof:
  1. legacy:   run TIG as published (original commit, legacy emitter);
  2. generate: run TIG with the Cloq backend;
  3. standalone: compile the generated proof (TIG invariants + generic script);
  4. substituted: compile the hand proof with its postcondition replaced by
     TIG's (does TIG produce the timing invariant the proof needs?).

Rocq jobs run one at a time.  Results are appended to a JSONL file.

    python eval/run_eval.py ENTRIES.json RESULTS.jsonl
"""
import json
import os
import subprocess
import sys
import time

TIG = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ORIG = os.path.join(os.path.dirname(TIG), "tig-orig")
PY = os.path.join(TIG, ".venv", "bin", "python")


def _cap_memory():
    # angr path explosion can exhaust RAM; give each analysis 3 GB.
    import resource
    resource.setrlimit(resource.RLIMIT_AS, (3 << 30, 3 << 30))


def sh(cmd, cwd, timeout):
    t = time.time()
    capped = cmd[0] == PY and "substitute.py" not in " ".join(cmd)
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout,
                           preexec_fn=_cap_memory if capped else None)
        return p.returncode, p.stdout + p.stderr, time.time() - t
    except subprocess.TimeoutExpired as e:
        return "timeout", (e.stdout or b"").decode(errors="ignore") if isinstance(e.stdout, bytes) else (e.stdout or ""), time.time() - t


def rocq_error(log):
    lines = [l for l in log.splitlines() if not l.startswith("Tactic call")]
    for i, l in enumerate(lines):
        if l.startswith("Error"):
            return " ".join(lines[i:i + 3])[:200]
    return ""


def main():
    entries = json.load(open(sys.argv[1]))
    out = sys.argv[2]
    cfg = entries["config"]
    done = set()
    if os.path.exists(out):
        done = {json.loads(l)["id"] for l in open(out)}
    rocq_dir = cfg["rocq_dir"]
    env_rocq = ["rocq", "compile", "-R", "../../", "Picinae"]
    for e in entries["proofs"]:
        if e["id"] in done:
            continue
        rec = {"id": e["id"], "arch": e.get("arch", "riscv")}
        # 2. Cloq backend
        gen = os.path.join(rocq_dir, "tig_out", "tig_" + e["id"] + ".v")  # prefix avoids clashes with lifted files
        rc, log, dt = sh([PY, "-m", "tig.cloq_main", e["elf"], e["func"], "--arch", rec["arch"],
                          "--header-from", e["hand"], "--out", gen] + e.get("extra", []), TIG, 900)
        try:
            rec["generate"] = json.loads([l for l in log.splitlines() if l.startswith('{"func"')][-1])
        except Exception:
            rec["generate"] = {"status": "crash" if "MemoryError" not in log else "out-of-memory (3 GB cap)",
                               "detail": log[-300:]}
        rec["generate"]["secs"] = round(dt)
        # 1. legacy TIG, RISC-V only (runs after generation, which caches Ghidra's output)
        if rec["arch"] == "riscv":
            rc, log, dt = sh([PY, "-m", "tig.tig", e["elf"], e["func"]], ORIG, 600)
            err = [l for l in log.splitlines() if "Error" in l or "Exception" in l]
            rec["legacy"] = {"rc": rc, "secs": round(dt), "err": err[-1][:160] if err else "",
                             "err_time": log.count("(* ERROR:"),
                             "time_inf": log.count("time_inf") - 1}
        if rec["generate"].get("status") == "generated":
            # 3. standalone
            rc, log, dt = sh(env_rocq + [os.path.relpath(gen, rocq_dir)], rocq_dir, cfg["timeout"])
            rec["standalone"] = {"rc": rc, "secs": round(dt), "err": rocq_error(log) if rc else ""}
            # 4. substituted into the hand proof
            # A hand loop proof's invariants fit its own postcondition, so loop
            # proofs are only checked standalone.
            if not e.get("skip_substitute") and "header" not in rec["generate"]:
                sub = os.path.join(rocq_dir, "tig_sub", e["id"] + ".v")
                rc, log, _ = sh([PY, "eval/substitute.py", e["hand"], gen, sub], TIG, 60)
                if rc != 0:
                    rec["substituted"] = {"rc": "subst-failed", "err": log.strip()[-200:]}
                else:
                    rc, log, dt = sh(env_rocq + [os.path.relpath(sub, rocq_dir)], rocq_dir, cfg["timeout"])
                    rec["substituted"] = {"rc": rc, "secs": round(dt), "err": rocq_error(log) if rc else ""}
        print(json.dumps(rec), flush=True)
        with open(out, "a") as f:
            f.write(json.dumps(rec) + "\n")


if __name__ == "__main__":
    main()
