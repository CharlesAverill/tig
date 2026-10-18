"""Rebuild a RISC-V ELF from a lifted Picinae program (`| 0xADDR => 0xWORD`).

The lifted Rocq file is what a Cloq proof actually verifies, so analyzing an
ELF rebuilt from it guarantees TIG sees the same code.  `(* <sym> *)` comments
become function symbols so that Ghidra recovers the same functions.

    python eval/synth_elf.py LIFTED.v OUT.elf [--def NAME]
"""
import argparse
import os
import re
import subprocess
import tempfile

TOOL = "/opt/riscv/bin/riscv32-unknown-elf-"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("lifted")
    ap.add_argument("out")
    ap.add_argument("--def", dest="defn", default=None,
                    help="only read the given Definition (for files with several)")
    ap.add_argument("--sym", action="append", default=[],
                    help="extra function symbol NAME@ADDR (for unannotated listings)")
    args = ap.parse_args()
    src = open(args.lifted).read()
    if args.defn:
        m = re.search(r"Definition " + args.defn + r"\b.*?\n\s*end\.", src, re.S)
        src = m.group(0)
    words, syms, cur = {}, [], None
    for line in src.splitlines():
        m = re.search(r"\(\*\s*<([\w.$]+)>\s*\*\)", line)
        if m:
            cur = m.group(1)
            continue
        m = re.search(r"\|\s*(0x[0-9a-fA-F]+)\s*=>\s*(0x[0-9a-fA-F]+)", line)
        if m:
            a, w = int(m.group(1), 16), int(m.group(2), 16)
            words[a] = w
            if cur is not None:
                syms.append((cur, a))
                cur = None
    for spec in args.sym:
        n, a = spec.split("@")
        syms.append((n, int(a, 0)))
    syms.sort(key=lambda x: x[1])
    addrs = sorted(words)
    asm = [".section .text", ".option norvc", ".option norelax"]
    starts = {a: s for s, a in syms}
    ends = [a for _, a in syms][1:] + [addrs[-1] + 4]
    for (s, a), e in zip(syms, ends):
        asm.append(f".globl {s}\n.type {s}, @function\n.set {s}, {a}\n.size {s}, {e - a}")
    pc = addrs[0]
    asm.append(f".org {addrs[0]}")
    for a in addrs:
        if a != pc:
            asm.append(f".org {a}")
        asm.append(f".insn 0x{words[a]:08x}")  # .word would be marked as data ($d)
        pc = a + 4
    # Minimal .data/.bss: the original TIG expects both sections to exist.
    asm += [".section .data", ".word 0", ".section .bss", ".space 4"]
    with tempfile.TemporaryDirectory() as d:
        s, o = os.path.join(d, "p.S"), os.path.join(d, "p.o")
        open(s, "w").write("\n".join(asm) + "\n")
        subprocess.run([TOOL + "as", "-march=rv32imac_zicsr_zbb", "-o", o, s], check=True)
        subprocess.run([TOOL + "ld", "-Ttext=0", "-e", "0", "--no-relax", "-o", args.out, o], check=True)
    print(f"{args.out}: {len(words)} words, {len(syms)} symbols")


if __name__ == "__main__":
    main()
