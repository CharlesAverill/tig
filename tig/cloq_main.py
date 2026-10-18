"""tig-cloq: generate a Cloq timing proof for one function.

    GHIDRA_HOME=... python -m tig.cloq_main BIN FUNC --header-from HAND_PROOF.v --out OUT.v
"""
import argparse
import json
import os
import re
import sys
import traceback

from tig.bininfo import Function
from tig.cloq import ARCHS, Formula, Unsupported, emit_riscv_proof
from tig.loops import RISCV_GPRS, LoopFormula, emit_riscv_loop_proof, find_loops
from tig.extract_basic_blocks import extract_bb, get_non_terminated_functions
from tig.symbolic_execution import exec_func, get_project


class _Done(Exception):
    pass


def header_from(hand_proof: str):
    """Reuse the hand-written proof's imports and binary binding."""
    src = open(hand_proof).read()
    head = src.split("Module TimingProof")[0].strip()
    m = re.search(r"Definition binary := ([\w.]+)\.", src)
    if m is not None:
        return head, m.group(1)
    # the program is written out in the proof (Definition binary (a : addr) : N := match ...)
    m = re.search(r"Definition binary\s*\(a : addr\) : N :=(.*?end)\.", src, re.S)
    if m is None:
        raise SystemExit(f"no `Definition binary` in {hand_proof}")
    return head, "fun (a : addr) =>" + m.group(1)


def fill_empty_blocks(fdata, project):
    """Ghidra's block script drops some instructions (e.g. x86 RET at the end
    of a block); disassemble whatever part of each block it left uncovered."""
    import capstone
    arch = project.arch
    for b in fdata["blocks"]:
        covered = sum(int(i["instr_size"]) for i in b["instructions"])
        if covered >= b["bb_size"]:
            continue
        start = b["bb_start_vaddr"] + covered
        code = project.loader.memory.load(start, b["bb_size"] - covered)
        mode = capstone.CS_MODE_64 if arch.bits == 64 else capstone.CS_MODE_THUMB
        cs = capstone.Cs(capstone.CS_ARCH_X86 if arch.bits == 64 else capstone.CS_ARCH_ARM, mode)
        for i in cs.disasm(code, start):
            b["instructions"].append({
                "instr_offset": i.address, "instr_size": i.size, "mnem": i.mnemonic.upper(),
                "operands": [o.strip() for o in i.op_str.split(",") if o.strip()],
                "regs_read": [], "regs_written": [], "results": "",
                "instruction_str": f"{i.mnemonic.upper()} {i.op_str.upper()}".strip(),
                "instruction_byte": i.bytes.hex(), "is_big_endian": "false"})


def hook_zbb(project, func):
    """pypcode's RISC-V SLEIGH spec lacks the Zbb logic-with-negate
    instructions; emulate them with angr hooks."""
    ops = {"andn": lambda a, b: a & ~b, "orn": lambda a, b: a | ~b, "xnor": lambda a, b: ~(a ^ b)}
    for b in func.blocks:
        for i in b.instructions:
            if i.mnem in ops:
                rd, rs1, rs2 = i.operands[:3]
                def h(state, f=ops[i.mnem], rd=rd, rs1=rs1, rs2=rs2):
                    v = f(state.registers.load(rs1), state.registers.load(rs2))
                    if rd != "zero":
                        state.registers.store(rd, v)
                project.hook(i.offset, h, length=i.size)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bin")
    ap.add_argument("func")
    ap.add_argument("--arch", default="riscv", choices=sorted(ARCHS))
    ap.add_argument("--objdump", default=None,
                    help="objdump for RISC-V operand syntax; other ISAs use Ghidra's disassembly")
    ap.add_argument("--dump-times", default=None,
                    help="write each instruction's Cloq timing term (relative to the entry) as JSON")
    ap.add_argument("--header-from", default=None)
    ap.add_argument("--out", required=True)
    ap.add_argument("--loop-bound", type=int, default=3,
                    help="loop iterations to explore when guessing invariants")
    ap.add_argument("--lazy-solves", action="store_true",
                    help="do not check branch feasibility during exploration")
    ap.add_argument("--report", default=None, help="JSON file to write a status record to")
    args = ap.parse_args()
    arch = ARCHS[args.arch]
    if args.objdump is None:
        args.objdump = "/opt/riscv/bin/riscv32-unknown-elf-objdump" if args.arch == "riscv" else "none"

    record = {"func": args.func, "status": None, "detail": ""}
    try:
        cache = f"{args.bin}.json"
        if os.path.exists(cache):
            data = json.load(open(cache))
        else:
            data = extract_bb(args.bin, cache, objdump=args.objdump)
        no_term = [a for _, a in get_non_terminated_functions(data)]
        fdata = [x for x in data if x["function_name"] == args.func]
        if not fdata:
            raise Unsupported(f"function {args.func} not found by Ghidra")
        # Ghidra's block script leaves some blocks (x86 RET blocks) without
        # instructions; disassemble those with angr.
        with open(args.bin, "rb") as fh:
            is_pie = fh.read(18)[16] == 3  # e_type == ET_DYN
        p = get_project(args.bin, 0x100000 if is_pie else None, arch.lang)
        fill_empty_blocks(fdata[0], p)
        func = Function(fdata[0])
        if args.arch == "riscv":
            hook_zbb(p, func)
        if args.arch == "amd64" and os.environ.get("CLOQ_AMD64_MODEL"):
            ARCHS["amd64"].load_model(os.environ["CLOQ_AMD64_MODEL"])
        if args.dump_times:
            times = {}
            for b in func.blocks:
                for i in b.instructions:
                    rel = hex(i.offset - func.entry_point)
                    times[rel] = (list(arch.branch_times(i)) if arch.is_branch(i)
                                  else arch.instr_time(i, ("?",)))
                    times[rel + "_asm"] = i.instr_str
            json.dump(times, open(args.dump_times, "w"), indent=1)
        # (p loads at Ghidra's addresses: Ghidra rebases position-independent
        # ELFs to 0x100000; other ELFs keep their link addresses.)
        loops = find_loops(func)
        if loops:
            if args.arch != "riscv":
                raise Unsupported("loop invariants are only implemented for RISC-V")
            if len(loops) > 1:
                raise Unsupported(f"{len(loops)} loops (only single, non-nested loops get invariants)")
            (h, body), = loops.items()
            # Branch targets outside the function that are not calls end the function too.
            extra = sorted({x for b in func.blocks for x in b.exit_vaddrs if x not in func.block_dict}
                           | {b.instructions[-1].offset + b.instructions[-1].size for b in func.blocks
                              if arch.is_branch(b.instructions[-1])
                              and b.instructions[-1].offset + b.instructions[-1].size not in func.block_dict})
            res = exec_func(p, func, no_term, state_args=arch.state_args, loop_bound=args.loop_bound,
                            snapshots=({h}, RISCV_GPRS), extra_exits=extra,
                            lazy_solves=args.lazy_solves)
            lf = LoopFormula(arch, func, res, h, body, extra).build()
            record.update(header=hex(h), count=lf.count, relation=lf.rel,
                          paths=len(lf.paths), assumptions=lf.assumptions)
            head, binary = header_from(args.header_from)
            open(args.out, "w").write(emit_riscv_loop_proof(func, lf, head, binary))
            record.update(status="generated", exits=[hex(e) for e in sorted(lf.posts)])
            raise _Done
        res = exec_func(p, func, no_term, state_args=arch.state_args)
        f = Formula(arch, func, res)
        record["paths"] = len(f.traces)
        formula = f.build()
        exits = sorted({func.get_block(t[-1]).instructions[-1].offset for t in f.traces})
        if args.arch != "riscv":
            raise Unsupported(f"postcondition generated, but proof emission is only implemented for RISC-V: {formula}")
        head, binary = header_from(args.header_from)
        proof = emit_riscv_proof(func, formula, f.printer, exits, head, binary)
        open(args.out, "w").write(proof)
        record.update(status="generated", exits=[hex(e) for e in exits])
    except _Done:
        pass
    except Unsupported as e:
        record.update(status="unsupported", detail=str(e))
    except Exception as e:
        record.update(status="crash", detail=f"{type(e).__name__}: {e}"[:300])
        traceback.print_exc()
    print(json.dumps(record))
    if args.report:
        json.dump(record, open(args.report, "w"))


if __name__ == "__main__":
    main()
