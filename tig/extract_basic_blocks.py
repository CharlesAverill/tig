import os
import json
import subprocess
import re
from subprocess import Popen, PIPE
from typing import List, Dict, Any, Tuple


def basic_extract_bb(binary_path: str) -> List[Dict[str, Any]]:
    """Extract basic blocks using ghidra_scripts/GetBasicBlocks.java via Docker

    Args:
        binary_path (str): Path to binary to analyze

    Raises:
        Exception: If Docker processes returned a non-zero exit code

    Returns:
        List[Dict[str, Any]]: A list of function dictionaries loaded from the output JSON
    """
    bin_name = os.path.basename(binary_path)
    bin_dir = os.path.dirname(os.path.abspath(binary_path))

    docker_run = (
        subprocess.run(
            [
                "docker",
                "run",
                "-dt",
                "-v",
                f"{bin_dir}:/samples",
                "ghidra-bbextract",
                f"/samples/{bin_name}",
            ],
            capture_output=True,
        )
        .stdout.decode()
        .strip()
    )
    container_id = docker_run[:12]

    ret = (
        subprocess.run(["docker", "logs", "-f", container_id], capture_output=True)
        .stdout.decode()
        .strip()
    )
    exit_code = (
        subprocess.run(["docker", "wait", container_id], capture_output=True)
        .stdout.decode()
        .strip()
    )

    subprocess.run(["docker", "rm", container_id], capture_output=True)

    if exit_code != "0":
        raise Exception(f"ghidra-bbextract failed with code {exit_code}: {ret}")

    return json.loads(ret)


def execute_objdump(binary, obj_bin="llvm-objdump", offset=0, do_offset=False):
    if do_offset:
        cmd = f"{obj_bin} -d --adjust-vma={offset} -M no-aliases {binary}"
    else:
        cmd = f"{obj_bin} -d -M no-aliases {binary}"
    print(f"Executing `{cmd}`")
    p = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE)
    out, err = p.communicate()
    if p.returncode != 0:
        print(err.decode())
        # NOTE / TODO: assume is x86, adjust offset
        if do_offset:
            cmd = f"{obj_bin} -d --adjust-vma={offset} {binary}"
        else:
            cmd = f"{obj_bin} -d {binary}"
        print(f"Executing `{cmd}`")
        p = Popen(cmd, shell=True, stdout=PIPE, stderr=PIPE)
        out, err = p.communicate()
        if p.returncode != 0:
            print(err.decode())
            exit(1)

    if do_offset:
        return out.decode()

    output = out.decode()
    for line in output.splitlines():
        if not re.match(r"^\s*[0-9a-f]+\s+<", line):
            continue
        addr = int(line.split()[0], 16)
        if addr != offset:
            return execute_objdump(binary, obj_bin, offset, True)
        break

    return output


def get_objdump_results(binary, obj_bin="llvm-objdump", offset=0):
    disassembly = {}

    output = execute_objdump(binary, obj_bin, offset)

    for line in output.splitlines():
        if not re.match(r"^\s*[0-9a-f]+:\s", line):
            continue
        address, rest = line.split(":", 1)
        address = int(address, 16)
        rest = rest.split("#")[0]
        byte_string, instr = re.split(r"\s{2,}", rest, 1)
        byte_string = byte_string.replace(" ", "")
        if "\t" not in instr:
            # disassembly[address] = {
            #        "mnem": "",
            #        "operands": "",
            #        "instruction_str": "",
            #        "instruction_byte": byte_string,
            #        "used": False
            #        }
            # continue
            mnem = instr
            op_str = ""
        else:
            mnem, op_str = instr.split("\t")
        op_str = op_str.strip().replace(", ", ",")
        mnem = mnem.strip()
        instr = f"{mnem} {op_str}".strip()
        op_str = re.sub(r"<[\w_+-]+>", "", op_str).strip()
        disassembly[address] = {
            "mnem": mnem,
            "operands": op_str,
            "instruction_str": instr,
            "instruction_byte": byte_string,
            "used": False,
        }
    return disassembly


def extract_bb(
    binary_path: str,
    out_path: str,
    offset: int = 0,
    objdump: str = "riscv32-unknown-elf-objdump",
) -> List[Dict[str, Any]]:
    """Extract basic blocks from a binary and unfold pseudoinstructions

    Args:
        binary_path (str): Path to binary to analyze
        out_path (str): Path to write analysis output JSON to
        offset (int, optional): Offset to apply during pseudoinstruction unfolding. Defaults to 0.
        objdump (str, optional): Objdump binary. Defaults to "riscv32-unknown-elf-objdump".

    Returns:
        List[Dict[str, Any]]: A list of function dictionaries loaded from the output JSON and with pseudoinstructions unfolded
    """
    objdump_results = get_objdump_results(binary_path, objdump, offset)

    bb = basic_extract_bb(binary_path)

    remove_empty = lambda l: [x for x in l if len(x)]

    instr_cnt = 0
    for func_data in bb:
        for block in func_data["blocks"]:
            for instr in block["instructions"]:
                try:
                    new_data = objdump_results[instr["instr_offset"]]
                    instr["mnem"] = new_data["mnem"]
                    instr["operands"] = new_data["operands"].split(",")
                    instr["instruction_str"] = new_data["instruction_str"]
                    instr["regs_read"] = remove_empty(instr["regs_read"].split(","))
                    instr["regs_written"] = remove_empty(
                        instr["regs_written"].split(",")
                    )
                    objdump_results[instr["instr_offset"]]["used"] = True
                    instr_cnt += 1
                except KeyError as e:
                    print(f"===Skipping {instr}, no {e}===")
    if instr_cnt != len(objdump_results):
        bb.append(
            {
                "function_name": "_OBJDUMP_ORPHANS",
                "blocks": [
                    {
                        "bb_start_vaddr": -1,
                        "bb_size": -1,
                        "is_exit_point": False,
                        "is_entry_point": True,
                        "exit_vaddrs": [],
                        "source_vaddrs": [],
                        "instr_mode": "?",
                        "instructions": [],
                    }
                ],
            }
        )
        for addr, data in objdump_results.items():
            if not data["used"]:
                bb[-1]["blocks"][0]["instructions"].append(
                    {
                        "instr_offset": addr,
                        "instr_size": len(data["instruction_byte"]) / 2,
                        "mnem": data["mnem"],
                        "operands": data["operands"].split(","),
                        "regs_read": "?",
                        "results": "?",
                        "instruction_str": data["instruction_str"],
                        "instruction_byte": data["instruction_byte"],
                        "is_big_endian": False,
                    }
                )

    with open(out_path, "w") as fd:
        json.dump(bb, fd, indent=2)

    return bb


def get_non_terminated_functions(bb_data: List) -> List[Tuple[str,int]]:
    no_terms = []
    for function in bb_data:
        has_exit = False
        for block in function["blocks"]:
            if block["is_exit_point"]:
                has_exit = True
                break
        if not has_exit:
            addr = function["blocks"][0]["bb_start_vaddr"]
            func_name = function["function_name"]
            no_terms.append((func_name, addr))
            #print(hex(addr), func_name)
    return no_terms

