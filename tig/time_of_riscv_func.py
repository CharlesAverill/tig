### This script is old, just a reference for manual CFG traversal
import json
import argparse
import os
import subprocess
import re
import sympy as sp
from collections import defaultdict
import networkx as nx
#import matplotlib.pyplot as plt

GHIDRA_ADDR_OFFSET = 0


# time of instr, condition, true time, false time if it branches
def time_of_riscv_instr(mnem, args, store_name, ML):
    time = None
    condition, true_time, false_time = None, None, None

    # Preprocess args into Picinae registers
    #for i in range(len(args)):
    #    arg = args[i]
    #    if (
    #        arg
    #        in "ra sp gp tp t0 t1 t2 t3 t4 t5 t6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7".split(
    #            " "
    #        )
    #    ):
    #        arg = f"R_{arg.upper()}"
    #    args[i] = arg

    if mnem in [
        "add",
        "sub",
        "xor",
        "or",
        "and",
        "slt",
        "sltu",
        "addi",
        "xori",
        "ori",
        "andi",
        "slti",
        "sltiu",
        "lui",
        "auipc",
    ]:
        time = "2"
    elif mnem in ["srl", "sll", "sra"]:
        raise NotImplementedError(f"Shift instructions {mnem} not implemented")
        time = f"3 + ({store_name} {args[2]} / 4 + {store_name} {args[2]} mod 4)"
    elif mnem == "clz":
        #time = f"3 + clz ({store_name} {args[1]}) 32"
        if args[1] is None:
            raise ValueError("clz instruction requires an argument")
        time = f"3 + clz ({args[1]}) 32"
    elif mnem in ["srli", "slli", "srai"]:
        raise NotImplementedError(f"Shift instructions {mnem} not implemented")
        time = f"3 + {args[2]} / 4 + {args[2]} mod 4"
    elif mnem in ["lb", "lh", "lw", "lbu", "lhu", "sb", "sh", "sw"]:
        #time = f"5 + ({ML} - 2)"
        time = "time_mem"
    elif mnem in ["beq", "bne", "blt", "bge", "bltu", "bgeu"]:
        true_time = f"time_branch"
        false_time = "3"
        # NOTE: not using in time_of_BasicBlock
        op1 = "0" if args[0] == "zero" else f"{store_name} {args[0]}"
        op2 = "0" if args[1] == "zero" else f"{store_name} {args[1]}"
        if mnem == "beq":
            condition = f"{op1} =? {op2}"
        elif mnem == "bne":
            condition = f"negb ({op1} =? {op2})"
        elif mnem == "blt":
            condition = f"Z.ltb (toZ 32 {op1}) (toZ 32 {op2})"
        elif mnem == "bge":
            condition = f"Z.geb (toZ 32 {op1}) (toZ 32 {op2})"
        elif mnem == "bltu":
            condition = f"{op1} <? {op2}"
        elif mnem == "bgeu":
            condition = f"negb ({op1} <? {op2})"
        time = f"if {condition} then {true_time} else {false_time}"
    elif mnem in ["jal", "jalr"]:
        #time = f"5 + ({ML} - 1)"
        time = "time_branch"
    elif mnem in ["mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu"]:
        time = f"36"
    else:
        # TODO : last few else ifs in Rocq RISCV timing function
        time = f"(* ERROR: {mnem} {args} *) err_time"

    return (time, condition, true_time, false_time)


def print_bb(results, function_name=""):
    if function_name != "":
        results = [x for x in results if x["function_name"] == function_name]
    for func_data in results:
        func_name = func_data["function_name"]
        blocks = func_data["blocks"]
        if not len(blocks):
            continue
        block_addr = blocks[0]["bb_start_vaddr"] + GHIDRA_ADDR_OFFSET
        print(f"{block_addr:010x}  <{func_name}>:")

        for block in blocks:
            preblock = "    > Src: " + ", ".join(
                f"{addr+GHIDRA_ADDR_OFFSET:x}" for addr in block["source_vaddrs"]
            )
            if block["is_entry_point"]:
                preblock += "(entry)"
            print(preblock)
            block_addr = block["bb_start_vaddr"] + GHIDRA_ADDR_OFFSET
            for instr in block["instructions"]:
                byte_instr = instr["instruction_byte"]
                str_instr = instr["instruction_str"]
                addr = instr["instr_offset"] + GHIDRA_ADDR_OFFSET
                print(f"{addr:7x}:   {byte_instr:20s} {str_instr}")

            problock = "    > Dst: " + ", ".join(
                f"{addr+GHIDRA_ADDR_OFFSET:x}" for addr in block["exit_vaddrs"]
            )
            if block["is_exit_point"]:
                problock += "(exit)"
            print(problock)

            print(time_of_basic_block(block))

            print()
        print()


# Return time of basic block, final instruction info extracted if it's a branch
def time_of_basic_block(block):
    times = [
        time_of_riscv_instr(instr["mnem"], instr["operands"], "s", "ML")[0]
        for instr in block["instructions"][:-1]
    ]
    times = [f"({time})" if " " in time else time for time in times]

    # Check final instruction for branching
    final_instr = block["instructions"][-1]
    final_time, condition, true_time, false_time = time_of_riscv_instr(
        final_instr["mnem"], final_instr["operands"], "s", "ML"
    )
    if condition is None:
        times.append(final_time)

    return f"{' + '.join(times)}", condition, true_time, false_time


def time_of_BasicBlock(block, 
                       cur_trace=[], 
                       cur_instr_args={},
                       all_traces=[]):
    def _get_instr_operands(instr, cur_instr_args, cur_trace):
        args = [None, None, None]
        if instr.mnem in cur_instr_args:
            found = False
            instr_history = cur_trace + [block.start_vaddr, instr.offset]
            collected = cur_instr_args[instr.mnem]
            for history, repr, idx in collected:
                if history == instr_history:
                    args[idx] = repr
                    found = True
            if not found:
                raise ValueError(
                    f"Cannot find instruction {instr.mnem} with history {[hex(a) for a in instr_history]} in args"
                )
        return args

    times = [
        time_of_riscv_instr(instr.mnem, 
                            _get_instr_operands(instr, cur_instr_args, cur_trace),
                            "s", 
                            "ML")[0]
        for instr in block.instructions[:-1]
    ]
    times = [f"({time})" if " " in time else time for time in times]

    # Check final instruction for branching
    final_instr = block.instructions[-1]

    br_instrs = ["beq", "bne", "blt", "bge", "bltu", "bgeu"]
    if final_instr.mnem in br_instrs:
        # NOTE: Assume angr's branch guards true-false matches with exact instruction
        #       Note sure if this is always the case, but it seems to be
        #       e.g. we have (a == b) for `bne` and (a != b) for `beq`
        _, _, true_time, false_time = time_of_riscv_instr(
            final_instr.mnem, final_instr.operands, "s", "ML"
        )
        return f"{' + '.join(times)}", True, true_time, false_time

    if final_instr.mnem in ["jal", "jalr"]:
        # Check return path exists, else infinite
        # check only one exit_vaddr
        if len(block.exit_vaddrs) > 1:
            raise ValueError(f"0x{block.start_vaddr:x} has multiple exit_vaddrs for jal/jalr")
        if len(block.exit_vaddrs) == 0:
            check_trace = cur_trace
        else:
            check_trace = cur_trace + [block.exit_vaddrs[0]]
        found = False
        for trace in all_traces:
            if len(trace) >= len(check_trace) and trace[: len(check_trace)] == check_trace:
                found = True
                break
        if not found:
            return "time_inf", None, None, None

    final_time, condition, true_time, false_time = time_of_riscv_instr(
        final_instr.mnem, final_instr.operands, "s", "ML"
    )
    if condition is not None:
        raise ValueError(f"Shouldn't have condition for {final_instr.mnem}")
    times.append(final_time)

    return f"{' + '.join(times)}", condition, None, None


def time_of_function_basic_blocks(results, function_name):
    func = [x for x in results if x["function_name"] == function_name][0]
    out = f"Definition basic_block_times_{function_name} (s : store) (ML : nat) (addr : N) : option nat :=\n"
    out += "  let err_time := 999 in\n"
    out += "  match addr with\n"
    for block in func["blocks"]:
        block_time, condition, tt, ft = time_of_basic_block(block)
        out += f"  | {hex(block['instructions'][-1]['instr_offset'] + GHIDRA_ADDR_OFFSET)} => {block_time}"
        if condition is not None:
            out += f" + (if {condition} then {tt} else {ft})"
        out += "\n"
    out += "  end.\n\n"
    return out


def preprocess_data(results, function_name):
    for i in range(len(results)):
        if results[i]["function_name"] == function_name:
            break

    blocks = results[i]["blocks"]

    for block in blocks:
        for instr in block["instructions"]:
            instr["operands"] = instr["operands"].split(",")

    results[i]["blocks"] = blocks


def simplify_expression(expr):
    """Simplifies arithmetic expressions, preserving 'if' conditions and combining like terms."""

    # Regular expression to match 'if (...) then ... else ...' expressions
    conditional_pattern = re.compile(r"if\s*\(.*\)\s*then\s*(.*)\s*else\s*(.*)")

    def simplify_branch(match):
        """Simplifies the then/else branches separately."""
        condition = match.group(0).split("then")[0] + "then"
        then_branch = match.group(1).strip()
        else_branch = match.group(2).strip()

        simplified_then = simplify_expression(
            then_branch
        )  # str(sp.simplify(then_branch))
        simplified_else = simplify_expression(
            else_branch
        )  # str(sp.simplify(else_branch))

        return f"{condition} {simplified_then} else {simplified_else}"

    # Simplify each branch within conditionals
    expr = conditional_pattern.sub(simplify_branch, expr)

    # Simplify the remaining arithmetic expression
    tokens = re.findall(r"\b[a-zA-Z_][a-zA-Z0-9_]*\b|\d+|[+\-*/()]", expr)
    sym_expr = " ".join(tokens)

    try:
        simplified = str(sp.simplify(sym_expr))
    except:
        simplified = expr  # Fallback if sympy fails

    return simplified


def compute_dominator_tree(blocks):
    """Compute the dominator tree of a control flow graph (CFG)."""
    cfg = {block["bb_start_vaddr"]: set(block["exit_vaddrs"]) for block in blocks}
    entry = blocks[0]["bb_start_vaddr"]

    nodes = set(cfg.keys())
    dominators = {node: nodes.copy() for node in nodes}
    dominators[entry] = {entry}

    changed = True
    while changed:
        changed = False
        for node in nodes - {entry}:
            preds = {pred for pred in nodes if node in cfg.get(pred, set())}
            new_dom = (
                {node} | set.intersection(*(dominators[p] for p in preds))
                if preds
                else {node}
            )
            if dominators[node] != new_dom:
                dominators[node] = new_dom
                changed = True

    dom_tree = defaultdict(set)
    for node in nodes:
        for dom in dominators[node] - {node}:
            if all(
                dom not in dominators[other] for other in dominators[node] - {node, dom}
            ):
                dom_tree[dom].add(node)

    return dom_tree, entry


def preorder_traversal(dom_tree, node, verbose=False):
    """Preorder traversal of the dominator tree."""
    if verbose:
        print(hex(node))

    out = [node]
    for child in sorted(dom_tree[node]):
        out.extend(preorder_traversal(dom_tree, child, verbose=verbose))
    return out


def draw_dominator_tree(dom_tree, blocks):
    """Draw the dominator tree with instruction details as a top-down tree."""
    G = nx.DiGraph()
    labels = {}

    block_map = {block["bb_start_vaddr"]: block for block in blocks}

    for parent, children in dom_tree.items():
        parent_instrs = "\n".join(
            instr["instruction_str"]
            for instr in block_map[parent].get("instructions", [])
        )
        parent_label = f"=={hex(parent)}==\n{parent_instrs}"
        labels[parent] = parent_label
        for child in children:
            child_instrs = "\n".join(
                instr["instruction_str"]
                for instr in block_map[child].get("instructions", [])
            )
            child_label = f"=={hex(child)}==\n{child_instrs}"
            labels[child] = child_label
            G.add_edge(parent, child)

    pos = nx.nx_agraph.graphviz_layout(
        G, prog="dot"
    )  # Use hierarchical layout for a tree structure

    plt.figure(figsize=(12, 8))
    nx.draw(
        G,
        pos,
        with_labels=True,
        labels=labels,
        node_size=6000,
        node_color="lightblue",
        edge_color="gray",
        font_size=8,
    )
    plt.show()


def generate_timing_invariants(results, function_name):
    func = next(x for x in results if x["function_name"] == function_name)
    blocks = func["blocks"]

    dom_tree, entry = compute_dominator_tree(blocks)

    def negate(b):
        match = re.match(r"\(?negb (.+)\)?", b)
        if match:
            return match.group(1)
        match = re.match(r"Z.ltb (.*)", b)
        if match:
            return f"Z.geb {match.group(1)}"
        match = re.match(r"Z.geb (.*)", b)
        if match:
            return f"Z.ltb {match.group(1)}"
        return f"negb ({b})"

    # Use a defaultdict of lists of sets to track conditions per path
    block_conditions = defaultdict(list)
    block_conditions[entry].append(set())  # Entry block has an empty condition set
    exit_points = []

    for node in preorder_traversal(dom_tree, entry):
        block = next(x for x in blocks if x["bb_start_vaddr"] == node)
        block_time, condition, true_time, false_time = time_of_basic_block(block)

        # Copy in each of these for loops to prevent infinite looping
        if block["is_exit_point"]:
            for path_conditions in block_conditions[node].copy():
                exit_points.append(block["instructions"][-1]["instr_offset"])
                block_conditions[exit_points[-1]].append(
                    path_conditions | {("true", block_time)}
                )
        if len(block["exit_vaddrs"]) == 1:
            for path_conditions in block_conditions[node].copy():
                block_conditions[block["exit_vaddrs"][0]].append(
                    path_conditions | {("true", block_time)}
                )
        elif len(block["exit_vaddrs"]) == 2:
            for path_conditions in block_conditions[node].copy():
                true_path = path_conditions | {
                    (condition, f"{block_time} + {true_time}")
                }
                false_path = path_conditions | {
                    (negate(condition), f"{block_time} + {false_time}")
                }
                block_conditions[block["exit_vaddrs"][0]].append(true_path)
                block_conditions[block["exit_vaddrs"][1]].append(false_path)

    def factorize_conditions(condition_sets):
        """Recursively factor out common conditions."""
        if len(condition_sets) == 1:
            condition, time = list(next(iter(condition_sets)))[0]
            return simplify_expression(time)

        # Group conditions by their first element
        grouped = defaultdict(list)
        for conds in condition_sets:
            if conds:
                first, *rest = sorted(conds, key=lambda x: x[0])
                grouped[first].append(set(rest))
            else:
                grouped[None].append(set())

        # Build nested `if` expressions
        if None in grouped:  # There is a fallback case
            fallback = factorize_conditions(grouped.pop(None))
        else:
            fallback = None

        clauses = []
        for cond, sub_conditions in grouped.items():
            inner_expr = factorize_conditions(sub_conditions)
            clauses.append(f"if {cond[0]} then ({inner_expr})")

        result = " else ".join(clauses)
        if fallback:
            result += f" else {fallback}"
        return result

    invariants = {}
    for k, v in block_conditions.items():
        # structured_conditions = [set(x) for x in v if x]  # Convert lists to sets
        # factored_expression = factorize_conditions(structured_conditions)
        # invariants[k] = factored_expression
        invariant = "time_of_trace t' = "
        if len(v) == 1:
            v = v[0]
            if v == set():
                invariant = "True"
            else:
                invariant += simplify_expression(" + ".join([x[1] for x in v]))
        else:
            for conditions_times in (x for x in v if x):
                conditions = " && ".join(
                    [x[0] for x in conditions_times if x[0] != "true"]
                ).strip()
                times = simplify_expression(
                    " + ".join([x[1] for x in conditions_times])
                ).strip()
                invariant += f"if {conditions} then {times} else "
            invariant += "err_time"
        invariants[k] = invariant

    return invariants


def rocq_of_invariants(name, invariants):
    out = f"""Definition {name}_timing_invs (_ : store) (p : addr)"
  (base_mem : addr -> N) (t : trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
"""
    for k, v in dict(sorted(invariants.items())).items():
        out += f"  | {hex(k)} => Some ({v})\n"
    out += """  | _ => None
  end
| _ => None
end."""

    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        "time_of_riscv_function.py", description="pretty print parsed json file"
    )
    parser.add_argument("bin")
    parser.add_argument("--riscv_objdump", default="riscv32-unknown-linux-gnu-objdump")
    parser.add_argument("--function_name", default="")
    parser.add_argument("--addr_offset", default=0, type=int)
    args = parser.parse_args()

    GHIDRA_ADDR_OFFSET = args.addr_offset

    # If preproc file doesn't exist, generate
    preproc_fn = f"{args.bin}.preprocessed.json"
    objdump_pass_fn = f"{args.bin}.preprocessed.objdump.json"
    if not os.path.exists(preproc_fn):
        result = subprocess.run(
            ["bash", "get_ghidra_basicblocks.sh", args.bin, preproc_fn],
            capture_output=True,
        )

        s = str(result.stdout)
        s = s[s.index("[") : s.rindex("]") + 1]
        with open(preproc_fn, "w") as file:
            json.dump(json.loads(s), file, indent=2)

    if not os.path.exists(objdump_pass_fn):
        # Run objdump pass
        from objdump_pass import objdump_pass

        class Object:
            pass

        objdump_args = Object()
        objdump_args.obj_bin = args.riscv_objdump
        objdump_args.binary = args.bin
        objdump_args.input_json = preproc_fn
        objdump_args.output_json = objdump_pass_fn
        objdump_pass(objdump_args, imported=True)

    with open(objdump_pass_fn, "r") as file:
        data = json.load(file)

    preprocess_data(data, args.function_name)
    # print(time_of_function_basic_blocks(data, args.function_name))
    invs = generate_timing_invariants(data, args.function_name)

    print(rocq_of_invariants(args.function_name, invs))

    blocks = (next(x for x in data if x["function_name"] == args.function_name))[
        "blocks"
    ]

    dom_tree, entry = compute_dominator_tree(blocks)
    draw_dominator_tree(dom_tree, blocks)
