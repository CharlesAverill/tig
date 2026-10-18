from tig.time_of_riscv_func import time_of_BasicBlock
from tig.bininfo import Instruction, BasicBlock, Function
from typing import Dict, Any, List, Tuple
from jinja2 import Environment, FileSystemLoader



class TimingTreeNode:
    def __init__(self, block, constraint_node=None):
        self.constraint_node = constraint_node      
        self.block = block

        self.child = None
        self.is_branching = False
        self.true_child = None
        self.false_child = None

        self.block_time = None
        self.true_time = None
        self.false_time = None

    def set_time(self, block_time, true_time, false_time) -> None:
        self.block_time = block_time
        self.true_time = true_time
        self.false_time = false_time

    def get_constraint_repr(self) -> str:
        if self.constraint_node is None:
            return ""
        return self.constraint_node.repr


def build_timing_tree(function, 
                      traces: List[List[int]], 
                      instruction_args: List[Dict],
                      constraint_nodes: List):
    """
        Combine all traces into a timing tree (made of TimingTreeNode).
        Each node corresponds to a BasicBlock, time info is calculated by time_of_BasicBlock.
        Args:
            - function: Function, used to get entrypoint & BasicBlock info, should be replacable
            - traces: List of traces, each trace is a list of block addresses
            - instruction_args: some instruction's time is affected by its arguments (e.g. clz)
                * collected during symbolic execution in SymMemPlugin
            - constraint_nodes: List of ConstraintNode, collected during symbolic execution in SymMemPlugin
    """
    # Assert that all traces start with function.entry_point
    for t in traces:
        if t[0] != function.entry_point:
            # ERROR
            raise ValueError(f"Traces not sync with Function Data")

    root_node = TimingTreeNode(function.blocks[0])
    for trace_id, trace in enumerate(traces[::-1],start=1):
        trace_id = - trace_id  # Reverse order for traces[::-1]
        cur_node = root_node
        prev_node = None
        for idx, block_addr in enumerate(trace):
            #if idx == 0:
            #    continue
            # Not initialized, create a new node

            # TODO: here
            if prev_node is not None:
                if prev_node.is_branching:
                    if block_addr == prev_node.constraint_node.true_jmp_target:
                        cur_node = prev_node.true_child
                    elif block_addr == prev_node.constraint_node.false_jmp_target:
                        cur_node = prev_node.false_child
                    else:
                        # ERROR
                        raise ValueError(f"Block address {hex(block_addr)} not found in constraint node {prev_node.constraint_node}")
                else:
                    cur_node = prev_node.child

            if cur_node.block_time is None:
                cur_block = function.get_block(block_addr)
                cur_trace = trace[:idx]
                cur_instr_args = instruction_args[trace_id]
                block_t, condition, true_t, false_t = time_of_BasicBlock(cur_block, 
                                                                         cur_trace, 
                                                                         cur_instr_args,
                                                                         traces)
                cur_node.set_time(block_t, true_t, false_t)
                if condition:
                    # Sync with constraint_node
                    # if not presented in constraint_node, failed
                    target_cn = None
                    for cn in constraint_nodes:
                        if trace[:idx+1] == cn.bbl_history:
                            target_cn = cn
                            break
                    if target_cn is not None :
                        cur_node.constraint_node = target_cn
                        cur_node.is_branching = True
                        # TODO: init here?
                        if target_cn.true_jmp_target:
                            cur_node.true_child = TimingTreeNode(function.get_block(target_cn.true_jmp_target))
                        if target_cn.false_jmp_target:
                            cur_node.false_child = TimingTreeNode(function.get_block(target_cn.false_jmp_target))
                    else:
                        # ERROR
                        h = "[, ]".join(f"{hex(addr)}" for addr in trace[:idx+1])
                        raise ValueError(f"Cannot find ConstraintNode for trace {h}")
                else:
                    if idx != len(trace) - 1:
                        cur_node.child = TimingTreeNode(function.get_block(trace[idx+1]))
            prev_node = cur_node

    return root_node


def _syn_branch_condition(node: TimingTreeNode, 
                          all_traces: List[List[int]],
                          cur_trace: List[int]=[],
                          formula: str="",
                          indent: str="",
                          findent: str="",
                          depth: int=0,
                          end_addr: int|None=None,
                          verbose: bool=False
                          )-> str:
    formula += f"\n{findent}+ (if {node.get_constraint_repr()}"

    if verbose:
        print(f"\n{indent}- True : ", end="")

    formula += f"\n{findent}  then"
    formula += f"\n{findent}    {node.true_time} + "
    if node.true_child:
        if end_addr is not None:
            true_time = partial_dfs_timing_tree(node.true_child, end_addr,
                                                cur_trace+[node.true_child.block.start_vaddr], 
                                                all_traces, depth + 2, verbose)
        else:
            true_time = dfs_timing_tree(node.true_child, 
                                        cur_trace+[node.true_child.block.start_vaddr], 
                                        all_traces, depth + 2)
    else:
        true_time = f"\n{findent}  time_inf"
    formula += f"{true_time}"

    if verbose:
        print(f"\n{indent}- False: ", end="")

    formula += f"\n{findent}  else"
    formula += f"\n{findent}    {node.false_time} + "
    if node.false_child:
        if end_addr is not None:
            false_time = partial_dfs_timing_tree(node.false_child, end_addr,
                                                 cur_trace+[node.false_child.block.start_vaddr], 
                                                 all_traces, depth + 2, verbose)
        else:
            false_time = dfs_timing_tree(node.false_child, 
                                         cur_trace+[node.false_child.block.start_vaddr], 
                                         all_traces, depth + 2, verbose)
    else:
        false_time = f"\n{findent}  time_inf"
    formula += f"{false_time}"
    formula += f"\n{findent}  )"
    return formula


def dfs_timing_tree(node: TimingTreeNode, 
                    cur_trace: List[int]=[], 
                    all_traces: List[List[int]]=[], 
                    depth: int=0,
                    verbose: bool=False):
    """
        DFA traversal of the timing tree to generate the formula.
        Args:
            - node: current TimingTreeNode
            - cur_trace: current trace (list of block addresses)
            - all_traces: all traces, to check if cur_trace reached the end of a trace
            - depth: current depth in the tree, used for formula indentation
            - verbose: whether to print debug info
    """
    if verbose:
        print(f"{node.block.start_vaddr:#x} ", end="")

    # NOTE: disable the indentation (not sure which has better readability)
    indent = "  " * depth 
    addr_indent = len("(* 0x80001234 *) ")
    addr_text = f"(* {node.block.start_vaddr:#x} *)"
    findent = indent + " " * addr_indent

    if not node.block_time:
        if verbose:
            print(f" xxx", end="")
        return f"\n{addr_text} {indent}time_inf"

    formula = f"\n{addr_text} {indent}{node.block_time}"

    if not (node.true_child or node.false_child or node.child):
        if cur_trace in all_traces:
            if verbose:
                print(" <END>", end="")
            return formula
        else:
            if verbose:
                print(" xxx", end="")
            return formula + " + time_inf"

    if node.is_branching:
        formula = _syn_branch_condition(node, all_traces, cur_trace, 
                                        formula, indent, findent, depth, None, verbose)
    else:
        if node.child:
            child_time = dfs_timing_tree(node.child, cur_trace+[node.child.block.start_vaddr], 
                                         all_traces, depth, verbose)
            formula += f" +{child_time}"
    return formula


def partial_dfs_timing_tree(node: TimingTreeNode, 
                            end_addr: int,
                            cur_trace: List[int]=[], 
                            all_traces: List[List[int]]=[], 
                            depth: int=0,
                            verbose: bool=False):
    """
        DFA traversal of the timing tree to generate the formula.
        Args:
            - node: current TimingTreeNode
            - end_addr: address of the block where to stop the traversal
            - cur_trace: current trace (list of block addresses)
            - all_traces: all traces, to check if cur_trace reached the end of a trace
            - depth: current depth in the tree, used for formula indentation
            - verbose: whether to print debug info
    """
    if verbose:
        print(f"{node.block.start_vaddr:#x} ", end="")

    # Don't need to include this block as we've reached computing pre-conditions
    if end_addr == node.block.start_vaddr:
        if verbose:
            print(" <REACH>", end="")
        return "0" 

    # NOTE: disable the indentation (not sure which has better readability)
    indent = "  " * depth 
    addr_indent = len("(* 0x80001234 *) ")
    addr_text = f"(* {node.block.start_vaddr:#x} *)"
    findent = indent + " " * addr_indent

    formula = f"\n{addr_text} {indent}{node.block_time}"

    if not (node.true_child or node.false_child or node.child):
        raise ValueError("Preempted traces, should not reach here")

    if node.is_branching:
        # Check if we need to include branch condition
        cur_trace_len = len(cur_trace)
        next_addrs = set([t[cur_trace_len] for t in all_traces if len(t) > cur_trace_len])
        if not len(next_addrs):
            raise ValueError("Preempted traces, should have more nodes")

        if len(next_addrs) > 1:
            # Need to include branch condition
            formula = _syn_branch_condition(node, all_traces, cur_trace, 
                                            formula, indent, findent, depth, end_addr, verbose)
        else:
            # Check if it's the false or true branch
            next_addr = next_addrs.pop()
            if next_addr == node.constraint_node.true_jmp_target:
                trans_time = node.true_time
                next_node = node.true_child
                msg = "Only-true"
            elif next_addr == node.constraint_node.false_jmp_target:
                trans_time = node.false_time
                next_node = node.false_child
                msg = "Only-false"
            else:
                history = ", ".join(f"{hex(addr)}" for addr in node.constraint_node.bbl_history)
                raise ValueError(f"Preempted traces, {next_addr} not found in constraint node {history}")

            if verbose:
                print(f"\n{indent}- {msg} ", end="")
            formula += " + " + f"\n{findent}  {trans_time} + "
            formula += partial_dfs_timing_tree(next_node, end_addr, 
                                               cur_trace+[next_addr], all_traces, depth, verbose)
    else:
        if node.child:
            child_time = partial_dfs_timing_tree(node.child, end_addr, 
                                                 cur_trace+[node.child.block.start_vaddr], 
                                                 all_traces, depth, verbose)
            formula += f" + {child_time}"
    return formula


"""
    ###########################################################################
"""

#def _gen_reg_args(sym_info: Dict[str, Any]) -> Tuple[List[str], List[str], List[str]]:
#    params = []
#    variables = []
#    regs = []
#    for reg in sym_info["registers"]:
#        #for v in sym_info["variables"].keys():
#        #    if v.startswith(f"reg_init_{reg.lower()}"):
#        #        params.append(f"({v} : N)\t(* {reg} *)")
#        #        regs.append(reg.lower())
#        #        variables.append(v)
#    return params, variables, regs

def _gen_reg_args(sym_info: Dict[str, Any]) -> List[str]:
    return [f"({reg} : N)" for reg in sym_info["registers"].keys()]


def _gen_reg_invariant_comps(sym_info: Dict[str, Any]) -> Dict[str, str]:
    reg_invs = {}
    for reg in sym_info["registers"]:
        cap_reg = reg.upper()
        reg_invs[cap_reg] = f"s R_{cap_reg} = Ⓓ{reg}"
    return reg_invs


def _has_mem_ref(sym_info: Dict[str, Any],
                 sym_traces: List[Dict]) -> bool:
    return any(len(t["memory_regions"]) > 0 for t in sym_traces) \
            and len(sym_info["branch_constraints"]) > 0


def gen_proof_postcondition(target_name: str,
                            entry_point: int, 
                            timetree_root: TimingTreeNode,
                            sym_info: Dict[str, Any],
                            sym_traces: List[Dict], 
                            verbose: bool=False) -> str:

    if verbose:
        print(f"+++ Timing tree for {target_name} +++")
        print("-- Guard tree")

    has_mem_ref = _has_mem_ref(sym_info, sym_traces)
    if has_mem_ref > 0:
        mem_param = "    (mem : addr -> N)\n"
    else:
        mem_param = ""

    param_regs = _gen_reg_args(sym_info)

    formula = dfs_timing_tree(timetree_root, [entry_point], 
                              [t["bb_history"] for t in sym_traces], 1, verbose)

    time_of  = f"Definition time_of_{target_name} (t : trace)\n"
    time_of += mem_param
    time_of += "    " + "\n    ".join(param_regs) + "\n" if param_regs and has_mem_ref else ""
    time_of += "  : Prop :=\n"
    time_of += f"    cycle_count_of_trace t ="
    time_of += formula
    time_of += "."
    if verbose:
        print("\n\n-- Formula:\n")
        print(time_of)
        print()
    return time_of


def gen_proof_memory_regions(sym_info: Dict[str, Any],
                             sym_traces: List[Dict],
                             verbose: bool=False) -> str:
    memory_regions = set()
    for t in sym_traces:
        for m in t["memory_regions"]:
            memory_regions.add((m))

    param_regs = _gen_reg_args(sym_info)
    has_mem_ref = _has_mem_ref(sym_info, sym_traces)

    text  = "Definition memory_regions\n"
    text += "    (mem : addr -> N)\n" 
    text += "    " + "\n    ".join(param_regs) + "\n" if param_regs and has_mem_ref else ""
    text += "    := map (fun x => (4, x)) [\n"
    text += "\t\t" + ";\n\t\t".join(memory_regions)
    text += "\n"
    text += "      ].\n\n"
    text += "Definition noverlaps\n"
    text += "    (mem : addr -> N)\n" 
    text += "    " + "\n    ".join(param_regs) + "\n" if param_regs and has_mem_ref else ""
    text += f"    :=  create_noverlaps (memory_regions mem {' '.join(sym_info['registers'].keys())})."

    return text


def gen_proof_invariants(target_name: str,
                         entry_point: int, 
                         end_addrs_str: str,
                         timetree_root: TimingTreeNode,
                         sym_info: Dict[str, Any],
                         sym_traces: List[Dict], 
                         verbose: bool=False):
    if verbose:
        print(f"+++ Partial timing tree for {target_name} +++")

    # Determine merging points
    covered_blocks = set(sym_traces[0]["bb_history"])
    merge_points = set()
    for t in sym_traces[1:]:
        has_split = False
        for b in t["bb_history"]:
            if not has_split:
                if b in covered_blocks:
                    continue
                else:
                    has_split = True
            else:
                if b in covered_blocks:
                    merge_points.add(b) 
                    has_split = False
            covered_blocks.add(b)

    if verbose:
        for t in sym_traces:
            print([hex(b) for b in t["bb_history"]])
        print(f"Merge points: {[hex(mp) for mp in merge_points]}")

    # Generate invariant for each merging point
    invariants = {}
    for merge_point in merge_points:
        if verbose:
            print(f"\n=== Invariant for block {hex(merge_point)} ===")

        formula = partial_dfs_timing_tree(timetree_root, merge_point, [entry_point], 
                                         [t["bb_history"] for t in sym_traces \
                                                 if merge_point in t["bb_history"]], 
                                          1, verbose)
        # Increase padding
        formula = "\n".join("  " + line for line in formula.split("\n"))
        invariants[merge_point] = formula

    # Start proof generation
    param_regs = _gen_reg_args(sym_info)
    var_regs = list(sym_info["registers"].keys())
    reg_invs = _gen_reg_invariant_comps(sym_info)

    has_mem_ref = _has_mem_ref(sym_info, sym_traces)
    if has_mem_ref:
        mem_param = "(mem : addr -> N)\n"
    else:
        mem_param = ""

    if has_mem_ref:
        no_overlaps_cond = f"noverlaps mem " + " ".join(var_regs)
    else:
        no_overlaps_cond = ""

    def _gen_entry():
        s  = f"| {hex(entry_point)} => Some ("
        if has_mem_ref:
            s +=  " /\\\n\t\t\t".join(reg_invs.values()) + " /\\\n\t\t\t" if reg_invs else ""
            s +=  "s V_MEM32 = Ⓜmem /\\\n"
            s += f"\t\t\t{no_overlaps_cond} /\\\n\t\t\t"
        s +=  "cycle_count_of_trace t' = 0"
        s +=  ")\n"
        return s
    def _gen_merge_points():
        s = ""
        for mp in merge_points:
            s += f"| {hex(mp)} => Some ("
            s +=  "exists mem, s V_MEM32 = Ⓜmem /\\\n" if has_mem_ref else ""
            s += f"\t\t\t{no_overlaps_cond} /\\\n" if has_mem_ref else ""
            s +=  "\t\t\tcycle_count_of_trace t' = "
            s += invariants[mp] + "\n\t\t)\n"
        return s
    def _gen_ending():
        s  = f"{end_addrs_str} => Some ("
        s +=  "exists mem, s V_MEM32 = Ⓜmem /\\\n" if has_mem_ref else ""
        s +=  "\t\t\t" if has_mem_ref else ""
        s += f"time_of_{target_name} t"
        s += " mem" if has_mem_ref else ""
        s += " " + " ".join(var_regs) if var_regs and has_mem_ref else ""
        s += ")\n"
        s += "| _ => None end | _ => None end\n"
        return s

    time_of  = f"Definition {target_name}_timing_invs \n"
    time_of += "    " + mem_param
    time_of += "    " + "\n    ".join(param_regs) + "\n" if param_regs and has_mem_ref else ""
    time_of += "    (t : trace) : option Prop :=\n"
    time_of += "match t with (Addr a, s) :: t' => match a with\n"
    time_of += _gen_entry()
    time_of += _gen_merge_points()
    time_of += _gen_ending()
    time_of += "."

    if verbose:
        print("\n\n-- Formula:\n")
        print(time_of)
        print()
    return time_of


def gen_proof_procedure(target_name: str,
                        sym_info: Dict[str, Any],
                        sym_traces: List[Dict], 
                        verbose: bool=False):
    regs = list(sym_info["registers"].keys())
    # NOTE: could use this but not necessary for now for simplicity
    # reg_invs = _gen_reg_invariant_comps(sym_info)
    has_mem_ref = _has_mem_ref(sym_info, sym_traces)

    s  = f"Theorem {target_name}_timing:\n"
    s +=  "  forall s t s' x'"
    s +=  " mem" if has_mem_ref else ""
    s +=  " " + " ".join(regs) if regs and has_mem_ref else "" 
    s +=  "\n"
    s +=  "    (ENTRY: startof t (x',s') = (Addr entry_addr, s))\n"
    s +=  "    (MDL: models rvtypctx s)\n"
    s +=  "    (NVL: create_noverlaps (memory_regions mem " + " ".join(regs) + "))\n" if has_mem_ref else ""
    s +=  "    (MEM: s V_MEM32 = Ⓜmem)" if has_mem_ref else ""
    s +=  "\n" + "\n".join(f"    ({r.upper()}: s R_{r.upper()} = Ⓓ{r})" for r in regs) if regs and has_mem_ref else ""
    s +=  ",\n"
    s +=  "  satisfies_all\n"
    s += f"    lifted_{target_name}\n"
    s += f"    ({target_name}_timing_invs"
    s +=  " mem" if has_mem_ref else ""
    s +=  " " + " ".join(regs) if regs and has_mem_ref else ""
    s += ")\n"
    s += "    exits\n ((x',s')::t).\n"
    s += "Proof using.\n"
    s += "  (* TODO *)\n  Admitted.\n"
    s += "Qed.\n"

    return s


"""
         (NVL : create_noverlaps (memory_regions base_mem a0))
    ###########################################################################
"""


def synthesize_noverlaps_proof(function: Function,
                               sym_info: Dict[str, Any],
                               sym_traces: List[Dict], 
                               verbose: bool=False
                              )-> str:
    entry_addr = hex(function.entry_point)
    end_addrs = []
    for t in sym_traces:
        instr = function.get_block(t["bb_history"][-1]).instructions[-1].offset
        if instr not in end_addrs:
            end_addrs.append(instr) 
    end_addrs_str = "| " + " | ".join(hex(addr) for addr in end_addrs)

    root = build_timing_tree(function, 
                             [t["bb_history"] for t in sym_traces], 
                             [t["instruction_args"] for t in sym_traces], 
                             sym_info["branch_constraints"])

    postcondition = gen_proof_postcondition(function.name, function.entry_point,
                                               root, sym_info, sym_traces, verbose=verbose)

    if _has_mem_ref(sym_info, sym_traces):
        memory_regions = gen_proof_memory_regions(sym_info, sym_traces, verbose=verbose)
    else:
        memory_regions = ""

    invariants = gen_proof_invariants(function.name, function.entry_point, end_addrs_str,
                                               root, sym_info, sym_traces, verbose)

    proof = gen_proof_procedure(function.name, sym_info, sym_traces, verbose)

    # Loading Jinja modules and templates
    jinja_env = Environment(loader=FileSystemLoader("tig/jinja_templates"))
    noverlaps_temp = jinja_env.get_template("noverlaps.template.v")

    return noverlaps_temp.render(
        func_name=function.name,
        entry_addr=entry_addr,
        end_addrs=end_addrs_str,
        postcondition=postcondition,
        memory_regions=memory_regions,
        invariants=invariants,
        proof=proof,
    )


