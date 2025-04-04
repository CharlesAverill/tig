import pypcode, archinfo, angr, claripy
from typing import List, Union, Optional, Any
from tig.bininfo import BasicBlock, Function
from enum import Enum
import logging

logging.getLogger("angr").setLevel(logging.ERROR)
logging.getLogger("claripy").setLevel(logging.ERROR)
logging.getLogger("pyvex").setLevel(logging.ERROR)
logging.getLogger("cle").setLevel(logging.ERROR)


def get_project(bin_path: str, lang: str = "RISCV:LE:32:default") -> angr.Project:
    """Get an angr Project using pypcode

    Args:
        bin_path (str): Path to binary of output Project
        lang (str, optional): SPARC identifier for assembly language.
                              See https://api.angr.io/projects/pypcode/en/latest/languages.html.
                              Defaults to "RISCV:LE:32:default".

    Raises:
        Exception: If SPARC identifier is unsupported by pypcode

    Returns:
        angr.Project: Project object for provided binary
    """
    sparc_lang = None
    for arch in pypcode.Arch.enumerate():
        for l in arch.languages:
            if l.id == lang:
                sparc_lang = l
                break
        if sparc_lang is not None:
            break
    if sparc_lang is None:
        raise Exception(f"Unable to find SPARC language for {lang}")

    pcode_arch = archinfo.ArchPcode(sparc_lang)

    return angr.Project(bin_path, arch=pcode_arch, auto_load_libs=False)


class ConstraintType(Enum):
    Unknown = 0
    BranchTrue = 1
    BranchFalse = 2
    DeadEnd = 3
    Unconstrained = 4


class Constraint:
    def __init__(
        self,
        t: ConstraintType,
        constraints: Union[claripy.ast.bool.Bool, List[claripy.ast.bool.Bool]],
        next_addr: Optional[int],
    ):
        self.type = t
        self.constraints: List[claripy.ast.bool.Bool] = [
            b
            for b in (
                [constraints]
                if type(constraints) == claripy.ast.bool.Bool
                else constraints
            )
            if not b.is_true()
        ]
        self.next_addr = next_addr

    def add_constraints(self, l: List[claripy.ast.bool.Bool]):
        self.constraints += l

    def __repr__(self):
        return f"Constraints ({self.type}) -> {self.next_addr}: {self.constraints}"


def solve_opt(state: angr.SimState, to_solve: str, default: Any) -> Any:
    """Try solving for a value, and return a default if an error occurs

    Args:
        state (angr.SimState): State to solve in
        to_solve (str): State attribute to solve
        default (Any): Default value to return in case of error

    Returns:
        Any: Default value if an error has occurred
    """
    try:
        return state.solver.eval(getattr(state, to_solve))
    except:
        return default


def reg_constraints(
    state: angr.SimState, bb: BasicBlock
) -> List[claripy.ast.bool.Bool]:
    regs_written = set()
    for i in bb:
        regs_written |= set(i.regs_written)

    out = []
    for reg in regs_written:
        reg = getattr(state.regs, reg)
        min, max = state.solver.min(reg), state.solver.max(reg)

        if min == max:
            out.append(reg == min)
        else:
            out.append(min <= reg)
            if max < 2**32:
                out.append(reg < max)
    return [x for x in out if not x.is_true()]


class StashMonitor(angr.exploration_techniques.ExplorationTechnique):
    """Exploration technique that prints stashes before and after each step"""

    def __init__(self, verbose=True):
        super().__init__()
        self.verbose = verbose

    def step(self, simgr, stash="active", **kwargs):
        # Print pre-step information
        if self.verbose:
            print("\nBefore step:")
            self._print_stashes(simgr)

        # Execute the step
        simgr = simgr.step(stash=stash, **kwargs)

        # Print post-step information
        if self.verbose:
            print("\nAfter step:")
            self._print_stashes(simgr)

        return simgr

    def _print_stashes(self, simgr):
        for stash_name, states in simgr.stashes.items():
            if states:
                print(f"{stash_name} ({len(states)}): [", end="")
                for s in states:
                    try:
                        print(f"{hex(s.addr)},", end="")
                    except:
                        print("<symbolic>,", end="")
                print("]")


def make_static_memory_symbolic(
    project: angr.Project, state: angr.SimState, chunk_size: int = 4
):
    """Overwrite .data and .bss sections with symbolic values

    Args:
        project (angr.Project): Project for target binary
        state (angr.SimState): State to write into
        chunk_size (int, optional): Size in bytes of symbolic chunks. Defaults to 4.
    """
    # Get section information
    data_section = project.loader.main_object.sections_map[".data"]
    bss_section = project.loader.main_object.sections_map[".bss"]

    # Process .data section
    for addr in range(data_section.min_addr, data_section.max_addr, chunk_size):
        sym_name = f"data_{hex(addr)}"
        symbolic_value = state.solver.BVS(sym_name, chunk_size * 8)
        state.memory.store(addr, symbolic_value)

    # Process .bss section
    for addr in range(bss_section.min_addr, bss_section.max_addr, chunk_size):
        sym_name = f"bss_{hex(addr)}"
        symbolic_value = state.solver.BVS(sym_name, chunk_size * 8)
        state.memory.store(addr, symbolic_value)

    return state


def exec_func(p: angr.Project, func: Function) -> List[claripy.ast.bool.Bool]:
    """Symbolically executes a function and computes input constraints

    Args:
        p (angr.Project): Project for target binary
        func (Function): Function to run

    Returns:
        List[claripy.ast.bool.Bool]: Constraints corresponding to control-flow paths through the function
    """
    state: angr.SimState = p.factory.blank_state(addr=func.entry_point)
    state = make_static_memory_symbolic(p, state, chunk_size=4)

    def print_mem_write(state):
        print(
            "Write", state.inspect.mem_write_expr, "to", state.inspect.mem_write_address
        )

    def print_reg_write(state):
        reg_offset = state.inspect.reg_write_offset  # Get the register offset
        reg_name = state.arch.register_names.get(reg_offset, f"Unknown({reg_offset})")
        print("Write", state.inspect.reg_write_expr, "to", reg_name)

    state.inspect.b("mem_write", when=angr.BP_AFTER, action=print_mem_write)
    state.inspect.b("reg_write", when=angr.BP_AFTER, action=print_reg_write)

    sm = p.factory.simgr(state)

    regions = [(func.entry_point, ret) for ret in func.return_addrs]
    in_regions = lambda addr: any([e <= addr <= r for e, r in regions])
    cfg = p.analyses.CFGFast()
    f = cfg.kb.functions.function(name=func.name)
    if f is None:
        print("Can't find function", func.name)
        return []
    sm.use_technique(angr.exploration_techniques.LoopSeer(cfg=cfg, bound=5))
    sm.use_technique(StashMonitor())

    sm.explore(
        find=func.return_addrs,
        # avoid=(lambda s: not (in_regions(s.addr))), # change this eventually, we do want function calls but we want to step over them if possible
        num_find=100,
    )

    return [s.solver.constraints for s in sm.found]


def exec_bb(
    p: angr.Project, bb: BasicBlock, input_constraints: List[Constraint]
) -> List[Constraint]:
    """Symbolically execute a BasicBlock and retrieve its constraints

    Args:
        p (angr.Project): Project for targeted binary
        bb (BasicBlock): Block to execute

    Returns:
        List[Constraint]: List of constraints, annotated with their type
    """

    # Setup input state
    state = p.factory.blank_state(addr=bb.start_vaddr)
    for c in input_constraints:
        state.solver.add(c)

    # Setup breakpoints on memory and register writes
    state.inspect.b("mem_write", when=angr.BP_AFTER)
    state.inspect.b("reg_write", when=angr.BP_AFTER)

    sm = p.factory.simgr(state, save_unconstrained=True)

    sm.step()

    """
    out = []
    if len(sm.active) == 2:
        true_addr = solve_opt(sm.active[0], "addr", None)
        out.append(Constraint(ConstraintType.BranchTrue, sm.active[0].solver.constraints, true_addr))
        out[-1].add_constraints(reg_constraints(sm.active[0], bb))
        false_addr = solve_opt(sm.active[1], "addr", None)
        out.append(Constraint(ConstraintType.BranchFalse, sm.active[1].solver.constraints, false_addr))
        out[-1].add_constraints(reg_constraints(sm.active[1], bb))
    else:
        for s in sm.active:
            addr = solve_opt(s, "addr", None)
            for c in s.solver.constraints:
                out.append(Constraint(ConstraintType.Unknown, c, addr))
                out[-1].add_constraints(reg_constraints(s, bb))
    for s in sm.deadended:
        addr = solve_opt(s, "addr", None)
        for c in s.solver.constraints:
            out.append(Constraint(ConstraintType.DeadEnd, c, addr))
            out[-1].add_constraints(reg_constraints(s, bb))
    for s in sm.unconstrained:
        addr = solve_opt(s, "addr", None)
        for c in s.solver.constraints:
            out.append(Constraint(ConstraintType.Unconstrained, c, addr))
            out[-1].add_constraints(reg_constraints(s, bb))
    for s in sm.pruned + sm.unsat:
        addr = solve_opt(s, "addr", None)
        for c in s.solver.constraints:
            out.append(Constraint(ConstraintType.Unknown, c, addr))
            out[-1].add_constraints(reg_constraints(s, bb))

    # for i in range(len(out)):
    #     constraints = out[i].con
    #     if type(constraints) == list:
    #         out[i] = (out[i][0], [x for x in constraints if not x.is_true()])
    #     elif type(constraints) == claripy.ast.bool.Bool:
    #         out[i] = (out[i][0], ([constraints] if not constraints.is_true() else []))"
    """

    return []
