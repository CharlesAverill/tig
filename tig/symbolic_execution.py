import pypcode, archinfo, angr, claripy
from typing import List, Dict
from tig.bininfo import Function
import logging

logging.getLogger("angr").setLevel(logging.ERROR)
logging.getLogger("ailment").setLevel(logging.ERROR)
logging.getLogger("claripy").setLevel(logging.ERROR)
logging.getLogger("pyvex").setLevel(logging.ERROR)
logging.getLogger("cle").setLevel(logging.ERROR)

# NOTE: Customize CLZ, SimStatePlugin (and legacy memory overwrite)
import tig.memory_mixins



def get_project(bin_path: str, 
                base_addr: int,
                lang: str = "RISCV:LE:32:default") -> angr.Project:
    """vGet an angr Project using pypcode

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

    main_opts = {} if base_addr is None else {'base_addr': base_addr}
    return angr.Project(bin_path, 
                        arch=pcode_arch, 
                        load_options={'auto_load_libs': False, 
                                      'main_opts': main_opts
                                      }
                        )


class StashMonitor(angr.exploration_techniques.ExplorationTechnique):
    """ Exploration technique that prints stashes before and after each step 

    Usage:
        sm = p.factory.simgr(state)
        sm.use_technique(StashMonitor(verbose=verbose))
    """

    def __init__(self, verbose=True):
        super().__init__()
        self.verbose = verbose

    def step(self, simgr, stash="active", **kwargs):
        # Print pre-step information
        #if self.verbose:
        #    print("\nBefore step:")
        #    self._print_stashes(simgr)

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
    """ Overwrite .data and .bss sections with symbolic values

    Args:
        project (angr.Project): Project for target binary
        state (angr.SimState): State to write into
        chunk_size (int, optional): Size in bytes of symbolic chunks. Defaults to 4.
    Note: the naming convention is used in .tig.memory_mixins
    """
    # Get section information
    sections = project.loader.main_object.sections_map
    data_section = sections.get(".data")
    bss_section = sections.get(".bss")

    # Process .data section
    for addr in (range(data_section.min_addr, data_section.max_addr, chunk_size) if data_section else []):
        sym_name = f"data_init_{hex(addr)}"
        symbolic_value = state.solver.BVS(sym_name, chunk_size * 8)
        # NOTE: Reverse for little-endian
        state.memory.store(addr, symbolic_value.reversed)

    # Process .bss section
    for addr in (range(bss_section.min_addr, bss_section.max_addr, chunk_size) if bss_section else []):
        sym_name = f"bss_init_{hex(addr)}"
        symbolic_value = state.solver.BVS(sym_name, chunk_size * 8)
        # NOTE: Reverse for little-endian
        state.memory.store(addr, symbolic_value.reversed)


def make_registers_symbolic(
    project: angr.Project, state: angr.SimState, reg_size: int = 8
):
    # NOTE: This is currently not used
    """ Overwrite .data and .bss sections with symbolic values

    Args:
        project (angr.Project): Project for target binary
        state (angr.SimState): State to write into
        reg_size (int, optional): Size in bytes of symbolic registers. Defaults to 8
    Note: the naming convention is used in .tig.memory_mixins
    """
    import re
    arch = project.arch
    # make registers symbolic: sp, ra, gp; a0...a?, s0...s?
    init_regs = []
    for reg_name in arch.registers:
        if not (re.match(r"(a|s)\d+", reg_name) or reg_name in ["sp", "ra", "gp"]):
            continue
        _, size_bytes = arch.registers[reg_name]
        size_bits = size_bytes * reg_size

        sym_val = claripy.BVS(f"reg_init_{reg_name}", size_bits)
        # Write symbolic value to register
        state.registers.store(reg_name, sym_val)
        init_regs.append(reg_name)
    return init_regs


class NonTermAvoid(angr.exploration_techniques.ExplorationTechnique):
    """ Directly remove a state if calling non-terminated functions 

    Usage:
        sm = p.factory.simgr(state)
        sm.use_technique(NonTermAvoid(non_term_funcs, verbose=verbose))
    """

    def __init__(self, non_term_funcs=[], verbose=True):
        super().__init__()
        self.verbose = verbose
        self.non_term_funcs = non_term_funcs


    def step(self, simgr, stash="active", **kwargs):
        # Execute the step
        simgr = simgr.step(stash=stash, **kwargs)

        for state in simgr.stashes.get(stash, []):
            self._attach_hook(state)

        simgr.move(
            from_stash=stash,
            to_stash='avoid',
            filter_func=lambda s: s.globals.get('move_to_avoid', False)
        )

        return simgr
    
    def _attach_hook(self, state):
        if state.globals.get('hook_attached'):
            return
        state.globals['hook_attached'] = True

        def check_calling_non_term(state):
            addr = state.solver.eval(state.inspect.function_address)
            if addr in self.non_term_funcs:
                if self.verbose:
                    print(" ++ killing", hex(addr))
                state.globals['move_to_avoid'] = True

        state.inspect.b("call", when=angr.BP_BEFORE, action=check_calling_non_term)


def hook_symmem(state: angr.SimState, func: Function, verbose: bool = False,
                state_args=None, snapshots=None) -> None:
    """ Hook tig.memory_mixins.SymMemPlugin operations """
    state.register_plugin('sym_mem', tig.memory_mixins.SymMemPlugin())

    # Mapping 
    def symmem_add(state):
        var_name = state.inspect.symbolic_name
        if verbose:
            print(" + NEW", var_name)
        if var_name.startswith("reg_"):
            reg_name = var_name.replace("reg_", "").split("_")[0]
            size = int(var_name.rsplit("_")[-1]) // 8
            if reg_name not in state.arch.register_names:
                state.get_plugin("sym_mem").register_references[reg_name] = [var_name]
            else:
                state.get_plugin("sym_mem").register_references[reg_name].append(var_name)
            state.get_plugin("sym_mem").symbolic_references[var_name] = (reg_name, size)
        else:
            state.get_plugin("sym_mem").symbolic_references[var_name] = None

    def symmem_mem_read(state):
        f = state.get_plugin("sym_mem").record_memory_read
        length = state.inspect.mem_read_length
        repr = f(state.inspect.instruction, 
                 state.inspect.mem_read_address, 
                 state.inspect.mem_read_expr,
                 length)
        if verbose:
            print( " MEM Read", state.inspect.mem_read_expr, "from:", repr)
            print(f"          length: {length} bytes;", f"&({state.inspect.mem_read_address})")

    def symmem_mem_write(state):
        f = state.get_plugin("sym_mem").record_memory_write
        length = state.inspect.mem_write_length
        repr = f(state.inspect.instruction, state.inspect.mem_write_address)
        if verbose:
            print( " MEM Write", state.inspect.mem_write_expr, "to:", repr)
            print(f"          length: {length} bytes;", f"&({state.inspect.mem_write_address})")

    def skip_memory_constraints(state):
        state.inspect.address_concretization_add_constraints = False
        # NOTE: Don't check memory constraints for symbolic addresses
        #if verbose:
        #    c = str(state.inspect.address_concretization_expr)
        #    if len(c) > 20:
        #        c = c[:20] + "..."
        #    print("   Skip adding:", c)

    def symmem_path_constraint(state):
        instr = func.get_instruction(state.inspect.instruction)
        if instr is not None and instr.mnem.startswith("csr"):
            if verbose:
                print("  x Skip csr* constraints")
            return
        f = state.get_plugin("sym_mem").record_path_constraint
        repr = f(list(state.history.bbl_addrs), state.inspect.added_constraints)
        if repr is not None and verbose:
            if not repr.startswith(" (x Recorded)"):
                print(" Path constraint:", repr)
                print(f"                  ({state.inspect.added_constraints})")

    def symmem_reg_write(state):
        reg_offset = state.inspect.reg_write_offset  # Get the register offset
        reg_name = state.arch.register_names.get(reg_offset, f"Unknown({reg_offset})")
        length = state.inspect.reg_write_length
        if verbose:
            print(" REG Write", state.inspect.reg_write_expr, "to", reg_name, ", length:", length)
        # We may be extending a smaller value into a larger register, update symbolic_references accordingly
        # NOTE: see memory_mixins overwrite for limitations
        state.get_plugin("sym_mem").record_register_write(reg_name, state.inspect.reg_write_expr, verbose)
        # NOTE: instructions arguments may be handled here?

    def symmem_reg_read(state):
        reg_offset = state.inspect.reg_read_offset  # Get the register offset
        reg_name = state.arch.register_names.get(reg_offset, f"Unknown({reg_offset})")
        length = state.inspect.reg_read_length
        if verbose:
            print(" REG Read ", state.inspect.reg_read_expr, "from ", reg_name, ", length:", length)
        #state.get_plugin("sym_mem").record_register_read(reg_name, state.inspect.reg_read_expr, length)

        # NOTE: instructions arguments may be handled here?
        cur_instr = func.get_instruction(state.inspect.instruction)
        if cur_instr is None:
            return
        if cur_instr.mnem == "clz":
            # NOTE: recorde clz "read" arg for timing 
            f = state.get_plugin("sym_mem").record_instr_arg
            bbl_addrs = state.get_plugin("sym_mem").bbl_history
            f("clz", bbl_addrs, state.inspect.instruction, state.inspect.reg_read_expr, 1)

    def symmem_exit(state):
        jmp_target = state.inspect.exit_target
        guard = state.inspect.exit_guard
        instr = func.get_instruction(state.inspect.instruction)
        if instr is not None and instr.mnem.startswith("csr"):
            if verbose:
                print("*", hex(state.inspect.instruction), "->", hex(jmp_target), f"({state.inspect.exit_jumpkind})")
                print(" x Skip csr* Guard")
        else:
            f = state.get_plugin("sym_mem").record_branch_jump
            bbl_addrs = state.get_plugin("sym_mem").bbl_history
            cn = f(bbl_addrs, guard, jmp_target)
            if verbose:
                print("*", hex(state.inspect.instruction), "->", hex(jmp_target), f"({state.inspect.exit_jumpkind})")
                print(" Guard", cn)
        # NOTE: if the jump target is exactly the return address of the function, angr will
        #       stop and not include the return block in the history, manually add it here
        if jmp_target in func.block_dict.keys() and jmp_target in func.return_addrs:
            state.get_plugin("sym_mem").history[jmp_target] = []
            state.get_plugin("sym_mem").bbl_history.append(jmp_target)

    def record_addr(state):
        instr_addr = state.inspect.instruction
        instr = func.get_instruction(instr_addr)
        if verbose:
            if instr is not None:
                print("\n->", instr)
            else:
                print("\n->", hex(instr_addr), "??")
        if instr_addr in func.block_dict:
            state.get_plugin("sym_mem").bbl_history.append(instr_addr)
        # Cloq backend: capture the pre-instruction values of the registers that
        # this instruction's timing depends on (e.g. RISC-V sll/clz read rd).
        if state_args is not None and instr is not None:
            regs = state_args(instr)
            if regs:
                key = (tuple(state.get_plugin("sym_mem").bbl_history), instr_addr)
                vals = tuple(state.registers.load(r, inspect=False, disable_actions=True) for r in regs)
                state.globals["tig_state_args"] = {**state.globals.get("tig_state_args", {}), key: vals}
        # Cloq backend: snapshot the general-purpose registers at loop headers,
        # once per visit, to recover induction variables and loop-invariant values.
        if snapshots and instr_addr in snapshots[0]:
            key = tuple(state.get_plugin("sym_mem").bbl_history)
            vals = {r: state.registers.load(r, inspect=False, disable_actions=True) for r in snapshots[1]}
            state.globals["tig_snapshots"] = {**state.globals.get("tig_snapshots", {}), key: vals}
        # May be useful for fine-grained records?
        state.get_plugin("sym_mem").history[instr_addr] = []

    state.inspect.b("instruction", when=angr.BP_BEFORE, action=record_addr)
    state.inspect.b("symbolic_variable", when=angr.BP_AFTER, action=symmem_add)
    state.inspect.b("mem_read", when=angr.BP_AFTER, action=symmem_mem_read)
    state.inspect.b("mem_write", when=angr.BP_AFTER, action=symmem_mem_write)
    state.inspect.b('address_concretization', when=angr.BP_BEFORE, action=skip_memory_constraints)
    state.inspect.b("constraints", when=angr.BP_AFTER, action=symmem_path_constraint)
    state.inspect.b("exit", when=angr.BP_AFTER, action=symmem_exit)
    state.inspect.b("reg_read", when=angr.BP_AFTER, action=symmem_reg_read)
    state.inspect.b("reg_write", when=angr.BP_AFTER, action=symmem_reg_write)


def exec_func(p: angr.Project, 
              func: Function, 
              non_term_funcs: List[int], 
              verbose: bool = False,
              state_args=None,
              loop_bound: int = 5,
              snapshots=None,
              extra_exits=(),
              lazy_solves: bool = False) -> Dict:
    """Symbolically executes a function and computes input constraints

    Args:
        p (angr.Project): Project for target binary
        func (Function): Function to run
        non_term_funcs (List[int]): list of non-terminated function addresses
        verbose (bool): debug printing

    Returns:
        Dict[
            "results": List[], # info from each sym-exec path through the function
            "info":    Dict[]     # common information about all paths
        ]
    """
    # Reference: https://docs.angr.io/en/latest/appendix/options.html
    #  - angr.options.CONSERVATIVE_READ_STRATEGY sounds good but oddly useless
    state: angr.SimState = p.factory.blank_state(
        addr=func.entry_point,
        mode="symbolic",
        add_options={
            angr.options.CACHELESS_SOLVER,
            angr.options.AVOID_MULTIVALUED_READS, # This creates new symbolic value when dereferencing address with symbolic values
            angr.options.CALLLESS,
            angr.options.SYMBOLIC_INITIAL_VALUES,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY
        },
        remove_options={
            angr.options.SIMPLIFY_REGISTER_WRITES,
            angr.options.SIMPLIFY_MEMORY_WRITES,
            angr.options.SIMPLIFY_REGISTER_READS,
            # TODO: all of them??
            angr.options.SIMPLIFY_MEMORY_READS,
            angr.options.SIMPLIFY_CONSTRAINTS,
            angr.options.SIMPLIFY_EXIT_GUARD,
            angr.options.SIMPLIFY_EXPRS,
            }
    )

    state = make_static_memory_symbolic(p, state, chunk_size=4)

    state = make_registers_symbolic(p, state, chunk_size=4)

    # For debug printing
    if verbose:
        set_debug_inspect(state)
    
    # Create sym_mem as plugin so that it can be deep-copied when state forks
    class SymMapPlugin(angr.SimStatePlugin):
        def __init__(self, data=None, exprs=None):
            super().__init__()
            self.data = data or {}
            self.exprs = exprs or {}

        def copy(self, memo):
            return SymMapPlugin(copy.deepcopy(self.data), copy.deepcopy(self.exprs))

    state.register_plugin('sym_mem', SymMapPlugin())

    # Mapping 
    def symmem_add(state):
        state.get_plugin("sym_mem").data[state.inspect.symbolic_name] = []
        state.get_plugin("sym_mem").exprs[state.inspect.symbolic_name] = state.inspect.symbolic_expr

    def symmem_set(state):
        if len(state.inspect.mem_read_expr.args) == 2:
            arg0_name = state.inspect.mem_read_expr.args[0]
            if arg0_name in state.get_plugin("sym_mem").data:
                state.get_plugin("sym_mem").data[arg0_name].append((hex(state.inspect.instruction), copy.deepcopy(state.inspect.mem_read_address)))
                #if verbose:
                #    print(f"  - SYM_MEM: {arg0_name} -> {state.inspect.mem_read_address}" )

    state.inspect.b("symbolic_variable", when=angr.BP_AFTER, action=symmem_add)
    state.inspect.b("mem_read", when=angr.BP_AFTER, action=symmem_set)

    #state.memory.unconstrained_use_addr = True

    sm = p.factory.simgr(state)

    # Boundaries of the function
    regions = [(func.entry_point, ret) for ret in func.return_addrs]
    if verbose:
        print("Entry:", hex(func.entry_point))
        print("Regions:", [f"({hex(a)}, {hex(b)})" for a,b in regions])
        print()

    # A path stays inside the function iff it is in one of the function's
    # blocks.  (Comparing against [entry, return] wrongly discards blocks the
    # compiler places after the return instruction, e.g. outlined branches.)
    block_ranges = [(b.start_vaddr, b.start_vaddr + b.size) for b in func.blocks]
    in_regions = lambda addr: any(lo <= addr < hi for lo, hi in block_ranges)
    try:
        cfg = p.analyses.CFGFast()
        sm.use_technique(angr.exploration_techniques.LoopSeer(cfg=cfg, bound=loop_bound))
    except AttributeError:
        # angr's CFG recovery assumes its native ARM arch; for pcode ARM bound
        # paths by length instead (loops are still unrolled, then reported).
        sm.use_technique(angr.exploration_techniques.LengthLimiter(max_length=4 * loop_bound))
    # NonTermAvoid check and move states to avoid, must come first
    sm.use_technique(NonTermAvoid(non_term_funcs, verbose=verbose))
    sm.use_technique(StashMonitor(verbose=verbose))

    sm.explore(
        find=list(func.return_addrs) + list(extra_exits),
        # change this eventually, we do want function calls but we want to step over them if possible
        avoid=(lambda s: not (in_regions(s.addr))), 
        num_find=100,
    )
    # sm.step()

    def dedup_constraints(constraint_sets):
        out = []
        seen = set()
        for addr, c, sym_mem, exprs in constraint_sets:
            if str(c) not in seen:
                seen.add(repr(c))
                new_sym_mem = {}
                new_exprs = {}
                for sym, ptr in sym_mem.items():
                    if not ptr:
                        continue
                    # TODO: I believe we only need to keep the last update
                    #if len(ptr) > 1:
                    #    raise NotImplementedError("More than one sym mem mapping. Check!")
                    new_sym_mem[sym] = ptr[-1][1]
                for name,val in exprs.items():
                    if not name:
                        continue
                    new_exprs[name] = val
                out.append((addr, c, new_sym_mem, new_exprs))
        return out

    for s in sm.active + sm.found:
        s.solver.simplify()

    return dedup_constraints([(s.addr, 
                               s.solver.constraints, 
                               s.get_plugin("sym_mem").data, 
                               s.get_plugin("sym_mem").exprs ) for s in sm.found] )
