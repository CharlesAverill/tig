
""" Overwrite Pcode's clz handler """
from angr.engines.pcode.behavior import OpBehaviorLzcount
#from angr.state_plugins import history
from claripy.ast.bv import BV, BVS

orig_evaluate_unary = OpBehaviorLzcount.evaluate_unary

def sym_eval_lzcount(self, size_out: int, size_in: int, in1: BV) -> BV:
    extracted_expr,_ = in1.args
    return BVS("CLZ_{"+extracted_expr+"}", size_out * 8)

OpBehaviorLzcount.evaluate_unary = sym_eval_lzcount


""" Overwrite claripy BV's sign_extend and zero_extend """
# NOTE: this is probably called from angr/engines/pcode/emulate.py:_adjust_value_size
from claripy.ast.bv import ZeroExt, SignExt
orig_sext = BV.sign_extend
def sym_eval_sext(self: BV, extra_bits: int) -> BV:
    # TODO: can only handle single variable now
    if len(self.variables) == 1 and self.depth == 1:
        #print("+++++++++sext overwrite on", self, "with", extra_bits)
        extracted_expr,_ = self.args
        print("+++++++++sext overwrite on", extracted_expr, "with", extra_bits)
        if extracted_expr.startswith("CLZ"):
            # CLZ should not be handled
            return SignExt(extra_bits, self)
        return BVS(extracted_expr, self.size() + extra_bits)
    else:
        return SignExt(extra_bits, self)
BV.sign_extend = sym_eval_sext

orig_zext = BV.zero_extend
def sym_eval_zext(self: BV, extra_bits: int) -> BV:
    # TODO: can only handle single variable now
    if len(self.variables) == 1 and self.depth == 1:
        #print("+++++++++zext overwrite on ", self, "with", extra_bits)
        extracted_expr,_ = self.args
        print("+++++++++zext overwrite on", extracted_expr, "with", extra_bits)
        if extracted_expr.startswith("CLZ"):
            # CLZ should not be handled
            return ZeroExt(extra_bits, self)
        return BVS(extracted_expr, self.size() + extra_bits)
    else:
        return ZeroExt(extra_bits, self)
BV.zero_extend = sym_eval_zext


""" Object to support recursive memory ref """

# Create sym_mem as plugin so that it can be deep-copied when state forks
import re
from typing import List, Tuple
from copy import deepcopy
from angr import SimStatePlugin
from claripy.operations import infix, prefix


class ConstraintNode():
    """ Class to store brach conditions on a sym-exec path """
    def __init__(self, bbl_history: List[int], constraint: BV, repr: str, inv_repr: str):
        self.bbl_history = bbl_history
        self.bvv = constraint
        self.repr = repr
        self.inv_repr = inv_repr

        self.true_jmp_target = 0
        self.false_jmp_target = 0

    def add_jmp_target(self, target: int, branch: bool):
        if branch:
            self.true_jmp_target = target
        else:
            self.false_jmp_target = target

    def __repr__(self):
        #return "[" + ", ".join(f"{hex(addr)}" for addr in self.bbl_history) + "]:\n\t" + self.repr
        guard_str = self.repr
        if len(guard_str) > 150:
            guard_str = guard_str[:150] + "..."
        return f"  0x{self.bbl_history[-1]:x} => <0x{self.true_jmp_target:x}|0x{self.false_jmp_target:x}>:\n\t" + guard_str

    def __str__(self):
        #return "[" + ", ".join(f"{hex(addr)}" for addr in self.bbl_history) + "]: " + self.repr
        return f"  0x{self.bbl_history[-1]:x} => <0x{self.true_jmp_target:x}|0x{self.false_jmp_target:x}>: " + self.repr


class SymMemPlugin(SimStatePlugin):
    """ Plugin to track symbolic memory references, path constraints (and more!)

    Args:
        symbolic_references: { <symbolic_var:str>: (<symbolic_var:addr>, <length:int>) }
        path_constraints:    [ <path_constraint:str> ] 
        branch_constraints:  [ <branch_constraint:ConstraintNode> ]   # shared between states
        recorded_history:    [ <instr_addr:int> ]                     # shared between states
        variables:           [ <symbolic_var:str> }                   # shared between states,
        history:             { <instr_addr>: [<TODO_info>] }
        bbl_history:         [ <bbl_addr:int> ]
        instruction_args:    { <instr_mnem:str>: [(history:List[int], arg_repr:str, arg_idx:int)] }
        memory_regions:      { <symbolic_addr:str>: {"read":  [<instr_addr:int>],
                                                     "write": [<instr_addr:int>]
                                                    }
                             }
        register_references:           { reg_name: [symbolic_value_repr] }?

        - symbolic_references:  store the mapping of a symbolic address to its repr
        - path_constraints:     all constraints generated when sym-exec during each state
        - branch_constraints:   collected (adding T/F child) when branch condition is evaluated
        - recorded_history:     help tracking the creation of branch_constraints, each CN should be unique
        - variables:            this helps creating function parameters in proof synthesis
        - history:              updates in tig.symbolic_execution.hook_symmem.record_addr, useless for now
        - bbl_history:          track the basic block history of current state
        - instruction_args:     repr of symbolic arguments of instructions, used in proof synthesis
        - memory_regions:       tracks the usage of symbolic memory addresses, used in memory_no_overlap proof
        - registers_references: TODO: add comment 
                                    
    Functions:
    - get_repr(entry: BV) -> str
        * Get a string representation of a symbolic value (recursively dereferencing BV)

    - record_memory_read(instr_addr: int, symbolic_addr: BV, symbolic_value: BV) -> str
        * Updates `memory_regions`
        * Record a memory read for address <repr(symbolic_addr)> at <instr_addr> 
        * Map symbolic_references[symbolic_value: str] = <symbolic_addr: str>, <length: int> .
        * Hooked to state.inspect.b("mem_read")
        
    - record_write_read(instr_addr: int, symbolic_addr: BV, symbolic_value: BV) -> str
        * Updates `memory_regions`
        * Record a memory write to address <repr(symbolic_addr)> at <instr_addr> 
        * Hooked to state.inspect.b("mem_write")

    - get_constraint_reprs(constraints: List[BV])-> List[str]:
        * get_repr for list of BV constraints (from `s.solver.constraints`) 
        * useless for now

    - record_path_constraint(self, history:List[int], constraints: Tuple[BV])-> str | None
        * Record a constraint in `path_constraints` if it is not already present.
        * Hooked to state.inspect.b("constraints")

    - record_branch_jump(self, history:List[int], guard: BV, jmp_target: int)-> ConstraintNode | None
        * Construct a ConstraintNode with the given history and guard. 
        * Set up the jump target for the branch.
        * If the history is already recorded, it will add the jump target to the existing ConstraintNode.
        * Hooked to state.inspect.b("branch_jump")

    - record_instr_arg(self, instr:str, bb_history: List[int], addr:int, arg: BV, arg_idx: int)-> None
        * Record the symbolic argument of an instruction in `instruction_args`.
        * Each record is a tuple of (history, repr(arg), arg_idx).
        * The history is the [basic block history] + [instruction address]
        * Currently only implements `clz`
        * Hook target is based on VEX's implementation of each instruction

    """
    def __init__(self, 
                 symbolic_references={}, 
                 path_constraints=[],
                 branch_constraints=[],
                 recorded_history=[],
                 register_references={},
                 variables=[],
                 history={}, 
                 bbl_history=[],
                 instruction_args={},
                 memory_regions={},
                 mem_read_asts=None):
        super().__init__()
        self.mem_read_asts = {} if mem_read_asts is None else mem_read_asts
        self.symbolic_references = symbolic_references
        self.history = history
        self.bbl_history = bbl_history
        self.path_constraints = path_constraints
        self.branch_constraints = branch_constraints
        self.register_references = register_references
        self.variables = variables
        self.instruction_args = instruction_args
        self.recorded_history = recorded_history
        self.memory_regions = memory_regions


    def _add_variable(self, var: BV)-> None:
        for v in var.variables:
            if v not in self.variables and \
                v not in self.symbolic_references and \
                not v.startswith("CLZ"):
                # TODO: anything to do here?
                if not v.startswith("data_init") and not v.startswith("reg_"):
                    raise NotImplementedError(f"Symbolic variable {v} not expected in constraints")
                self.variables.append(v)

    def record_memory_read(self, instr_addr: int, symbolic_addr: BV, symbolic_value: BV, length: int)-> str:
        addr_repr = self.get_repr(symbolic_addr)
        if symbolic_value.depth == 1 and len(symbolic_value.variables) == 1:
            symbolic_name = list(symbolic_value.variables)[0]
            self.symbolic_references[symbolic_name] = (addr_repr, length)
            self.mem_read_asts[symbolic_name] = (symbolic_addr, length)
        if addr_repr not in self.memory_regions:
            self.memory_regions[addr_repr] = {"read":[instr_addr], "write":[]}
            self._add_variable(symbolic_value)
        else:
            self.memory_regions[addr_repr]["read"].append(instr_addr)
        return addr_repr

    def record_memory_write(self, instr_addr: int, symbolic_addr: BV)-> str:
        addr_repr = self.get_repr(symbolic_addr)
        if addr_repr not in self.memory_regions:
            self.memory_regions[addr_repr] = {"read":[], "write":[instr_addr]}
            self._add_variable(symbolic_addr)
        else:
            self.memory_regions[addr_repr]["write"].append(instr_addr)
        return addr_repr

    def record_register_read(self, reg_name: str, symbolic_value: BV, length: int):
        raise NotImplementedError()

    def record_register_write(self, reg_name: str, symbolic_value: BV, verbose=False):
        if not hasattr(symbolic_value, "depth"):
            return  # concrete write (pcode context registers on ARM)
        if symbolic_value.depth == 1 and len(symbolic_value.variables) == 1:
            symbolic_name = list(symbolic_value.variables)[0]
            if symbolic_name.startswith("CLZ"):
                # don't track CLZ result
                return
            if symbolic_name not in self.symbolic_references:
                old_name = symbolic_name.rsplit("_", 2)[0]
                if old_name not in self.symbolic_references:
                    return  # initial register copied before it was referenced
                self.symbolic_references[symbolic_name] = self.symbolic_references[old_name]
                if verbose:
                    print(f"  +++++ register write: {reg_name} = {symbolic_value} <- {old_name}")

    def copy(self, memo):
        return SymMemPlugin(deepcopy(self.symbolic_references),
                            deepcopy(self.path_constraints),
                            self.branch_constraints,
                            self.recorded_history,
                            deepcopy(self.register_references),
                            self.variables,
                            deepcopy(self.history),
                            deepcopy(self.bbl_history),
                            deepcopy(self.instruction_args),
                            deepcopy(self.memory_regions),
                            self.mem_read_asts)

    def get_repr(self, entry: BV)-> str:
        if isinstance(entry, int):
            return hex(entry)  # concrete address
        # The legacy printer handles few operators. The Cloq backend prints
        # from the ASTs, so do not abort symbolic execution here.
        try:
            value, negate = self._get_repr(entry)
        except (NotImplementedError, KeyError, ValueError, AttributeError):
            return f"<unprintable {getattr(entry, 'op', entry)}>"
        if negate:
            value = f"(- {value})"
        return value

    def _get_repr(self, entry: BV)-> Tuple[str, bool]:
        # Return <repr, to negate or not>
        def _deref(value: str, length: int)-> str:
            if length == 1:
                return f"mem Ⓑ[{value}]"
            elif length == 2:
                return f"mem Ⓦ[{value}]"
            elif length == 4:
                return f"mem Ⓓ[{value}]"
            else:
                raise NotImplementedError(f"Cannot deref memory of length {length}")
        if entry.depth > 1: 
            # Expand non-terminals
            if len(entry.args) > 1:
                if entry.op not in infix:
                    raise NotImplementedError(f"Cannot parse infix op {entry.op} in {entry}")
                if str(infix[entry.op]) == "==":
                    op = "=?"
                    negate = False
                elif str(infix[entry.op]) == "!=":
                    op = "=?"
                    negate = True
                else:
                    op = str(infix[entry.op])
                    negate = False
                full_repr = ""
                for arg in entry.args:
                    arg_repr, arg_negate = self._get_repr(arg)
                    if full_repr == "":
                        if arg_negate:
                            arg_repr = f"(- {arg_repr})"
                        else:
                            full_repr = arg_repr
                    else:
                        if op == "*":
                            op = "⊗"
                        if arg_negate:
                            if op == "+":
                                cur_op = "⊖"
                            elif op == "-":
                                cur_op = "⊕"
                            else:
                                cur_op = op
                                arg_repr = f"(- {arg_repr})"
                            full_repr = f"{full_repr} {cur_op} {arg_repr}"
                        else:
                            full_repr = f"{full_repr} {op} {arg_repr}"
                if negate:
                    full_repr = f"negb({full_repr})"
                return full_repr, False
            else:
                if entry.op not in prefix:
                    raise NotImplementedError(f"Cannot parse prefix op {entry.op} in {entry}")
                full_repr, negate = self._get_repr(entry.args[0])
                if negate: 
                    raise NotImplementedError(f"Cannot parse nested negation in {entry}")
                return f" {prefix[entry.op]} " + full_repr, negate
        else: 
            # Terminals
            value = entry.args[0]
            if type(value) == str:
                if value.startswith("reg_"):
                    return self.symbolic_references[value][0], False
                elif "CLZ" in value:
                    match_group = re.match(r"CLZ_{(.+)}.+", value)
                    if not match_group:
                        raise NotImplementedError(f"Cannot parse CLZ symbolic reference {value}")
                    clz_arg = match_group.group(1)
                    if clz_arg in self.symbolic_references:
                        content, length = self.symbolic_references[clz_arg]
                        return f"CLZ({_deref(content, length)})", False
                    else:
                        raise NotImplementedError(f"Cannot find symbolic reference for {clz_arg}")
                else:
                    content, length = self.symbolic_references[value]
                    return f"{_deref(content, length)}", False
            else:
                # should be a BVV, see if need to negate
                orig_hex = f"{value:x}"
                if orig_hex.startswith("f"):
                    return f"0x{(-entry).args[0]:x}", True
                else:
                    return f"0x{value:x}", False
        
    def get_constraint_reprs(self, constraints: List[BV])-> List[str]:
        return [self.get_repr(c) for c in constraints]

    def record_path_constraint(self, bbl_history:List[int], constraints: Tuple[BV])-> str | None:
        c = constraints[0] if len(constraints) == 1 else None
        if c is None:
            h = ", ".join(f"{hex(addr)}" for addr in bbl_history)
            raise ValueError(f"Expected a single constraint, got {len(constraints)}: {constraints} for trace {h}")

        # if no variable in c and eval to true, skip
        if len(c.variables) == 0 and c.is_true():
            return None
        
        self._add_variable(c)

        repr = self.get_repr(c)
        if repr not in self.path_constraints:
            self.path_constraints.append(repr)
            return repr
        else:
            return " (x Recorded) " + repr[:5] + "..."


    def record_branch_jump(self, 
                           bbl_history:List[int], 
                           guard: BV, 
                           jmp_target: int)-> ConstraintNode | None:
        # if no variable in c and eval to true, skip
        if len(guard.variables) == 0 and guard.is_true():
            return None
        
        self._add_variable(guard)

        repr = self.get_repr(guard)
        if repr not in self.path_constraints:
            self.path_constraints.append(repr)

        bbl_history = deepcopy(bbl_history)

        if bbl_history not in self.recorded_history:
            cn = ConstraintNode(bbl_history, guard, repr, self.get_repr(guard.__invert__()))
            cn.add_jmp_target(jmp_target, True)
            self.branch_constraints.append(cn)
            self.recorded_history.append(deepcopy(bbl_history))
            return cn
        else:
            target_cn = None
            for cn in self.branch_constraints:
                if bbl_history == cn.bbl_history:
                    target_cn = cn
                    break
            if target_cn is None :
                # ERROR
                h = ", ".join(f"{hex(addr)}" for addr in bbl_history)
                raise ValueError(f"Cannot find ConstraintNode for bbl_history {h}")

            if target_cn.inv_repr == repr:
                target_cn.add_jmp_target(jmp_target, False)
            else:
                # ERROR
                h = ", ".join(f"{hex(addr)}" for addr in bbl_history)
                raise NotImplementedError(f"ConstraintNode {repr} misbehave at bbl_history {h}")
        return target_cn

    def record_instr_arg(self, instr:str, bb_history: List[int], addr:int, arg: BV, arg_idx: int)-> None:
        history = bb_history + [addr]
        if instr not in self.instruction_args:
            self.instruction_args[instr] = []
        self.instruction_args[instr].append((history, self.get_repr(arg), arg_idx))
