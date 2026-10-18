from typing import Dict, Any, List


class Instruction:
    """Contains information about individual machine instructions pulled from Ghidra"""

    def __init__(self, data: Dict[str, Any]):
        self.offset: int = data["instr_offset"]
        self.size: int = data["instr_size"]
        self.mnem: str = data["mnem"]
        self.operands: List[str] = data["operands"]
        self.regs_read: List[str] = data["regs_read"]
        self.regs_written: List[str] = data["regs_written"]
        self.results: str = data["results"]
        self.instr_str: str = data["instruction_str"]
        self.instr_byte: str = data["instruction_byte"]
        self.is_big_endian: bool = data["is_big_endian"] == "true"

    def __repr__(self):
        return f"{hex(self.offset)}: {self.instr_str} (0x{self.instr_byte})"

    def __str__(self):
        return self.__repr__()


class BasicBlock(list):
    """A sequence of Instructions"""

    def __init__(self, data: Dict[str, Any]):
        self.start_vaddr: int = data["bb_start_vaddr"]
        self.size: int = data["bb_size"]
        self.is_exit_point: bool = data["is_exit_point"]
        self.exit_vaddrs: List[int] = data["exit_vaddrs"]
        self.is_entry_point: bool = data["is_entry_point"]
        self.source_vaddrs: List[int] = data["source_vaddrs"]
        self.instr_mode: str = data["instr_mode"]
        self.instructions: List[Instruction] = [
            Instruction(instr) for instr in data["instructions"]
        ]

        self.branches: bool = len(self.exit_vaddrs) > 1

    def __iter__(self):
        return iter(self.instructions)

    def __getitem__(self, idx):
        return self.instructions[idx]

    def __repr__(self):
        return f"====={hex(self.start_vaddr)}=====\n" + "\n".join(
            [str(i) for i in self.instructions]
        )

    def __str__(self):
        return self.__repr__()


class Function(list):
    """A sequence of BasicBlocks"""

    def __init__(self, data: Dict[str, Any]):
        self.name: str = data["function_name"]
        self.blocks: List[BasicBlock] = [BasicBlock(block) for block in data["blocks"]]
        self.block_dict: Dict[int, BasicBlock] = {b.start_vaddr: b for b in self.blocks}
        self.instructions: Dict[int, Instruction] = {i.offset: i for b in self.blocks for i in b.instructions}

    @property
    def entry_point(self) -> int:
        return self.blocks[0].start_vaddr

    @property
    def return_addrs(self) -> List[int]:
        return [block[-1].offset for block in self.blocks if block.is_exit_point]

    def get_block(self, vaddr: int) -> BasicBlock | None:
        return self.block_dict.get(vaddr, None)

    def get_instruction(self, offset: int) -> Instruction | None:
        return self.instructions.get(offset, None)

    def __repr__(self):
        out = f"<{self.name}>\n"
        for block in self.blocks:
            out += f"{block}\n"
        return out

    def __getitem__(self, idx):
        return self.blocks[idx]

    def __iter__(self):
        return iter(self.blocks)

    def __str__(self):
        return self.__repr__()
