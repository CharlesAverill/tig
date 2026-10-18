import sys
from tig.symbolic_execution import get_project
import json
from tig.bininfo import Function

with open("examples/RTOSDemo.elf.json", "r") as file:
    data = json.load(file)

if len(sys.argv) < 2:
    function_name = "vTaskSwitchContext"
    function_name = "xTimerIsTimerActive"
else:
    function_name = sys.argv[1]

base_addr = data[0]["blocks"][0]["bb_start_vaddr"]
p = get_project("examples/RTOSDemo.elf", base_addr)

func = Function([x for x in data if x["function_name"] == function_name][0])


def print_block_vex(block, insts):
    isrb = p.factory.block(block.start_vaddr).vex
    isrb.pp()
    if isrb.next:
        n_addr = isrb.next
        while n_addr in insts:
            isrb = p.factory.block(n_addr).vex
            isrb.pp()
            if isrb.next:
                n_addr = isrb.next
        
for block in func.blocks:
    print(block)
    print_block_vex(block, [i.offset for i in block.instructions])
