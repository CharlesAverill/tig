"""Compare TIG's per-instruction Cloq timing terms with a hand proof's.

x86 proofs list `| 0xREL => name` per address in their time_of_addr; this checks
that TIG's operand-form classifier assigns the same names.

    python eval/compare_times.py DUMP.json HAND_PROOF.v
"""
import json
import re
import sys

dump = json.load(open(sys.argv[1]))
src = open(sys.argv[2]).read()
body = re.search(r"Definition time_of_addr.*?end\.", src, re.S).group(0)
hand = {hex(int(a, 16)): n for a, n in re.findall(r"\|\s*(0x[0-9a-fA-F]+)\s*=>\s*(\w+)", body)}
ok = bad = 0
for a, n in sorted(hand.items(), key=lambda x: int(x[0], 16)):
    t = dump.get(a)
    got = t[0] if isinstance(t, list) else t
    if got == n:
        ok += 1
    else:
        bad += 1
        print(f"  {a}: hand={n} tig={got}  ({dump.get(a + '_asm')})")
print(f"{ok}/{ok + bad} addresses agree")
