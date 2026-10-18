
# Program

```py
def func:
    if c1:
        A
        if c2:
            B
            inf_loop()
        else:
            C
    D
```

# Symbolic executions
```py
A->B->inf  ; [c1, c2]
A->C->D    ; [c1,!c2]
D          ; [!c1]
```

# Merged traces
```py
func()
- (c1)  True: A
   - (c2)  True: B, inf_loop()
   - (c2) False: C, D
- (c1) False: D
```


# Cycle counts (Post-condition)
```py
cycle = 
  (if (c1)
   then
     A_t
     + (if (c2)
        then
          B_t + time_inf
        else
          C_t + D_t
       )
   else
     D_t
  ).
```

B->inf is probably a `jal` instruction, check if exists in history, if not, inf_loop



# Invariants (TODO)
...
match t with (Addr a, s) :: t' => match a with
 | (starting addr) => Some (init mem & regs /\ no_overlap base_mem & regs /\ cycle_count_of_trace t' = 0) 
 | (??)            => Some (xxx /\ no_overlap base_mem & regs /\ ?? )  -> blocks where path merges. time -> everything acccumulated so far
 | (End of 'D')    => Some (cycle_count_of_trace t = time_of_func xxx )
| _ => None end | _ => None end.

Only looks at the existing traces -> discard inf/dont-care paths.
  -> **check all blockes in the traces if bing merging points**
Compute merges block -> to generate pre-condition

-> Partial-DFA
  - include if-constraint content only if it's a splitting point
  - fall through if not a splitting point


## Questions:
`xTimerIsTimerActive`
What to do if merging point is one of the ending points?
  -> can be ignored, since no more code after that?

Convert `reg_init_gp_22242_32 + 0xfffff880` to simplier rule
0xfffff880 -> picane notation "circled-plus/minus"
  (can be found in `vTaskSwitchContext`)
1. Some can be simplified by using options (e.g. `angr.options.SIMPLIFY_REGISTER_WRITES`)
2. Some are default negative integer in BVV will be converted to `0xff...`

Determine whether to use the notation can be a bit more tricky ?
(Probably can do the trick of enabling above option back and  overwrite `angr/storage/memory_mixins/simplification_mixin.py`)
Is it guarateed for all register arithmetics be modulated?
How about memory calculation?


## TODOS
Add missing instruction time (Trivial)
