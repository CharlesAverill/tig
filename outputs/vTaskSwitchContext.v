Require Import RTOSDemo_NoAsserts_Clz.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Variable ML : N.
Variable ML_pos : 1 <= ML.

Definition time_mem : N :=
    5 + (ML - 2).
Definition time_branch : N :=
    5 + (ML - 1).
Definition time_inf : N :=
    9999.

Definition err_time : N := 
    9999.

(* Common for all timing proofs - facilitates automation *)
Module vTaskSwitchContextTime <: TimingModule.
  Definition time_of_addr (s : store) (a : addr) : N :=
      match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
      | Some x => x | _ => 999 end.
  
  Definition entry_addr : N := 0x8000137c.
  
  Definition exits (t:trace) : bool :=
      match t with (Addr a,_)::_ => match a with
      | 0x8000138c | 0x8000144c => true
      | _ => false
    end | _ => false end.
End vTaskSwitchContextTime.
Module vTaskSwitchContextAuto := TimingAutomation vTaskSwitchContextTime.
Import vTaskSwitchContextTime vTaskSwitchContextAuto.


Definition CLZ (n : N) : N := clz(n) 32.


(* Postcondition *)
Definition time_of_vTaskSwitchContext (t : trace)
    (mem : addr -> N)
    (gp : N)
  : Prop :=
    cycle_count_of_trace t =
(* 0x8000137c *)   time_mem
                   + (if mem Ⓓ[gp ⊖ 0x7a0] =? 0x0
                     then
                       time_branch + 
(* 0x80001390 *)       2 + time_mem + time_mem + time_mem + 2 + time_mem + time_mem + 2 + time_mem
                       + (if negb(mem Ⓓ[mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30]] =? 0xa5a5a5a5)
                         then
                           time_branch + 
(* 0x800013d0 *)           time_inf
                         else
                           3 + 
(* 0x800013b8 *)           time_mem
                           + (if negb(mem Ⓓ[mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0x4] =? mem Ⓓ[mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30]])
                             then
                               time_branch + 
(* 0x800013d0 *)               time_inf
                             else
                               3 + 
(* 0x800013c0 *)               time_mem
                               + (if negb(mem Ⓓ[mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0x8] =? mem Ⓓ[mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0x4])
                                 then
                                   time_branch + 
(* 0x800013d0 *)                   time_inf
                                 else
                                   3 + 
(* 0x800013c8 *)                   time_mem
                                   + (if mem Ⓓ[mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0xc] =? mem Ⓓ[mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0x8]
                                     then
                                       time_branch + 
(* 0x800013e0 *)                       time_mem + 2 + (3 + clz (mem Ⓓ[gp ⊖ 0x780]) 32) + 2 + 2 + 36 + 2 + 2 + 2 + time_mem + 2 + 2 + time_mem + time_mem
                                       + (if negb(mem Ⓓ[mem Ⓓ[gp + 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 ⊖ 0x398] + 0x4] =? 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 + gp ⊖ 0x394)
                                         then
                                           time_branch + 
(* 0x80001424 *)                           2 + 36 + time_mem + 2 + time_mem + time_mem + time_mem + time_mem + time_mem + 2 + time_branch
                                         else
                                           3 + 
(* 0x8000141c *)                           time_mem + time_mem +
(* 0x80001424 *)                           2 + 36 + time_mem + 2 + time_mem + time_mem + time_mem + time_mem + time_mem + 2 + time_branch
                                         )
                                     else
                                       3 + 
(* 0x800013d0 *)                       time_inf
                                     )
                                 )
                             )
                         )
                     else
                       3 + 
(* 0x80001384 *)       2 + time_mem + time_branch
                     ).


(* Memory Regions *)
Definition memory_regions
    (mem : addr -> N)
    (gp : N)
    := map (fun x => (4, x)) [
		gp ⊖ 0x780;
		gp + 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 ⊖ 0x398;
		gp + 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 ⊖ 0x390;
		mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30];
		mem Ⓓ[gp + 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 ⊖ 0x398] + 0xc;
		0x7ffffff7;
		gp ⊖ 0x768;
		gp ⊖ 0x78c;
		mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0x8;
		mem Ⓓ[gp + 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 ⊖ 0x398] + 0x4;
		mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0xc;
		mem Ⓓ[mem Ⓓ[gp ⊖ 0x768] + 0x30] + 0x4;
		gp ⊖ 0x7a0;
		mem Ⓓ[gp ⊖ 0x768] + 0x30;
		0x7ffffffb
      ].

Definition noverlaps
    (mem : addr -> N)
    (gp : N)
    :=  create_noverlaps (memory_regions mem gp).


(* Invariants *)
Definition vTaskSwitchContext_timing_invs 
    (mem : addr -> N)
    (gp : N)
    (t : trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x8000137c => Some (s R_GP = Ⓓgp /\
			s V_MEM32 = Ⓜmem /\
			noverlaps mem gp /\
			cycle_count_of_trace t' = 0)
| 0x80001424 => Some (exists mem, s V_MEM32 = Ⓜmem /\
			noverlaps mem gp /\
			cycle_count_of_trace t' =   
  (* 0x8000137c *)   time_mem + 
                       time_branch + 
  (* 0x80001390 *)   2 + time_mem + time_mem + time_mem + 2 + time_mem + time_mem + 2 + time_mem + 
                       3 + 
  (* 0x800013b8 *)   time_mem + 
                       3 + 
  (* 0x800013c0 *)   time_mem + 
                       3 + 
  (* 0x800013c8 *)   time_mem + 
                       time_branch + 
  (* 0x800013e0 *)   time_mem + 2 + (3 + clz (mem Ⓓ[gp ⊖ 0x780]) 32) + 2 + 2 + 36 + 2 + 2 + 2 + time_mem + 2 + 2 + time_mem + time_mem
                     + (if negb(mem Ⓓ[mem Ⓓ[gp + 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 ⊖ 0x398] + 0x4] =? 0x1f - CLZ(mem Ⓓ[gp ⊖ 0x780]) ⊗ 0x14 + gp ⊖ 0x394)
                       then
                         time_branch + 0
                       else
                         3 + 
  (* 0x8000141c *)       time_mem + time_mem + 0
                       )
		)
| 0x8000138c | 0x8000144c => Some (exists mem, s V_MEM32 = Ⓜmem /\
			time_of_vTaskSwitchContext t mem gp)
| _ => None end | _ => None end
.


(* Lift the program *)
Definition lifted_vTaskSwitchContext : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.


(* Proof *)
Theorem vTaskSwitchContext_timing:
  forall s t s' x' mem gp
    (ENTRY: startof t (x',s') = (Addr entry_addr, s))
    (MDL: models rvtypctx s)
    (NVL: create_noverlaps (memory_regions mem gp))
    (MEM: s V_MEM32 = Ⓜmem)
    (GP: s R_GP = Ⓓgp),
  satisfies_all
    lifted_vTaskSwitchContext
    (vTaskSwitchContext_timing_invs mem gp)
    exits
 ((x',s')::t).
Proof using.
  (* TODO *)
  Admitted.
Qed.
