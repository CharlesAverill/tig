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

(* Common for all timing proofs - facilitates automation *)
Module vTaskSuspendAllTime <: TimingModule.
  Definition time_of_addr (s : store) (a : addr) : N :=
      match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
      | Some x => x | _ => 999 end.
  
  Definition entry_addr : N := 0x80000d14.
  
  Definition exits (t:trace) : bool :=
      match t with (Addr a,_)::_ => match a with
      | 0x80000d20 => true
      | _ => false
    end | _ => false end.
End vTaskSuspendAllTime.
Module vTaskSuspendAllAuto := TimingAutomation vTaskSuspendAllTime.
Import vTaskSuspendAllTime vTaskSuspendAllAuto.


Definition CLZ (n : N) : N := clz(n) 32.


(* Postcondition *)
Definition time_of_vTaskSuspendAll (t : trace)
  : Prop :=
    cycle_count_of_trace t =
(* 0x80000d14 *)   time_mem + 2 + time_mem + time_branch.


(* Memory Regions *)



(* Invariants *)
Definition vTaskSuspendAll_timing_invs 
        (t : trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80000d14 => Some (cycle_count_of_trace t' = 0)
| 0x80000d20 => Some (time_of_vTaskSuspendAll t)
| _ => None end | _ => None end
.


(* Lift the program *)
Definition lifted_vTaskSuspendAll : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.


(* Proof *)
Theorem vTaskSuspendAll_timing:
  forall s t s' x'
    (ENTRY: startof t (x',s') = (Addr entry_addr, s))
    (MDL: models rvtypctx s)
,
  satisfies_all
    lifted_vTaskSuspendAll
    (vTaskSuspendAll_timing_invs)
    exits
 ((x',s')::t).
Proof using.
  (* TODO *)
  Admitted.
Qed.
