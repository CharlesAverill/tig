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
Module xTimerIsTimerActiveTime <: TimingModule.
  Definition time_of_addr (s : store) (a : addr) : N :=
      match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
      | Some x => x | _ => 999 end.
  
  Definition entry_addr : N := 0x80003ec4.
  
  Definition exits (t:trace) : bool :=
      match t with (Addr a,_)::_ => match a with
      | 0x80003ee0 => true
      | _ => false
    end | _ => false end.
End xTimerIsTimerActiveTime.
Module xTimerIsTimerActiveAuto := TimingAutomation xTimerIsTimerActiveTime.
Import xTimerIsTimerActiveTime xTimerIsTimerActiveAuto.


Definition CLZ (n : N) : N := clz(n) 32.


(* Postcondition *)
Definition time_of_xTimerIsTimerActive (t : trace)
    (mem : addr -> N)
    (mstatus : N)
    (a0 : N)
  : Prop :=
    cycle_count_of_trace t =
(* 0x80003ec4 *)   ((* ERROR: csrrci [None, None, None] *) err_time) + 2 + time_mem + time_mem + 2
                   + (if negb(mem Ⓓ[0x80080004] =? 0x0)
                     then
                       time_branch + 
(* 0x80003ee0 *)       time_branch
                     else
                       3 + 
(* 0x80003edc *)       (* ERROR: csrrsi ['zero', 'mstatus', '8'] *) err_time +
(* 0x80003ee0 *)       time_branch
                     ).


(* Memory Regions *)
Definition memory_regions
    (mem : addr -> N)
    (mstatus : N)
    (a0 : N)
    := map (fun x => (4, x)) [
		0x80080004;
		a0 + 0x28
      ].

Definition noverlaps
    (mem : addr -> N)
    (mstatus : N)
    (a0 : N)
    :=  create_noverlaps (memory_regions mem mstatus a0).


(* Invariants *)
Definition xTimerIsTimerActive_timing_invs 
    (mem : addr -> N)
    (mstatus : N)
    (a0 : N)
    (t : trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80003ec4 => Some (s R_MSTATUS = Ⓓmstatus /\
			s R_A0 = Ⓓa0 /\
			s V_MEM32 = Ⓜmem /\
			noverlaps mem mstatus a0 /\
			cycle_count_of_trace t' = 0)
| 0x80003ee0 => Some (exists mem, s V_MEM32 = Ⓜmem /\
			noverlaps mem mstatus a0 /\
			cycle_count_of_trace t' =   
  (* 0x80003ec4 *)   ((* ERROR: csrrci [None, None, None] *) err_time) + 2 + time_mem + time_mem + 2
                     + (if negb(mem Ⓓ[0x80080004] =? 0x0)
                       then
                         time_branch + 0
                       else
                         3 + 
  (* 0x80003edc *)       (* ERROR: csrrsi ['zero', 'mstatus', '8'] *) err_time + 0
                       )
		)
| 0x80003ee0 => Some (exists mem, s V_MEM32 = Ⓜmem /\
			time_of_xTimerIsTimerActive t mem mstatus a0)
| _ => None end | _ => None end
.


(* Lift the program *)
Definition lifted_xTimerIsTimerActive : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.


(* Proof *)
Theorem xTimerIsTimerActive_timing:
  forall s t s' x' mem mstatus a0
    (ENTRY: startof t (x',s') = (Addr entry_addr, s))
    (MDL: models rvtypctx s)
    (NVL: create_noverlaps (memory_regions mem mstatus a0))
    (MEM: s V_MEM32 = Ⓜmem)
    (MSTATUS: s R_MSTATUS = Ⓓmstatus)
    (A0: s R_A0 = Ⓓa0),
  satisfies_all
    lifted_xTimerIsTimerActive
    (xTimerIsTimerActive_timing_invs mem mstatus a0)
    exits
 ((x',s')::t).
Proof using.
  (* TODO *)
  Admitted.
Qed.
