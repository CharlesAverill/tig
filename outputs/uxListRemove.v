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
Module uxListRemoveTime <: TimingModule.
  Definition time_of_addr (s : store) (a : addr) : N :=
      match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
      | Some x => x | _ => 999 end.
  
  Definition entry_addr : N := 0x80002440.
  
  Definition exits (t:trace) : bool :=
      match t with (Addr a,_)::_ => match a with
      | 0x80002470 => true
      | _ => false
    end | _ => false end.
End uxListRemoveTime.
Module uxListRemoveAuto := TimingAutomation uxListRemoveTime.
Import uxListRemoveTime uxListRemoveAuto.


Definition CLZ (n : N) : N := clz(n) 32.


(* Postcondition *)
Definition time_of_uxListRemove (t : trace)
    (mem : addr -> N)
    (a0 : N)
  : Prop :=
    cycle_count_of_trace t =
(* 0x80002440 *)   time_mem + time_mem + time_mem + time_mem + time_mem + time_mem
                   + (if negb(mem Ⓓ[mem Ⓓ[a0 + 0x10] + 0x4] =? a0)
                     then
                       time_branch + 
(* 0x80002460 *)       time_mem + time_mem + 2 + time_mem + time_branch
                     else
                       3 + 
(* 0x8000245c *)       time_mem +
(* 0x80002460 *)       time_mem + time_mem + 2 + time_mem + time_branch
                     ).


(* Memory Regions *)
Definition memory_regions
    (mem : addr -> N)
    (a0 : N)
    := map (fun x => (4, x)) [
		mem Ⓓ[a0 + 0x4] + 0x8;
		mem Ⓓ[a0 + 0x10];
		a0 + 0x10;
		a0 + 0x4;
		a0 + 0x8;
		mem Ⓓ[a0 + 0x8] + 0x4;
		mem Ⓓ[a0 + 0x10] + 0x4
      ].

Definition noverlaps
    (mem : addr -> N)
    (a0 : N)
    :=  create_noverlaps (memory_regions mem a0).


(* Invariants *)
Definition uxListRemove_timing_invs 
    (mem : addr -> N)
    (a0 : N)
    (t : trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x80002440 => Some (s R_A0 = Ⓓa0 /\
			s V_MEM32 = Ⓜmem /\
			noverlaps mem a0 /\
			cycle_count_of_trace t' = 0)
| 0x80002460 => Some (exists mem, s V_MEM32 = Ⓜmem /\
			noverlaps mem a0 /\
			cycle_count_of_trace t' =   
  (* 0x80002440 *)   time_mem + time_mem + time_mem + time_mem + time_mem + time_mem
                     + (if negb(mem Ⓓ[mem Ⓓ[a0 + 0x10] + 0x4] =? a0)
                       then
                         time_branch + 0
                       else
                         3 + 
  (* 0x8000245c *)       time_mem + 0
                       )
		)
| 0x80002470 => Some (exists mem, s V_MEM32 = Ⓜmem /\
			time_of_uxListRemove t mem a0)
| _ => None end | _ => None end
.


(* Lift the program *)
Definition lifted_uxListRemove : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.


(* Proof *)
Theorem uxListRemove_timing:
  forall s t s' x' mem a0
    (ENTRY: startof t (x',s') = (Addr entry_addr, s))
    (MDL: models rvtypctx s)
    (NVL: create_noverlaps (memory_regions mem a0))
    (MEM: s V_MEM32 = Ⓜmem)
    (A0: s R_A0 = Ⓓa0),
  satisfies_all
    lifted_uxListRemove
    (uxListRemove_timing_invs mem a0)
    exits
 ((x',s')::t).
Proof using.
  (* TODO *)
  Admitted.
Qed.
