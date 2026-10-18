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
Module {{func_name}}Time <: TimingModule.
  Definition time_of_addr (s : store) (a : addr) : N :=
      match neorv32_cycles_upper_bound ML s (RTOSDemo_NoAsserts_Clz a) with
      | Some x => x | _ => 999 end.
  
  Definition entry_addr : N := {{entry_addr}}.
  
  Definition exits (t:trace) : bool :=
      match t with (Addr a,_)::_ => match a with
      {{end_addrs}} => true
      | _ => false
    end | _ => false end.
End {{func_name}}Time.
Module {{func_name}}Auto := TimingAutomation {{func_name}}Time.
Import {{func_name}}Time {{func_name}}Auto.


Definition CLZ (n : N) : N := clz(n) 32.


(* Postcondition *)
{{postcondition}}


(* Memory Regions *)
{{memory_regions}}


(* Invariants *)
{{invariants}}


(* Lift the program *)
Definition lifted_{{func_name}} : program :=
    lift_riscv RTOSDemo_NoAsserts_Clz.


(* Proof *)
{{proof}}
