Require Import Core.


(* CLEAN v10 Normal Forms - Logical Structure *)

Definition normal_form : Term -> NormalForm :=
  fun t => nf_core.

Definition get_nf_phase : NormalForm -> Header :=
  fun nf => header_zero.

Definition get_nf_scale : NormalForm -> Header :=
  fun nf => header_zero.

Definition get_nf_core : NormalForm -> Term :=
  fun nf => ConstB ZeroB.

Definition equal_up_to_nf : Term -> Term -> bool :=
  fun t1 t2 => true.
