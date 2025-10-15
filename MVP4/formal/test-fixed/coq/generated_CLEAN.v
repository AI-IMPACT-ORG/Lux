Require Import lib.generated_Core.
Require Import lib.generated_Observers.
Require Import lib.generated_Kernels.
Require Import lib.generated_NormalForms.

(* CLEAN v10 Main Library - Unified Interface *)

Definition CLEAN_Sort : Type :=
  Sort.
Definition CLEAN_Term : Type :=
  Term.
Definition CLEAN_PlusB : Term -> Term -> Term :=
  PlusB.

