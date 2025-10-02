Require Import Core.


(* CLEAN v10 Observers - Expanded with Logical Functions *)

Definition project_L : Term -> Term :=
  fun t => t.

Definition project_R : Term -> Term :=
  fun t => t.

Definition inject_L : Term -> Term :=
  fun t => t.

Definition inject_R : Term -> Term :=
  fun t => t.

Definition reflect_L : Term -> Term :=
  fun t => TermInject_L t.

Definition reflect_R : Term -> Term :=
  fun t => TermInject_R t.

Definition observer_value : Term -> Term :=
  fun t => TermProject_L t.

Definition reconstitute : Term -> Term -> Term :=
  fun l r => TermPlusB l r.

Definition residual : Term -> Term :=
  fun t => TermPlusB (project_L t) (project_R t).

Definition triality_sum : Term -> Term -> Term -> Term :=
  fun l b r => TermPlusB (TermPlusB l b) r.
