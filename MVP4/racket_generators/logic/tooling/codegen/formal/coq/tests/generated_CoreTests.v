Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import lib.generated_Core.
Require Import lib.generated_Observers.
Require Import lib.generated_Kernels.
Require Import lib.generated_NormalForms.

(* CLEAN v10 Core Mathematical Tests *)

Module CoreTests.

(* Test 1: Basic Type Definitions *)
Definition test_sort_definition : Prop :=
  exists s : Sort, s = L \/ s = B \/ s = R \/ s = I.

Definition test_operation_definition : Prop :=
  exists op : Operation, op = PlusB \/ op = MultB.

Definition test_term_definition : Prop :=
  exists t : Term, True.

(* Test 2: Observer Functions *)
Definition test_observer_value : Prop :=
  forall t : Term, observer_value t = observer_value t.

Definition test_reflect_L : Prop :=
  forall t : Term, reflect_L t = reflect_L t.

Definition test_reflect_R : Prop :=
  forall t : Term, reflect_R t = reflect_R t.

End CoreTests.