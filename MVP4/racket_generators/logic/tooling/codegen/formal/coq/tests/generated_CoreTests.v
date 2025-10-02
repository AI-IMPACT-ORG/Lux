Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import lib.generated_Core.
Require Import lib.generated_Observers.
Require Import lib.generated_Kernels.
Require Import lib.generated_NormalForms.

(* CLEAN v10 Core Mathematical Tests *)

Module CoreTests.

(* Test 1: Header Mathematics *)
Definition test_header_addition : Prop :=
  let h1 := (header 1.0 2.0) in
  let h2 := (header 3.0 4.0) in
  let sum := header_add h1 h2 in
  header_equal sum (header 4.0 6.0).

Definition test_header_multiplication : Prop :=
  let h1 := (header 1.0 2.0) in
  let h2 := (header 3.0 4.0) in
  let product := header_multiply h1 h2 in
  header_equal product (header 3.0 8.0).

(* Test 2: Kernel Composition Laws *)
Definition test_kernel_associativity : Prop :=
  let k1 := kernel (header 1.0 2.0) (transition 'k1 (fun x => x) nil) in
  let k2 := kernel (header 3.0 4.0) (transition 'k2 (fun x => x) nil) in
  let k3 := kernel (header 5.0 6.0) (transition 'k3 (fun x => x) nil) in
  let left_assoc := kernel_compose (kernel_compose k1 k2) k3 in
  let right_assoc := kernel_compose k1 (kernel_compose k2 k3) in
  header_equal (kernel_header left_assoc) (kernel_header right_assoc).

(* Test 3: Observer Functions *)
Definition test_observer_value : Prop :=
  let t := make_term 'test_term (header 2.0 3.0) 'test_core in
  let obs := observer_value t in
  term_equal obs t.

(* Test 4: Property-Based Testing *)
Definition test_header_commutativity : Prop :=
  forall h1 h2 : Header,
  header_equal (header_add h1 h2) (header_add h2 h1).

Definition test_header_associativity : Prop :=
  forall h1 h2 h3 : Header,
  header_equal (header_add (header_add h1 h2) h3) (header_add h1 (header_add h2 h3)).

End CoreTests.