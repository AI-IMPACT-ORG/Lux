Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import lib.generated_Core.

(* CLEAN v10 Property-Based Tests *)

Module PropertyTests.

(* Random data generation *)
Definition random_header : Header :=
  header (Random.float 10.0) (Random.float 10.0).

(* Property: Header addition is commutative *)
Definition prop_header_commutative : Prop :=
  forall h1 h2 : Header,
  header_equal (header_add h1 h2) (header_add h2 h1).

(* Property: Header addition is associative *)
Definition prop_header_associative : Prop :=
  forall h1 h2 h3 : Header,
  header_equal (header_add (header_add h1 h2) h3) (header_add h1 (header_add h2 h3)).

(* Property: Header zero is identity *)
Definition prop_header_zero_identity : Prop :=
  forall h : Header,
  header_equal (header_add h header_zero) h.

(* Property: Kernel composition is associative *)
Definition prop_kernel_associative : Prop :=
  forall k1 k2 k3 : Kernel,
  header_equal (kernel_header (kernel_compose (kernel_compose k1 k2) k3))
               (kernel_header (kernel_compose k1 (kernel_compose k2 k3))).

End PropertyTests.