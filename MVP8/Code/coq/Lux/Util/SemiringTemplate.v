(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

(** 
 * Semiring Template
 * 
 * This module provides a template for creating commutative semirings
 * to reduce code duplication in the Signature module.
 *)

From Lux.Util Require Import Semiring.

Module Type CommutativeSemiringTemplate.
  Parameter carrier : Type.
  Parameter zero one : carrier.
  Parameter add mul : carrier -> carrier -> carrier.
  
  Infix "+" := add.
  Infix "*" := mul.
  
  (** Semiring axioms *)
  Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
  Axiom add_comm  : forall x y, x + y = y + x.
  Axiom add_zero_l : forall x, zero + x = x.
  
  Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
  Axiom mul_comm  : forall x y, x * y = y * x.
  Axiom mul_one_l : forall x, one * x = x.
  
  Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
  Axiom mul_zero_l : forall x, zero * x = zero.
  
  (** Mathematical foundation axioms *)
  Axiom non_trivial : zero <> one.
  Axiom add_zero_r : forall x, x + zero = x.
  Axiom mul_one_r : forall x, x * one = x.
  Axiom mul_zero_r : forall x, x * zero = zero.
  
  (** Derived lemmas *)
  Lemma add_zero_r' : forall x, x + zero = x.
  Proof. intros. rewrite add_comm. apply add_zero_l. Qed.
  
  Lemma mul_one_r' : forall x, x * one = x.
  Proof. intros. rewrite mul_comm. apply mul_one_l. Qed.
  
  Lemma mul_zero_r' : forall x, x * zero = zero.
  Proof. intros. rewrite mul_comm. apply mul_zero_l. Qed.
End CommutativeSemiringTemplate.

(** Helper to create semiring instances *)
Module MakeCommutativeSemiring (T:CommutativeSemiringTemplate) <: CommutativeSemiring.
  Definition carrier := T.carrier.
  Definition zero := T.zero.
  Definition one := T.one.
  Definition add := T.add.
  Definition mul := T.mul.
  
  Infix "+" := add.
  Infix "*" := mul.
  
  Definition add_assoc := T.add_assoc.
  Definition add_comm := T.add_comm.
  Definition add_zero_l := T.add_zero_l.
  
  Definition mul_assoc := T.mul_assoc.
  Definition mul_comm := T.mul_comm.
  Definition mul_one_l := T.mul_one_l.
  
  Definition mul_distr_l := T.mul_distr_l.
  Definition mul_zero_l := T.mul_zero_l.
  
  (* Mathematical foundation axioms *)
  Definition non_trivial := T.non_trivial.
  Definition add_zero_r := T.add_zero_r.
  Definition mul_one_r := T.mul_one_r.
  Definition mul_zero_r := T.mul_zero_r.
End MakeCommutativeSemiring.
