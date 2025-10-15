(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

(** 
 * Semiring Functors and Advanced Algebraic Structures
 * 
 * This module provides abstract algebraic structures used throughout the Lux
 * mathematical logic system. It defines functors and module types that enable
 * clean abstraction and code reuse.
 * 
 * Key structures:
 * - FrobeniusAlgebra: Semiring with comultiplication and Frobenius compatibility
 * - DistributiveLattice: Algebraic structure for guarded negation
 * 
 * This module is essential for maintaining clean abstractions and avoiding
 * code duplication in the Lux system.
 *)

From Coq Require Import Setoids.Setoid.
From Coq Require Import Morphisms.

From Lux.Util Require Import Semiring.

(** Frobenius algebra structure for the bulk semiring B *)
Module Type FrobeniusAlgebra.
  Parameter carrier : Type.
  Parameter zero one : carrier.
  Parameter add mul : carrier -> carrier -> carrier.
  Parameter comul : carrier -> carrier * carrier.
  
  Infix "+" := add.
  Infix "*" := mul.
  
  (** Semiring axioms *)
  Parameter add_assoc : forall x y z, x + (y + z) = (x + y) + z.
  Parameter add_comm  : forall x y, x + y = y + x.
  Parameter add_zero_l : forall x, zero + x = x.
  
  Parameter mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
  Parameter mul_comm  : forall x y, x * y = y * x.
  Parameter mul_one_l : forall x, one * x = x.
  
  Parameter mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
  Parameter mul_zero_l : forall x, zero * x = zero.
  
  (** Frobenius compatibility *)
  Parameter frobenius_l : forall x y z, x * (fst (comul y)) * z = fst (comul (x * y * z)).
  Parameter frobenius_r : forall x y z, x * (snd (comul y)) * z = snd (comul (x * y * z)).
  
End FrobeniusAlgebra.

(** Distributive lattice structure for guarded negation *)
Module Type DistributiveLattice.
  Parameter carrier : Type.
  Parameter bot top : carrier.
  Parameter meet join : carrier -> carrier -> carrier.
  
  Infix "∧" := meet (at level 50, left associativity).
  Infix "∨" := join (at level 50, left associativity).
  
  (** Lattice axioms *)
  Parameter meet_assoc : forall x y z, x ∧ (y ∧ z) = (x ∧ y) ∧ z.
  Parameter meet_comm  : forall x y, x ∧ y = y ∧ x.
  Parameter meet_idem  : forall x, x ∧ x = x.
  Parameter meet_top   : forall x, x ∧ top = x.
  
  Parameter join_assoc : forall x y z, x ∨ (y ∨ z) = (x ∨ y) ∨ z.
  Parameter join_comm  : forall x y, x ∨ y = y ∨ x.
  Parameter join_idem  : forall x, x ∨ x = x.
  Parameter join_bot   : forall x, x ∨ bot = x.
  
  (** Absorption laws *)
  Parameter meet_join_abs : forall x y, x ∧ (x ∨ y) = x.
  Parameter join_meet_abs : forall x y, x ∨ (x ∧ y) = x.
  
  (** Distributivity *)
  Parameter meet_distr : forall x y z, x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z).
  Parameter join_distr : forall x y z, x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z).
  
End DistributiveLattice.
