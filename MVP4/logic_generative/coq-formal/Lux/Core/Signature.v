(** 
 * Lux Core Signature
 * 
 * This module defines the fundamental signature (interface) for the Lux mathematical
 * logic system. It specifies the core algebraic structures and operations that form
 * the foundation of the Lux formalism.
 * 
 * The signature includes:
 * - Four commutative semirings (L, R, Core, B) with B being a Frobenius algebra
 * - Observer/embedding maps between semirings
 * - Central units and braiding operations
 * - Exponential/logarithmic structure for header operations
 * - Basepoint and Gen4 operations
 * 
 * This signature is designed to be instantiated by concrete implementations
 * that provide the actual mathematical structures.
 *)

From Coq Require Import Setoids.Setoid.
From Coq Require Import Morphisms.
From Coq Require Import ZArith.

From Lux.Util Require Import Semiring SemiringFunctor.

Module Type LuxSignature.
  (** Unit sort I for typing central scalars *)
  Parameter I : Type.
  
  (** Four commutative semirings using proper abstraction *)
  Module L <: CommutativeSemiring.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    Infix "+" := add. Infix "*" := mul.
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
  End L.
  
  Module R <: CommutativeSemiring.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    Infix "+" := add. Infix "*" := mul.
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
  End R.
  
  Module Core <: CommutativeSemiring.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    Infix "+" := add. Infix "*" := mul.
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
  End Core.
  
  (** B is a Frobenius algebra (bulk semiring with comultiplication) *)
  Module B <: FrobeniusAlgebra.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    Parameter comul : carrier -> carrier * carrier.
    
    Infix "+" := add. Infix "*" := mul.
    
    (** Semiring axioms *)
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
    
    (** Frobenius compatibility *)
    Axiom frobenius_l : forall x y z, x * (fst (comul y)) * z = fst (comul (x * y * z)).
    Axiom frobenius_r : forall x y z, x * (snd (comul y)) * z = snd (comul (x * y * z)).
  End B.

  (** Observer/embedding maps between semirings *)
  Parameter iotaL : L.carrier -> B.carrier.
  Parameter iotaR : R.carrier -> B.carrier.
  Parameter iotaCore : Core.carrier -> B.carrier.
  Parameter nuL   : B.carrier -> L.carrier.
  Parameter nuR   : B.carrier -> R.carrier.

  (** Central units in B *)
  Parameter phi z zbar : B.carrier.
  Parameter ad : nat -> B.carrier -> B.carrier.

  (** Basepoint/Gen4 operations *)
  Parameter a0 a1 a2 a3 : B.carrier.
  Parameter Gen4 : B.carrier -> B.carrier -> B.carrier -> B.carrier -> B.carrier.

  (** Exponential/logarithmic structure for header operations *)
  Parameter dec : B.carrier -> (Z * Z * Z) * Core.carrier.
  Parameter rec : (Z * Z * Z) * Core.carrier -> B.carrier.
  
  (** Header extraction functions *)
  Parameter k_phi : B.carrier -> Z.
  Parameter m_z : B.carrier -> Z.
  Parameter m_zbar : B.carrier -> Z.
  Parameter core : B.carrier -> Core.carrier.
  
  (** Scale header (derived from z and zbar headers) *)
  Definition m_Lambda (t : B.carrier) : Z := Z.add (m_z t) (m_zbar t).
  
  (** Lambda central unit (derived from z and zbar) *)
  Definition Lambda : B.carrier := B.mul z zbar.
End LuxSignature.

