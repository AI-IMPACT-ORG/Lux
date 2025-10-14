(* (c) 2025 AI.IMPACT GmbH *)

From Coq Require Import ZArith.
From Lux.Util Require Import Semiring SemiringFunctor.
From Lux.Core Require Import Signature Axioms Observers.

Module Type MinimalModel <: LuxSignature.
  (* Unit sort *)
  Parameter I : Type.
  
  Module L : CommutativeSemiring.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    
    Infix "+" := add.
    Infix "*" := mul.
    
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
  End L.
  
  Module R : CommutativeSemiring.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    
    Infix "+" := add.
    Infix "*" := mul.
    
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
  End R.
  
  Module Core : CommutativeSemiring.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    
    Infix "+" := add.
    Infix "*" := mul.
    
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
  End Core.
  
  Module B : FrobeniusAlgebra.
    Parameter carrier : Type.
    Parameter zero one : carrier.
    Parameter add mul : carrier -> carrier -> carrier.
    Parameter comul : carrier -> carrier * carrier.
    
    Infix "+" := add. Infix "*" := mul.
    
    (* Semiring axioms *)
    Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
    Axiom add_comm  : forall x y, x + y = y + x.
    Axiom add_zero_l : forall x, zero + x = x.
    
    Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
    Axiom mul_comm  : forall x y, x * y = y * x.
    Axiom mul_one_l : forall x, one * x = x.
    
    Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
    Axiom mul_zero_l : forall x, zero * x = zero.
    
    (* Frobenius compatibility *)
    Axiom frobenius_l : forall x y z, x * (fst (comul y)) * z = fst (comul (x * y * z)).
    Axiom frobenius_r : forall x y z, x * (snd (comul y)) * z = snd (comul (x * y * z)).
  End B.
  Parameter iotaL : L.carrier -> B.carrier.
  Parameter iotaR : R.carrier -> B.carrier.
  Parameter iotaCore : Core.carrier -> B.carrier.
  Parameter nuL   : B.carrier -> L.carrier.
  Parameter nuR   : B.carrier -> R.carrier.
  Parameter phi z zbar : B.carrier.
  Parameter ad : nat -> B.carrier -> B.carrier.
  Parameter a0 a1 a2 a3 : B.carrier.
  Parameter Gen4 : B.carrier -> B.carrier -> B.carrier -> B.carrier -> B.carrier.
  Parameter dec : B.carrier -> (Z * Z * Z) * Core.carrier.
  Parameter rec : (Z * Z * Z) * Core.carrier -> B.carrier.
  Parameter k_phi : B.carrier -> Z.
  Parameter m_z : B.carrier -> Z.
  Parameter m_zbar : B.carrier -> Z.
  Parameter core : B.carrier -> Core.carrier.
  
  (* Derived definitions *)
  Definition m_Lambda (t : B.carrier) : Z := Z.add (m_z t) (m_zbar t).
  Definition Lambda : B.carrier := B.mul z zbar.
End MinimalModel.

Module Test (S:MinimalModel).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).

  Theorem bulk_two_boundaries_L : forall t, S.nuL t = S.nuL (Obs.rho t).
  Proof. apply Obs.observer_equality_L. Qed.

  Theorem bulk_two_boundaries_R : forall t, S.nuR t = S.nuR (Obs.rho t).
  Proof. apply Obs.observer_equality_R. Qed.
End Test.

