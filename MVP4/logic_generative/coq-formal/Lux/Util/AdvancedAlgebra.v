(* (c) 2025 AI.IMPACT GmbH *)

From Coq Require Import Setoids.Setoid.
From Coq Require Import Morphisms.

From Lux.Util Require Import Semiring SemiringFunctor.

(* Header-degree filter for divergence detection *)
Module Type HeaderDegreeFilter.
  Parameter carrier : Type.
  Parameter header_degree : carrier -> nat.
  Parameter threshold : nat.
  Parameter add : carrier -> carrier -> carrier.
  Parameter mul : carrier -> carrier -> carrier.
  
  (* Divergence predicate *)
  Definition divergent (x : carrier) : Prop :=
    header_degree x > threshold.
    
  (* Degree preservation *)
  Parameter degree_add : forall x y,
    header_degree (add x y) <= max (header_degree x) (header_degree y).
  Parameter degree_mul : forall x y,
    header_degree (mul x y) = (header_degree x + header_degree y)%nat.
    
End HeaderDegreeFilter.

(* Ring completion for applications *)
Module Type RingCompletion.
  Parameter carrier : Type.
  Parameter embed : carrier -> carrier.
  Parameter add : carrier -> carrier -> carrier.
  Parameter mul : carrier -> carrier -> carrier.
  Parameter neg : carrier -> carrier.
  Parameter zero one : carrier.
  
  (* Ring axioms *)
  Parameter add_assoc : forall x y z, add x (add y z) = add (add x y) z.
  Parameter add_comm : forall x y, add x y = add y x.
  Parameter add_zero_l : forall x, add zero x = x.
  Parameter add_neg_l : forall x, add (neg x) x = zero.
  
  Parameter mul_assoc : forall x y z, mul x (mul y z) = mul (mul x y) z.
  Parameter mul_comm : forall x y, mul x y = mul y x.
  Parameter mul_one_l : forall x, mul one x = x.
  Parameter mul_distr_l : forall x y z, mul x (add y z) = add (mul x y) (mul x z).
  
End RingCompletion.
