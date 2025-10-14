(* (c) 2025 AI.IMPACT GmbH *)

From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms Observers.

Module TwoBI (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module B := S.B.

  Definition residual (t:B.carrier) : B.carrier := B.add t (Obs.rho t).

  Parameter J2BI : B.carrier -> Prop.
  Axiom J2BI_ideal : forall x y, J2BI x -> J2BI (B.add x y).
  Axiom J2BI_two_sided : forall x y, J2BI x -> J2BI (B.mul y x) /\ J2BI (B.mul x y).
  Axiom J2BI_braid_stable : forall i t, J2BI t -> J2BI (S.ad i t).
  Axiom J2BI_contains_residuals : forall t, J2BI (residual t).

  Parameter quotient : B.carrier -> B.carrier.
  Axiom quotient_kills_J2BI : forall t, J2BI t -> quotient t = B.zero.
  Axiom quotient_respects_add : forall t u, quotient (B.add t u) = B.add (quotient t) (quotient u).

  (* Spec-level universal property: π∘ρ = π (derived in intended models; assumed here) *)
  Axiom pi_rho_pi : forall t, quotient (Obs.rho t) = quotient t.
End TwoBI.
