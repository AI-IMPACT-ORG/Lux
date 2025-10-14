(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms Observers.

Module Truth (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).

  Theorem bulk_two_boundaries_L : forall t, S.nuL t = S.nuL (Obs.rho t).
  Proof. apply Obs.observer_equality_L. Qed.

  Theorem bulk_two_boundaries_R : forall t, S.nuR t = S.nuR (Obs.rho t).
  Proof. apply Obs.observer_equality_R. Qed.
End Truth.
