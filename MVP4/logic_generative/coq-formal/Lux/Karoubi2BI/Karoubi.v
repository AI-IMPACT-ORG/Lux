(* (c) 2025 AI.IMPACT GmbH *)

From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms Observers.

Module Karoubi (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module B := S.B.

  Definition idemp (e:B.carrier -> B.carrier) := forall t, e (e t) = e t.

  Lemma rho_idempotent : idemp Obs.rho.
  Proof.
    unfold idemp.
    (* Requires projL(projR t)=0 and projR(projL t)=0 to simplify cross terms. *)
    intros t. apply Obs.rho_idem.
  Qed.
End Karoubi.

