From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms.

Module Observers (S:LuxSignature).
  Module Ax := Axioms(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  Definition projL (t:B.carrier) : B.carrier := S.iotaL (S.nuL t).
  Definition projR (t:B.carrier) : B.carrier := S.iotaR (S.nuR t).
  Definition rho (t:B.carrier) : B.carrier := B.add (projL t) (projR t).
  
  (* Residual (interaction term) *)
  Definition residual (t:B.carrier) : B.carrier := B.add t (rho t).
  
  (* Interaction term (no subtraction needed) *)
  Definition interaction (t:B.carrier) : B.carrier := residual t.
  
  (* Bulk = Two Boundaries (reconstitution) *)
  Definition bulk_two_boundaries (t:B.carrier) : B.carrier := rho t.

  Lemma projL_idem : forall t, projL (projL t) = projL t.
  Proof.
    intro t. unfold projL. rewrite Ax.nu_iotaL_retraction. reflexivity.
  Qed.

  Lemma projR_idem : forall t, projR (projR t) = projR t.
  Proof.
    intro t. unfold projR. rewrite Ax.nu_iotaR_retraction. reflexivity.
  Qed.

  Lemma projL_projR_zero : forall t, projL (projR t) = B.zero.
  Proof.
    intro t. unfold projL, projR.
    rewrite Ax.cross_connector_L. apply Ax.iotaL_zero.
  Qed.

  Lemma projR_projL_zero : forall t, projR (projL t) = B.zero.
  Proof.
    intro t. unfold projL, projR.
    rewrite Ax.cross_connector_R. apply Ax.iotaR_zero.
  Qed.

  Local Lemma add_zero_r : forall x, B.add x B.zero = x.
  Proof.
    intro x. rewrite B.add_comm. apply B.add_zero_l.
  Qed.

  Local Lemma L_add_zero_r : forall x, L.add x L.zero = x.
  Proof.
    intro x. rewrite L.add_comm. apply L.add_zero_l.
  Qed.

  Local Lemma R_add_zero_r : forall x, R.add x R.zero = x.
  Proof.
    intro x. rewrite R.add_comm. apply R.add_zero_l.
  Qed.

  Lemma rho_idem : forall t, rho (rho t) = rho t.
  Proof.
    intro t. unfold rho, projL, projR.
    (* After unfolding: B.add (S.iotaL (S.nuL (B.add (S.iotaL (S.nuL t)) (S.iotaR (S.nuR t))))) 
                                (S.iotaR (S.nuR (B.add (S.iotaL (S.nuL t)) (S.iotaR (S.nuR t))))) *)
    rewrite Ax.nuL_add, Ax.nuR_add.
    rewrite Ax.iotaL_add, Ax.iotaR_add.
    rewrite Ax.nu_iotaL_retraction, Ax.nu_iotaR_retraction.
    rewrite Ax.cross_connector_L, Ax.cross_connector_R.
    rewrite Ax.iotaL_zero, Ax.iotaR_zero.
    (* Now: B.add (B.add (S.iotaL (S.nuL t)) B.zero) (B.add B.zero (S.iotaR (S.nuR t))) *)
    rewrite add_zero_r, B.add_zero_l.
    reflexivity.
  Qed.

  Lemma observer_equality_L : forall t,
    S.nuL t = S.nuL (rho t).
  Proof.
    intro t. unfold rho, projL, projR.
    (* S.nuL (rho t) = S.nuL (S.iotaL (S.nuL t) + S.iotaR (S.nuR t)) *)
    (* = S.nuL (S.iotaL (S.nuL t)) + S.nuL (S.iotaR (S.nuR t)) *)
    (* = S.nuL t + 0 = S.nuL t *)
    rewrite Ax.nuL_add.
    rewrite Ax.nu_iotaL_retraction.
    rewrite Ax.cross_connector_L.
    rewrite L_add_zero_r.
    reflexivity.
  Qed.

  Lemma observer_equality_R : forall t,
    S.nuR t = S.nuR (rho t).
  Proof.
    intro t. unfold rho, projL, projR.
    (* S.nuR (rho t) = S.nuR (S.iotaL (S.nuL t) + S.iotaR (S.nuR t)) *)
    (* = S.nuR (S.iotaL (S.nuL t)) + S.nuR (S.iotaR (S.nuR t)) *)
    (* = 0 + S.nuR t = S.nuR t *)
    rewrite Ax.nuR_add.
    rewrite Ax.cross_connector_R.
    rewrite Ax.nu_iotaR_retraction.
    rewrite R.add_zero_l.
    reflexivity.
  Qed.
End Observers.