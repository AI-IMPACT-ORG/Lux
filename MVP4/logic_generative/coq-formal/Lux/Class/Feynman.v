(* (c) 2025 AI.IMPACT GmbH *)

From Coq Require Import ZArith List.
From Lux.Core Require Import Signature Axioms Observers NF.

Module Feynman (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module N := NF(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  (* History step *)
  Record HistoryStep := {
    braid_index : nat;
    weight : B.carrier
  }.

  (* History *)
  Definition History := list HistoryStep.

  (* Step weight (central; integer headers) *)
  Parameter step_weight : nat -> B.carrier.
  Axiom step_weight_central : forall i t,
    B.mul (step_weight i) t = B.mul t (step_weight i).

  (* R-data matrix for scale splitting *)
  Parameter R_data : (Z * Z) * (Z * Z).
  Axiom R_data_constraint : 
    let '((r11, r12), (r21, r22)) := R_data in
    (r11 + r21)%Z = 1%Z /\ (r12 + r22)%Z = 1%Z.

  (* Action along a history *)
  Definition action (H : History) : B.carrier :=
    List.fold_left (fun acc step => B.mul acc step.(weight)) H B.one.

  (* Partition function (definitional) *)
  Definition Z_J (J : nat -> L.carrier) (H : History) : L.carrier :=
    S.nuL (N.NF_B (action H)).

  (* Sum over histories *)
  Parameter histories : nat -> L.carrier -> list History.
  Definition sum_over_histories (J : nat -> L.carrier) : L.carrier :=
    let hist_list := histories 0 (J 0) in
    List.fold_left (fun acc H => L.add acc (Z_J J H)) hist_list L.zero.

  (* Renormalisation identities *)

  (* Counterterm identity *)
  Parameter scheme_change : (Z * Z * Z) -> B.carrier -> B.carrier.
  Axiom counterterm_identity : forall Delta t,
    N.NF_B t = scheme_change Delta (N.NF_B t).

  (* Scheme invariance *)
  Axiom scheme_invariance : forall t Delta,
    S.nuL (N.NF_B t) = S.nuL (N.NF_B (scheme_change Delta t)).

  (* Wilson recursion *)
  Parameter kernel_step : B.carrier.
  Definition G_N (N : nat) : B.carrier :=
    List.fold_left (fun acc n => B.add B.one (B.mul kernel_step acc)) 
                   (List.seq 0 N) B.one.

  Axiom wilson_recursion : forall N,
    N.NF_B (G_N (S N)) = 
    B.add (N.NF_B B.one) (N.NF_B (B.mul kernel_step (G_N N))).

  (* Schwinger-Dyson identities *)
  Parameter Delta_i : nat -> (B.carrier -> B.carrier) -> B.carrier -> B.carrier.
  Axiom schwinger_dyson : forall i F,
    Delta_i i F (S.iotaL (sum_over_histories (fun _ => L.zero))) = B.zero.

  (* Equivalence with cumulant expansion *)
  Axiom feynman_cumulant_equivalence : forall J,
    sum_over_histories J = S.nuL (N.NF_B (G_N 10)).

End Feynman.
