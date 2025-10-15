(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

From Lux.Util Require Import StdlibImports.
From Lux.Core Require Import Signature Axioms Observers NF RegulatorScheme Counterterm.

Module Feynman (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module N := NF(S).
  Module RS := RegulatorScheme(S).
  Module CT := Counterterm(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  (* Use step_weight from RegulatorScheme *)
  Definition step_weight := RS.step_weight.
  Definition step_weight_central := RS.step_weight_central.

  (* Use kernel_step from Counterterm *)
  Definition kernel_step := CT.kernel_step.

  (* Use scheme_change from Counterterm *)
  Definition scheme_change := CT.scheme_change.

  (* Use counterterm_identity from Counterterm *)
  Definition counterterm_identity := CT.counterterm_identity.

  (* History step *)
  Record HistoryStep := {
    braid_index : nat;
    weight : B.carrier
  }.

  (* History *)
  Definition History := list HistoryStep.

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

  (* Scheme invariance *)
  Axiom scheme_invariance : forall t Delta,
    S.nuL (N.NF_B t) = S.nuL (N.NF_B (scheme_change Delta t)).

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
  Parameter truncation_order : nat.
  Axiom feynman_cumulant_equivalence : forall J,
    sum_over_histories J = S.nuL (N.NF_B (G_N truncation_order)).

End Feynman.
