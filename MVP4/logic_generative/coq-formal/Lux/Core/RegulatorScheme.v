From Coq Require Import ZArith List Bool.
From Lux.Core Require Import Signature Axioms NF.

Module RegulatorScheme (S:LuxSignature).
  Module Ax := Axioms(S).
  Module N := NF(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  (* Regulator window *)
  Record Regulator := {
    N : nat;  (* history length bound *)
    K : nat;  (* phase header bound *)
    M : nat   (* scale header bound *)
  }.

  (* Scheme *)
  Record Scheme := {
    mu_L : Z;     (* left moduli flow *)
    theta_L : Z;  (* left phase flow *)
    mu_R : Z;     (* right moduli flow *)
    theta_R : Z;  (* right phase flow *)
    z : B.carrier;     (* auxiliary moduli *)
    zbar : B.carrier;  (* auxiliary moduli *)
    R_data : (Z * Z) * (Z * Z)  (* R-data matrix *)
  }.

  (* R-data constraint *)
  Axiom R_data_constraint : forall sch,
    let '((r11, r12), (r21, r22)) := sch.(R_data) in
    (r11 + r21)%Z = 1%Z /\ (r12 + r22)%Z = 1%Z.

  (* Gauge-fixing convention *)
  Definition gauge_fix (t : B.carrier) (sch : Scheme) : B.carrier :=
    N.NF_B_parametric t sch.(mu_L) sch.(theta_L).

  (* Regularized observables *)
  Definition regularized_observable (F : B.carrier -> L.carrier) (K : B.carrier) 
                                   (R : Regulator) (sch : Scheme) : L.carrier :=
    S.nuL (gauge_fix K sch).

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

  (* Action along a history *)
  Definition action (H : History) : B.carrier :=
    List.fold_left (fun acc step => B.mul acc step.(weight)) H B.one.

  (* Sum over histories with regulator bounds *)
  Parameter histories : nat -> L.carrier -> list History.
  Definition sum_over_histories_regulated (J : nat -> L.carrier) (R : Regulator) : L.carrier :=
    let hist_list := histories R.(N) (J 0) in
    List.fold_left (fun acc H => L.add acc (S.nuL (N.NF_B (action H)))) hist_list L.zero.

  (* Header bounds enforcement *)
  Definition enforce_bounds (t : B.carrier) (R : Regulator) : option B.carrier :=
    let '(k, m_Lambda, c) := N.NF_tuple t in
    if (Z.abs k <=? Z.of_nat R.(K))%Z && (Z.abs m_Lambda <=? Z.of_nat R.(M))%Z
    then Some t
    else None.

End RegulatorScheme.
