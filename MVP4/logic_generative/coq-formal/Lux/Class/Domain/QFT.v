From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms Observers NF.
From Lux.Class Require Import PSDM Feynman.

Module QFTPort (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module N := NF(S).
  Module PSDM := PSDM(S).
  Module Feynman := Feynman(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  (* Euclidean carrier *)
  Parameter L_E : Type.
  Parameter L_E_zero L_E_one : L_E.
  Parameter L_E_add L_E_mul : L_E -> L_E -> L_E.

  (* Minkowski carrier *)
  Parameter L_M : Type.
  Parameter L_M_zero L_M_one : L_M.
  Parameter L_M_add L_M_mul : L_M -> L_M -> L_M.

  (* Phase semantics *)
  Parameter euclidean_phase : L_E -> L_E.
  Parameter minkowski_phase : L_M -> L_M.

  (* Feynman view *)
  Parameter histories_from_microsteps : B.carrier -> list Feynman.History.

  Definition action_product (H : Feynman.History) : B.carrier :=
    Feynman.action H.

  Definition amplitudes_via_domain (t : B.carrier) : L_E :=
    match PSDM.PSDM_B t with
    | Some _ => L_E_one
    | None => L_E_zero
    end.

  (* Propagator = inverse Fisher *)
  Parameter fisher_matrix : B.carrier -> B.carrier.
  Definition propagator (t : B.carrier) : B.carrier :=
    fisher_matrix t.

  (* Vertices = cumulants *)
  Parameter cumulant_vertex : nat -> B.carrier.
  Axiom cumulant_vertex_central : forall i t,
    B.mul (cumulant_vertex i) t = B.mul t (cumulant_vertex i).

  (* Wick choice *)
  Parameter wick_choice : bool.  (* true = Euclidean, false = Minkowski *)

  (* QFT carrier operations *)
  Definition qft_add (x y : L_E) : L_E := L_E_add x y.
  Definition qft_mul (x y : L_E) : L_E := L_E_mul x y.
  Definition qft_zero : L_E := L_E_zero.
  Definition qft_one : L_E := L_E_one.

  (* Phase header interpretation *)
  Definition phase_semantics (k_phi : Z) : L_E :=
    if wick_choice 
    then euclidean_phase (L_E_one)  (* damping factor *)
    else euclidean_phase (L_E_one). (* placeholder *)

  (* Scheme switch preserves cumulants *)
  Axiom scheme_invariance_qft : 
    qft_mul (phase_semantics 0) (qft_one) = qft_one.

  (* Schwinger-Dyson identities *)
  Axiom schwinger_dyson_qft : forall i F,
    Feynman.Delta_i i F (S.iotaL (Feynman.sum_over_histories (fun _ => L.zero))) = B.zero.

End QFTPort.
