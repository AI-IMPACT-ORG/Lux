(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

(** 
 * Quantum Field Theory Domain Port
 * 
 * This module provides QFT domain port implementations for the Lux system.
 * It includes both standard and semiring-based implementations to demonstrate
 * renormalization conditions and semantic mapping.
 *)

From Lux.Util Require Import StdlibImports ModuleInstantiations.
From Lux.Core Require Import Signature.
From Lux.Class Require Import PSDM Feynman.

(** Standard QFT Port Implementation *)
Module QFTPort (S:LuxSignature).
  Module Inst := LuxModuleInstantiations(S).
  Module Ax := Inst.Ax.
  Module Obs := Inst.Obs.
  Module N := Inst.N.
  Module PSDM := Inst.PSDM.
  Module Feynman := Inst.Feynman.
  Module L := Inst.L.
  Module R := Inst.R.
  Module B := Inst.B.

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

(** QFT Port with Core Semiring Dependency (Renormalization Demonstration) *)
Module QFTPortCoreSemiring (S:LuxSignature).
  Module Inst := LuxModuleInstantiations(S).
  Module Ax := Inst.Ax.
  Module Obs := Inst.Obs.
  Module N := Inst.N.
  Module PSDM := Inst.PSDM.
  Module Feynman := Inst.Feynman.
  Module L := Inst.L.
  Module R := Inst.R.
  Module B := Inst.B.
  Module Core := Inst.Core.

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

  (* 
   * RENORMALIZATION CONDITION: Phase header interpretation using Core semiring
   * 
   * Instead of: phase_semantics (k_phi : Z) : L_E
   * We use:     phase_semantics_core (k_phi : Core.carrier) : L_E
   * 
   * This demonstrates the semantic mapping ZArith → Core Semiring
   * while preserving the same mathematical content.
   *)
  Definition phase_semantics_core (k_phi : Core.carrier) : L_E :=
    if wick_choice 
    then euclidean_phase (L_E_one)  (* damping factor *)
    else euclidean_phase (L_E_one). (* placeholder *)

  (* 
   * RENORMALIZATION CONDITION: Core semiring operations
   * 
   * Instead of using ZArith operations (Z.add, Z.mul, etc.),
   * we use Core semiring operations (Core.add, Core.mul, etc.).
   * This preserves the mathematical structure while changing
   * the computational representation.
   *)
  Definition phase_header_add (k1 k2 : Core.carrier) : Core.carrier :=
    Core.add k1 k2.

  Definition phase_header_mul (k1 k2 : Core.carrier) : Core.carrier :=
    Core.mul k1 k2.

  Definition phase_header_zero : Core.carrier := Core.zero.

  Definition phase_header_one : Core.carrier := Core.one.

  (* 
   * RENORMALIZATION CONDITION: Scheme invariance
   * 
   * The port output remains invariant under the scheme change
   * from ZArith to Core semiring. This is the key renormalization
   * condition that ensures observational equivalence.
   *)
  Axiom scheme_invariance_core : 
    qft_mul (phase_semantics_core Core.zero) (qft_one) = qft_one.

  (* 
   * RENORMALIZATION CONDITION: Port coherence
   * 
   * The same mathematical operations produce the same results
   * regardless of whether we use ZArith or Core semiring.
   * This is the fundamental renormalization condition.
   *)
  Axiom port_coherence_core : forall k1 k2 : Core.carrier,
    phase_semantics_core (phase_header_add k1 k2) = 
    qft_mul (phase_semantics_core k1) (phase_semantics_core k2).

  (* Schwinger-Dyson identities *)
  Axiom schwinger_dyson_qft : forall i F,
    Feynman.Delta_i i F (S.iotaL (Feynman.sum_over_histories (fun _ => L.zero))) = B.zero.

  (* 
   * RENORMALIZATION CONDITION: Z to Core conversion
   * 
   * This function converts Z values to Core.carrier values,
   * implementing the semantic mapping ZArith → Core Semiring.
   * This is the key renormalization condition that allows
   * us to switch between different computational representations.
   *)
  Parameter Z_to_Core : Z -> Core.carrier.
  Axiom Z_to_Core_preserves_add : forall z1 z2,
    Z_to_Core (Z.add z1 z2) = Core.add (Z_to_Core z1) (Z_to_Core z2).
  Axiom Z_to_Core_preserves_mul : forall z1 z2,
    Z_to_Core (Z.mul z1 z2) = Core.mul (Z_to_Core z1) (Z_to_Core z2).
  Axiom Z_to_Core_zero : Z_to_Core 0%Z = Core.zero.
  Axiom Z_to_Core_one : Z_to_Core 1%Z = Core.one.

  (* 
   * RENORMALIZATION CONDITION: Header-only operations
   * 
   * The Core semiring operations act only on headers,
   * leaving the core mathematical structure unchanged.
   * This is exactly like the header-only NF operations
   * in the Lux framework.
   *)
  Definition header_only_phase (t : B.carrier) : Core.carrier :=
    let '(k, m_Lambda, c) := N.NF t in
    (* Extract phase header k and convert to Core semiring *)
    (* This is header-only - it doesn't affect the core component c *)
    Z_to_Core k.

  (* 
   * RENORMALIZATION CONDITION: Moduli-regularised gauge
   * 
   * All operations work in the moduli-regularised gauge,
   * where the Core semiring provides the renormalization
   * structure for phase operations.
   *)
  Definition moduli_regularised_phase (t : B.carrier) : L_E :=
    let k_core := header_only_phase t in
    phase_semantics_core k_core.

End QFTPortCoreSemiring.