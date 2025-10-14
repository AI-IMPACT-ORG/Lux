(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms Observers NF.
From Lux.Class Require Import PSDM Guarded.

Module InfoFlowPort (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module N := NF(S).
  Module PSDM := PSDM(S).
  Module Guarded := GuardedNegation(S).
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.

  (* Preorders/lattices *)
  Parameter preorder : L.carrier -> L.carrier -> Prop.
  Axiom preorder_refl : forall x, preorder x x.
  Axiom preorder_trans : forall x y z,
    preorder x y -> preorder y z -> preorder x z.

  (* Join operation *)
  Definition join (x y : L.carrier) : L.carrier := L.add x y.
  Axiom join_upper_bound : forall x y,
    preorder x (join x y) /\ preorder y (join x y).

  (* Flow operation *)
  Definition flow (x y : L.carrier) : L.carrier := L.mul x y.
  Axiom flow_monotone : forall x y z,
    preorder x y -> preorder (flow x z) (flow y z).

  (* Guarded negation yields relative complement *)
  Definition relative_complement (x : L.carrier) : L.carrier :=
    Guarded.guarded_not x.

  Axiom relative_complement_property : forall x,
    L.add x (relative_complement x) = Guarded.guard.

  (* PSDM drops non-flow paths *)
  Definition infoflow_PSDM (t : B.carrier) : option L.carrier :=
    match PSDM.PSDM_B t with
    | Some _ => Some (S.nuL (N.NF_B t))
    | None => None
    end.

  (* Irreversible information *)
  Axiom infoflow_irreversible : forall t t',
    infoflow_PSDM t = Some (S.nuL (N.NF_B t)) ->
    infoflow_PSDM t' = Some (S.nuL (N.NF_B t')) ->
    preorder (S.nuL (N.NF_B t)) (S.nuL (N.NF_B t')) ->
    exists path, flow (S.nuL (N.NF_B t)) path = S.nuL (N.NF_B t').

End InfoFlowPort.

