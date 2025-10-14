(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

From Coq Require Import ZArith.
From Lux.Core Require Import Signature Axioms Observers NF.

Module PSDM (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
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

  (* PSDM definition *)
  Parameter PSDM_L : L.carrier -> option L.carrier.
  Parameter PSDM_B : B.carrier -> option B.carrier.
  Parameter PSDM_R : R.carrier -> option R.carrier.

  (* Totality predicate *)
  Parameter totality : B.carrier -> Regulator -> bool.
  Axiom totality_implies_defined : forall t R,
    totality t R = true ->
    exists v, PSDM_B t = Some v.

  (* Stability under regulator inclusions *)
  Axiom stability : forall t R1 R2,
    R1.(N) <= R2.(N) ->
    R1.(K) <= R2.(K) ->
    R1.(M) <= R2.(M) ->
    totality t R1 = true ->
    totality t R2 = true.

  (* Commutation with NF *)
  Axiom PSDM_commutes_NF : forall t R,
    totality t R = true ->
    match PSDM_B t, PSDM_B (N.NF_B t) with
    | Some v1, Some v2 => v1 = v2
    | None, None => True
    | _, _ => False
    end.

  (* Commutation with observers *)
  Axiom PSDM_commutes_nuL : forall t R,
    totality t R = true ->
    match PSDM_B t, PSDM_L (S.nuL t) with
    | Some v1, Some v2 => S.nuL v1 = v2
    | None, None => True
    | _, _ => False
    end.

  Axiom PSDM_commutes_nuR : forall t R,
    totality t R = true ->
    match PSDM_B t, PSDM_R (S.nuR t) with
    | Some v1, Some v2 => S.nuR v1 = v2
    | None, None => True
    | _, _ => False
    end.

  (* Partiality in direct limit *)
  Axiom partiality_limit : forall t,
    (forall R, totality t R = false) ->
    PSDM_B t = None.

  (* Continuity when RG is contractive *)
  Parameter RG_contractive : Prop.
  Axiom continuity : RG_contractive ->
    forall t R, totality t R = true ->
    exists v, PSDM_B t = Some v.

End PSDM.
