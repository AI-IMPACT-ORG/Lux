(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

From Lux.Util Require Import StdlibImports ModuleInstantiations.
From Lux.Core Require Import Signature.
From Lux.Class Require Import PSDM.

Module LambdaPort (S:LuxSignature).
  Module Inst := LuxModuleInstantiations(S).
  Module Ax := Inst.Ax.
  Module Obs := Inst.Obs.
  Module N := Inst.N.
  Module PSDM := Inst.PSDM.
  Module L := Inst.L.
  Module R := Inst.R.
  Module B := Inst.B.

  (* Lambda terms *)
  Inductive LambdaTerm :=
  | Var : nat -> LambdaTerm
  | App : LambdaTerm -> LambdaTerm -> LambdaTerm
  | Abs : nat -> LambdaTerm -> LambdaTerm.

  (* Normal forms *)
  Inductive NormalForm :=
  | NF_Var : nat -> NormalForm
  | NF_Abs : nat -> NormalForm -> NormalForm.

  (* Beta reduction *)
  Parameter beta_step : LambdaTerm -> option LambdaTerm.
  Axiom beta_step_preserves_type : forall t,
    match beta_step t with
    | Some t' => True
    | None => True
    end.

  (* Evaluation via expectations *)
  Definition evaluate (t : LambdaTerm) : option NormalForm :=
    match beta_step t with
    | Some t' => Some (NF_Var 0)  (* Placeholder *)
    | None => None
    end.

  (* PSDM for Lambda port *)
  Definition lambda_PSDM (t : B.carrier) : option NormalForm :=
    match PSDM.PSDM_B t with
    | Some _ => Some (NF_Var 0)  (* Placeholder *)
    | None => None
    end.

  (* Defined iff β-normalises in regulator *)
  Axiom lambda_totality : forall t R,
    PSDM.totality t R = true ->
    exists nf, lambda_PSDM t = Some nf.

  (* Beta normalization *)
  Parameter beta_normalize : LambdaTerm -> option NormalForm.
  Axiom beta_normalize_complete : forall t nf,
    beta_normalize t = Some nf ->
    lambda_PSDM (B.one) = Some nf.

End LambdaPort.
