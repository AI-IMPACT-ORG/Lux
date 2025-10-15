(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

(** 
 * Module Instantiation Helper
 * 
 * This module provides a standard set of module instantiations
 * to reduce boilerplate across all Lux modules.
 *)

From Lux.Core Require Import Signature Axioms Observers NF Triality Cumulants.
From Lux.Class Require Import Moduli Guarded PSDM Feynman.

Module LuxModuleInstantiations (S:LuxSignature).
  Module Ax := Axioms(S).
  Module Obs := Observers(S).
  Module N := NF(S).
  Module T := Triality(S).
  Module Cum := Cumulants(S).
  Module Mod := Moduli(S).
  Module Guarded := GuardedNegation(S).
  Module PSDM := PSDM(S).
  Module Feynman := Feynman(S).
  
  Module L := S.L.
  Module R := S.R.
  Module B := S.B.
  Module Core := S.Core.
End LuxModuleInstantiations.
