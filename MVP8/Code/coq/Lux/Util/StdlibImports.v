(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

(** 
 * Semantic Standard Library Imports
 * 
 * This module provides a centralized location for standard library imports
 * organized by their semantic mapping to the Lux semiring structure.
 * 
 * Semantic Mapping:
 * - ZArith → Core Semiring (integer arithmetic for header operations)
 * - Init.Nat → L Semiring (natural numbers for indexing and counting)
 * - Bool → R Semiring (Boolean logic for decision-making and control flow)
 * - List → B Semiring (lists for Feynman path integrals and complex structures)
 * 
 * Usage: From Lux.Util Require Import StdlibImports.
 *)

From Coq Require Import ZArith.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.
From Coq Require Import List.

(* Re-export commonly used modules for convenience *)
Export ZArith.
Export List.
Export Bool.