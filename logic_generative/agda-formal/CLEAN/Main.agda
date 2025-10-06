-- CLEAN V2/V10 Main Module - Agda Formalization
--
-- PURPOSE: Main module for CLEAN V2 atomic system and V10 integration
-- STATUS: Active - Complete formal verification system
-- DEPENDENCIES: All CLEAN modules
--
-- This module provides:
-- - Complete V2 atomic system
-- - V10 machine derivations
-- - Comprehensive test suite
-- - Formal verification validation
-- - System integration

{-# OPTIONS --cubical #-}

module CLEAN.Main where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

open import CLEAN.V2.Atomic
open import CLEAN.V2.Tests.UnitTests
open import CLEAN.V10.Shell
open import CLEAN.V10.Tests.IntegrationTests
open import CLEAN.Tests.TestRunner

record CLEANSystem : Set₁ where
  field
    v2-foundation : V2Foundation
    v10-class-system : V10ClassSystem

initialize-v2-foundation : V2Foundation
initialize-v2-foundation = v2-foundation-default

initialize-v10-class-system : V10ClassSystem
initialize-v10-class-system = v10-class-default

initialize-clean-system : CLEANSystem
initialize-clean-system = record
  { v2-foundation = initialize-v2-foundation
  ; v10-class-system = initialize-v10-class-system
  }
