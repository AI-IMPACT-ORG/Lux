-- Lux Logic System - Main Module
--
-- PURPOSE: Main module for Lux V2 atomic system and V10 integration
-- STATUS: Active - Complete formal verification system
-- DEPENDENCIES: All Lux modules
--
-- Provides:
-- - Complete V2 atomic system
-- - V10 machine derivations
-- - Comprehensive test suite
-- - Formal verification validation
-- - System integration

{-# OPTIONS --cubical #-}

module Lux.Main where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Lux.V2.Atomic
open import Lux.V2.Tests.UnitTests
open import Lux.V10.Shell
open import Lux.V10.Tests.IntegrationTests
open import Lux.Tests.TestRunner

record LuxSystem : Set₁ where
  field
    v2-foundation : V2Foundation
    v10-class-system : V10ClassSystem

initialize-v2-foundation : V2Foundation
initialize-v2-foundation = v2-foundation-default

initialize-v10-class-system : V10ClassSystem
initialize-v10-class-system = v10-class-default

initialize-clean-system : LuxSystem
initialize-clean-system = record
  { v2-foundation = initialize-v2-foundation
  ; v10-class-system = initialize-v10-class-system
  }
