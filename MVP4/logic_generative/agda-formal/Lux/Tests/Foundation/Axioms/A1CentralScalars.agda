-- Lux Logic System - V2 Axiom A1 Tests (Central Scalars)
--
-- PURPOSE: Tests for V2 Axiom A1 - Central scalars (φ, z, \bar{z}, Λ)
-- STATUS: Active - A1 central scalars tests
-- DEPENDENCIES: Lux.Core.Kernel, Lux.Tests.Utils.TestFramework
--
-- This module provides comprehensive tests for:
-- - Central scalars φ, z, \bar{z} with centrality properties
-- - Λ definition: Λ := z ⊗_B \bar{z}
-- - Unit properties for all central scalars
-- - Commutativity with bulk operations

{-# OPTIONS --cubical --without-K #-}

module Lux.Tests.Foundation.V2Axioms.A1CentralScalars where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

open import Lux.Core.Kernel
open import Lux.Tests.Utils.TestFramework
open import Lux.Foundations.Types

-- ============================================================================
-- CENTRAL SCALARS TESTS (A1)
-- ============================================================================

-- Test φ centrality
test-phi-centrality : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-phi-centrality carriers bulk-semiring central-scalars = record
  { name = "phi-centrality"
  ; description = "Test that φ is central for bulk multiplication"
  ; test-function = ∀ (x : TrialityCarriers.Bulk carriers) → 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.φ central-scalars) x ≡ 
    BulkSemiring._⊗B_ bulk-semiring x (CentralScalars.φ central-scalars)
  ; expected-result = CentralScalars.φ-central central-scalars
  ; timeout = 1000
  }

-- Test z centrality
test-z-centrality : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-z-centrality carriers bulk-semiring central-scalars = record
  { name = "z-centrality"
  ; description = "Test that z is central for bulk multiplication"
  ; test-function = ∀ (x : TrialityCarriers.Bulk carriers) → 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.z central-scalars) x ≡ 
    BulkSemiring._⊗B_ bulk-semiring x (CentralScalars.z central-scalars)
  ; expected-result = CentralScalars.z-central central-scalars
  ; timeout = 1000
  }

-- Test z̄ centrality
test-zbar-centrality : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-zbar-centrality carriers bulk-semiring central-scalars = record
  { name = "zbar-centrality"
  ; description = "Test that z̄ is central for bulk multiplication"
  ; test-function = ∀ (x : TrialityCarriers.Bulk carriers) → 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.z̄ central-scalars) x ≡ 
    BulkSemiring._⊗B_ bulk-semiring x (CentralScalars.z̄ central-scalars)
  ; expected-result = CentralScalars.z̄-central central-scalars
  ; timeout = 1000
  }

-- Test Λ centrality
test-lambda-centrality : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-lambda-centrality carriers bulk-semiring central-scalars = record
  { name = "lambda-centrality"
  ; description = "Test that Λ is central for bulk multiplication"
  ; test-function = ∀ (x : TrialityCarriers.Bulk carriers) → 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.Λ central-scalars) x ≡ 
    BulkSemiring._⊗B_ bulk-semiring x (CentralScalars.Λ central-scalars)
  ; expected-result = CentralScalars.Λ-central central-scalars
  ; timeout = 1000
  }

-- Test Λ definition
test-lambda-definition : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-lambda-definition carriers bulk-semiring central-scalars = record
  { name = "lambda-definition"
  ; description = "Test that Λ is defined as z ⊗_B z̄"
  ; test-function = CentralScalars.Λ central-scalars ≡ 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.z central-scalars) (CentralScalars.z̄ central-scalars)
  ; expected-result = CentralScalars.Λ-definition central-scalars
  ; timeout = 1000
  }

-- ============================================================================
-- UNIT PROPERTIES TESTS (A1)
-- ============================================================================

-- Test φ unit properties
test-phi-unit-properties : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-phi-unit-properties carriers bulk-semiring central-scalars = record
  { name = "phi-unit-properties"
  ; description = "Test that φ has proper unit properties"
  ; test-function = 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.φ central-scalars) (BulkSemiring.oneB bulk-semiring) ≡ CentralScalars.φ central-scalars ∧
    BulkSemiring._⊗B_ bulk-semiring (BulkSemiring.oneB bulk-semiring) (CentralScalars.φ central-scalars) ≡ CentralScalars.φ central-scalars
  ; expected-result = refl
  ; timeout = 1000
  }
  where
    _∧_ : Bool → Bool → Bool
    true ∧ true = true
    _ ∧ _ = false

-- Test z unit properties
test-z-unit-properties : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-z-unit-properties carriers bulk-semiring central-scalars = record
  { name = "z-unit-properties"
  ; description = "Test that z has proper unit properties"
  ; test-function = 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.z central-scalars) (BulkSemiring.oneB bulk-semiring) ≡ CentralScalars.z central-scalars ∧
    BulkSemiring._⊗B_ bulk-semiring (BulkSemiring.oneB bulk-semiring) (CentralScalars.z central-scalars) ≡ CentralScalars.z central-scalars
  ; expected-result = refl
  ; timeout = 1000
  }
  where
    _∧_ : Bool → Bool → Bool
    true ∧ true = true
    _ ∧ _ = false

-- Test z̄ unit properties
test-zbar-unit-properties : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-zbar-unit-properties carriers bulk-semiring central-scalars = record
  { name = "zbar-unit-properties"
  ; description = "Test that z̄ has proper unit properties"
  ; test-function = 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.z̄ central-scalars) (BulkSemiring.oneB bulk-semiring) ≡ CentralScalars.z̄ central-scalars ∧
    BulkSemiring._⊗B_ bulk-semiring (BulkSemiring.oneB bulk-semiring) (CentralScalars.z̄ central-scalars) ≡ CentralScalars.z̄ central-scalars
  ; expected-result = refl
  ; timeout = 1000
  }
  where
    _∧_ : Bool → Bool → Bool
    true ∧ true = true
    _ ∧ _ = false

-- Test Λ unit properties
test-lambda-unit-properties : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) → TestCase
test-lambda-unit-properties carriers bulk-semiring central-scalars = record
  { name = "lambda-unit-properties"
  ; description = "Test that Λ has proper unit properties"
  ; test-function = 
    BulkSemiring._⊗B_ bulk-semiring (CentralScalars.Λ central-scalars) (BulkSemiring.oneB bulk-semiring) ≡ CentralScalars.Λ central-scalars ∧
    BulkSemiring._⊗B_ bulk-semiring (BulkSemiring.oneB bulk-semiring) (CentralScalars.Λ central-scalars) ≡ CentralScalars.Λ central-scalars
  ; expected-result = refl
  ; timeout = 1000
  }
  where
    _∧_ : Bool → Bool → Bool
    true ∧ true = true
    _ ∧ _ = false

-- ============================================================================
-- A1 CENTRAL SCALARS TEST SUITE
-- ============================================================================

-- Complete A1 central scalars test suite
a1-central-scalars-test-suite : ∀ (core-kernel : CoreKernelStructure) → TestSuite
a1-central-scalars-test-suite core-kernel = record
  { suite-name = "A1-Central-Scalars"
  ; test-cases = 
    -- Centrality tests
    test-phi-centrality (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    test-z-centrality (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    test-zbar-centrality (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    test-lambda-centrality (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    -- Definition tests
    test-lambda-definition (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    -- Unit property tests
    test-phi-unit-properties (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    test-z-unit-properties (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    test-zbar-unit-properties (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    test-lambda-unit-properties (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) ∷
    []
  ; dependencies = ["Lux.Core.Kernel", "Lux.Tests.Utils.TestFramework"]
  ; timeout = 5000
  }
