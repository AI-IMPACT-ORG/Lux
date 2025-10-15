-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - V2 Axiom A2 Tests (Observer/Embedding System)
--
-- PURPOSE: Tests for V2 Axiom A2 - Observer/embedding system (ν_L, ν_R, ι_L, ι_R)
-- STATUS: Active - A2 observer/embedding tests
-- DEPENDENCIES: Lux.Core.Kernel, Lux.Tests.Utils.TestFramework
--
-- This module provides comprehensive tests for:
-- - Observer homomorphisms ν_L, ν_R with retraction properties
-- - Embedding homomorphisms ι_L, ι_R with injection properties
-- - Retraction properties: ν_L ∘ ι_L = id_L, ν_R ∘ ι_R = id_R
-- - Homomorphism properties: ν_*(t ⊕_B u) = ν_*(t) ⊕_* ν_*(u)
-- - Identity preservation: ν_L(0_B) = 0_L, ν_L(1_B) = 1_L, etc.
-- - Frobenius-style compatibility: ν_L(ι_L x ⊗_B t) = x ⊗_L ν_L(t)
-- - Cross-connector: ν_L(ι_R y) = 0_L, ν_R(ι_L x) = 0_R

{-# OPTIONS --cubical --without-K #-}

module Lux.Tests.Foundation.V2Axioms.A2Observers where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

open import Lux.Core.Kernel
open import Lux.Tests.Utils.TestFramework
open import Lux.Foundations.Types

-- ============================================================================
-- OBSERVER/EMBEDDING TESTS (A2)
-- ============================================================================

-- Test ν_L retraction property
test-nuL-retraction : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuL-retraction carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuL-retraction"
  ; description = "Test that ν_L ∘ ι_L = id_L"
  ; test-function = ∀ (x : TrialityCarriers.Left carriers) → 
    ObserverSystem.νL observers (ObserverSystem.ιL observers x) ≡ x
  ; expected-result = ObserverSystem.retraction-L observers
  ; timeout = 1000
  }

-- Test ν_R retraction property
test-nuR-retraction : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuR-retraction carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuR-retraction"
  ; description = "Test that ν_R ∘ ι_R = id_R"
  ; test-function = ∀ (x : TrialityCarriers.Right carriers) → 
    ObserverSystem.νR observers (ObserverSystem.ιR observers x) ≡ x
  ; expected-result = ObserverSystem.retraction-R observers
  ; timeout = 1000
  }

-- Test ν_L additive homomorphism
test-nuL-additive-homomorphism : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuL-additive-homomorphism carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuL-additive-homomorphism"
  ; description = "Test that ν_L preserves addition: ν_L(t ⊕_B u) = ν_L(t) ⊕_L ν_L(u)"
  ; test-function = ∀ (x y : TrialityCarriers.Bulk carriers) → 
    ObserverSystem.νL observers (BulkSemiring._⊕B_ bulk-semiring x y) ≡ 
    LeftSemiring._⊕L_ left-semiring (ObserverSystem.νL observers x) (ObserverSystem.νL observers y)
  ; expected-result = ObserverSystem.hom-L-add observers
  ; timeout = 1000
  }

-- Test ν_R additive homomorphism
test-nuR-additive-homomorphism : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuR-additive-homomorphism carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuR-additive-homomorphism"
  ; description = "Test that ν_R preserves addition: ν_R(t ⊕_B u) = ν_R(t) ⊕_R ν_R(u)"
  ; test-function = ∀ (x y : TrialityCarriers.Bulk carriers) → 
    ObserverSystem.νR observers (BulkSemiring._⊕B_ bulk-semiring x y) ≡ 
    RightSemiring._⊕R_ right-semiring (ObserverSystem.νR observers x) (ObserverSystem.νR observers y)
  ; expected-result = ObserverSystem.hom-R-add observers
  ; timeout = 1000
  }

-- Test ν_L multiplicative homomorphism
test-nuL-multiplicative-homomorphism : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuL-multiplicative-homomorphism carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuL-multiplicative-homomorphism"
  ; description = "Test that ν_L preserves multiplication: ν_L(t ⊗_B u) = ν_L(t) ⊗_L ν_L(u)"
  ; test-function = ∀ (x y : TrialityCarriers.Bulk carriers) → 
    ObserverSystem.νL observers (BulkSemiring._⊗B_ bulk-semiring x y) ≡ 
    LeftSemiring._⊗L_ left-semiring (ObserverSystem.νL observers x) (ObserverSystem.νL observers y)
  ; expected-result = ObserverSystem.hom-L-mult observers
  ; timeout = 1000
  }

-- Test ν_R multiplicative homomorphism
test-nuR-multiplicative-homomorphism : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuR-multiplicative-homomorphism carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuR-multiplicative-homomorphism"
  ; description = "Test that ν_R preserves multiplication: ν_R(t ⊗_B u) = ν_R(t) ⊗_R ν_R(u)"
  ; test-function = ∀ (x y : TrialityCarriers.Bulk carriers) → 
    ObserverSystem.νR observers (BulkSemiring._⊗B_ bulk-semiring x y) ≡ 
    RightSemiring._⊗R_ right-semiring (ObserverSystem.νR observers x) (ObserverSystem.νR observers y)
  ; expected-result = ObserverSystem.hom-R-mult observers
  ; timeout = 1000
  }

-- ============================================================================
-- IDENTITY PRESERVATION TESTS (A2)
-- ============================================================================

-- Test ν_L identity preservation
test-nuL-identity-preservation : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuL-identity-preservation carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuL-identity-preservation"
  ; description = "Test that ν_L preserves identities: ν_L(0_B) = 0_L, ν_L(1_B) = 1_L"
  ; test-function = 
    ObserverSystem.νL observers (BulkSemiring.zeroB bulk-semiring) ≡ LeftSemiring.zeroL left-semiring ∧
    ObserverSystem.νL observers (BulkSemiring.oneB bulk-semiring) ≡ LeftSemiring.oneL left-semiring
  ; expected-result = refl
  ; timeout = 1000
  }
  where
    _∧_ : Bool → Bool → Bool
    true ∧ true = true
    _ ∧ _ = false

-- Test ν_R identity preservation
test-nuR-identity-preservation : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-nuR-identity-preservation carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "nuR-identity-preservation"
  ; description = "Test that ν_R preserves identities: ν_R(0_B) = 0_R, ν_R(1_B) = 1_R"
  ; test-function = 
    ObserverSystem.νR observers (BulkSemiring.zeroB bulk-semiring) ≡ RightSemiring.zeroR right-semiring ∧
    ObserverSystem.νR observers (BulkSemiring.oneB bulk-semiring) ≡ RightSemiring.oneR right-semiring
  ; expected-result = refl
  ; timeout = 1000
  }
  where
    _∧_ : Bool → Bool → Bool
    true ∧ true = true
    _ ∧ _ = false

-- ============================================================================
-- FROBENIUS-STYLE COMPATIBILITY TESTS (A4)
-- ============================================================================

-- Test local faithfulness L
test-local-faithfulness-L : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-local-faithfulness-L carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "local-faithfulness-L"
  ; description = "Test Frobenius-style compatibility: ν_L(ι_L x ⊗_B t) = x ⊗_L ν_L(t)"
  ; test-function = ∀ (x : TrialityCarriers.Left carriers) (t : TrialityCarriers.Bulk carriers) → 
    ObserverSystem.νL observers (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x) t) ≡ 
    LeftSemiring._⊗L_ left-semiring x (ObserverSystem.νL observers t)
  ; expected-result = ObserverSystem.local-faithfulness-L observers
  ; timeout = 1000
  }

-- Test local faithfulness R
test-local-faithfulness-R : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-local-faithfulness-R carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "local-faithfulness-R"
  ; description = "Test Frobenius-style compatibility: ν_R(ι_R y ⊗_B t) = y ⊗_R ν_R(t)"
  ; test-function = ∀ (y : TrialityCarriers.Right carriers) (t : TrialityCarriers.Bulk carriers) → 
    ObserverSystem.νR observers (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιR observers y) t) ≡ 
    RightSemiring._⊗R_ right-semiring y (ObserverSystem.νR observers t)
  ; expected-result = ObserverSystem.local-faithfulness-R observers
  ; timeout = 1000
  }

-- ============================================================================
-- CROSS-CONNECTOR TESTS (A4)
-- ============================================================================

-- Test cross-connector L
test-cross-connector-L : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-cross-connector-L carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "cross-connector-L"
  ; description = "Test cross-connector: ν_L(ι_R y) = 0_L"
  ; test-function = ∀ (y : TrialityCarriers.Right carriers) → 
    ObserverSystem.νL observers (ObserverSystem.ιR observers y) ≡ LeftSemiring.zeroL left-semiring
  ; expected-result = ObserverSystem.cross-connector-L observers
  ; timeout = 1000
  }

-- Test cross-connector R
test-cross-connector-R : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-cross-connector-R carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "cross-connector-R"
  ; description = "Test cross-connector: ν_R(ι_L x) = 0_R"
  ; test-function = ∀ (x : TrialityCarriers.Left carriers) → 
    ObserverSystem.νR observers (ObserverSystem.ιL observers x) ≡ RightSemiring.zeroR right-semiring
  ; expected-result = ObserverSystem.cross-connector-R observers
  ; timeout = 1000
  }

-- ============================================================================
-- BULK EQUALS BOUNDARIES TEST (A2)
-- ============================================================================

-- Test bulk equals boundaries
test-bulk-equals-boundaries : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-bulk-equals-boundaries carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "bulk-equals-boundaries"
  ; description = "Test bulk decomposition: t = ι_L(ν_L(t)) ⊕_B ι_R(ν_R(t))"
  ; test-function = ∀ (t : TrialityCarriers.Bulk carriers) → 
    t ≡ BulkSemiring._⊕B_ bulk-semiring 
      (ObserverSystem.ιL observers (ObserverSystem.νL observers t)) 
      (ObserverSystem.ιR observers (ObserverSystem.νR observers t))
  ; expected-result = ObserverSystem.bulk-equals-boundaries observers
  ; timeout = 1000
  }

-- ============================================================================
-- A2 OBSERVER/EMBEDDING TEST SUITE
-- ============================================================================

-- Complete A2 observer/embedding test suite
a2-observers-test-suite : ∀ (core-kernel : CoreKernelStructure) → TestSuite
a2-observers-test-suite core-kernel = record
  { suite-name = "A2-Observer-Embedding-System"
  ; test-cases = 
    -- Retraction tests
    test-nuL-retraction (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-nuR-retraction (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Homomorphism tests
    test-nuL-additive-homomorphism (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-nuR-additive-homomorphism (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-nuL-multiplicative-homomorphism (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-nuR-multiplicative-homomorphism (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Identity preservation tests
    test-nuL-identity-preservation (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-nuR-identity-preservation (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Frobenius-style compatibility tests
    test-local-faithfulness-L (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-local-faithfulness-R (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Cross-connector tests
    test-cross-connector-L (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-cross-connector-R (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Bulk decomposition test
    test-bulk-equals-boundaries (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    []
  ; dependencies = ["Lux.Core.Kernel", "Lux.Tests.Utils.TestFramework"]
  ; timeout = 5000
  }
