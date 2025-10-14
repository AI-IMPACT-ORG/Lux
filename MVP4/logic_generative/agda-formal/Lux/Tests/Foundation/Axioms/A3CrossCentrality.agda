-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - V2 Axiom A3 Tests (Cross-Centrality and Independence)
--
-- PURPOSE: Tests for V2 Axiom A3 - Cross-centrality and independence
-- STATUS: Active - A3 cross-centrality tests
-- DEPENDENCIES: Lux.Core.Kernel, Lux.Tests.Utils.TestFramework
--
-- This module provides comprehensive tests for:
-- - Images commute multiplicatively: ι_L(x) ⊗_B ι_R(y) = ι_R(y) ⊗_B ι_L(x)
-- - Cross-centrality properties
-- - Independence between left and right contributions

{-# OPTIONS --cubical --without-K #-}

module Lux.Tests.Foundation.V2Axioms.A3CrossCentrality where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)

open import Lux.Core.Kernel
open import Lux.Tests.Utils.TestFramework
open import Lux.Foundations.Types

-- ============================================================================
-- CROSS-CENTRALITY TESTS (A3)
-- ============================================================================

-- Test cross-centrality (images commute multiplicatively)
test-cross-centrality : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-cross-centrality carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "cross-centrality"
  ; description = "Test that images commute multiplicatively: ι_L(x) ⊗_B ι_R(y) = ι_R(y) ⊗_B ι_L(x)"
  ; test-function = ∀ (x : TrialityCarriers.Left carriers) (y : TrialityCarriers.Right carriers) → 
    BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x) (ObserverSystem.ιR observers y) ≡ 
    BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιR observers y) (ObserverSystem.ιL observers x)
  ; timeout = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  }

-- Test left-right independence (additive)
test-left-right-independence-additive : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-left-right-independence-additive carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "left-right-independence-additive"
  ; description = "Test that left and right contributions are independent under addition"
  ; test-function = ∀ (x₁ x₂ : TrialityCarriers.Left carriers) (y₁ y₂ : TrialityCarriers.Right carriers) → 
    BulkSemiring._⊕B_ bulk-semiring 
      (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x₁) (ObserverSystem.ιR observers y₁))
      (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x₂) (ObserverSystem.ιR observers y₂)) ≡
    BulkSemiring._⊗B_ bulk-semiring 
      (ObserverSystem.ιL observers (LeftSemiring._⊕L_ left-semiring x₁ x₂))
      (ObserverSystem.ιR observers (RightSemiring._⊕R_ right-semiring y₁ y₂))
  ; timeout = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  }

-- Test left-right independence (multiplicative)
test-left-right-independence-multiplicative : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-left-right-independence-multiplicative carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "left-right-independence-multiplicative"
  ; description = "Test that left and right contributions are independent under multiplication"
  ; test-function = ∀ (x₁ x₂ : TrialityCarriers.Left carriers) (y₁ y₂ : TrialityCarriers.Right carriers) → 
    BulkSemiring._⊗B_ bulk-semiring 
      (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x₁) (ObserverSystem.ιR observers y₁))
      (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x₂) (ObserverSystem.ιR observers y₂)) ≡
    BulkSemiring._⊗B_ bulk-semiring 
      (ObserverSystem.ιL observers (LeftSemiring._⊗L_ left-semiring x₁ x₂))
      (ObserverSystem.ιR observers (RightSemiring._⊗R_ right-semiring y₁ y₂))
  ; timeout = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  }

-- Test cross-centrality with central scalars
test-cross-centrality-with-central-scalars : ∀ (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) (central-scalars : CentralScalars carriers bulk-semiring) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-cross-centrality-with-central-scalars carriers bulk-semiring central-scalars left-semiring right-semiring observers = record
  { name = "cross-centrality-with-central-scalars"
  ; description = "Test that cross-centrality works with central scalars"
  ; test-function = ∀ (x : TrialityCarriers.Left carriers) (y : TrialityCarriers.Right carriers) → 
    BulkSemiring._⊗B_ bulk-semiring 
      (BulkSemiring._⊗B_ bulk-semiring (CentralScalars.φ central-scalars) (ObserverSystem.ιL observers x))
      (ObserverSystem.ιR observers y) ≡
    BulkSemiring._⊗B_ bulk-semiring 
      (ObserverSystem.ιR observers y)
      (BulkSemiring._⊗B_ bulk-semiring (CentralScalars.φ central-scalars) (ObserverSystem.ιL observers x))
  ; timeout = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  }

-- Test cross-centrality associativity
test-cross-centrality-associativity : ∀ (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) (observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring) → TestCase
test-cross-centrality-associativity carriers left-semiring right-semiring bulk-semiring observers = record
  { name = "cross-centrality-associativity"
  ; description = "Test associativity of cross-centrality operations"
  ; test-function = ∀ (x₁ x₂ : TrialityCarriers.Left carriers) (y₁ y₂ : TrialityCarriers.Right carriers) → 
    BulkSemiring._⊗B_ bulk-semiring 
      (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x₁) (ObserverSystem.ιR observers y₁))
      (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x₂) (ObserverSystem.ιR observers y₂)) ≡
    BulkSemiring._⊗B_ bulk-semiring 
      (ObserverSystem.ιL observers x₁)
      (BulkSemiring._⊗B_ bulk-semiring 
        (ObserverSystem.ιR observers y₁)
        (BulkSemiring._⊗B_ bulk-semiring (ObserverSystem.ιL observers x₂) (ObserverSystem.ιR observers y₂)))
  ; timeout = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  }

-- ============================================================================
-- A3 CROSS-CENTRALITY TEST SUITE
-- ============================================================================

-- Complete A3 cross-centrality test suite
a3-cross-centrality-test-suite : ∀ (core-kernel : CoreKernelStructure) → TestSuite
a3-cross-centrality-test-suite core-kernel = record
  { suite-name = "A3-Cross-Centrality-Independence"
  ; test-cases = 
    -- Cross-centrality tests
    test-cross-centrality (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Independence tests
    test-left-right-independence-additive (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    test-left-right-independence-multiplicative (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Central scalars integration tests
    test-cross-centrality-with-central-scalars (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.central-scalars core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    -- Associativity tests
    test-cross-centrality-associativity (CoreKernelStructure.carriers core-kernel) (CoreKernelStructure.left-semiring core-kernel) (CoreKernelStructure.right-semiring core-kernel) (CoreKernelStructure.bulk-semiring core-kernel) (CoreKernelStructure.observers core-kernel) ∷
    []
  ; dependencies = ["Lux.Core.Kernel", "Lux.Tests.Utils.TestFramework"]
  ; timeout = suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
  }
