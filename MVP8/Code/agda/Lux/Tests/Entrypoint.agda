-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - Test Entrypoint
--
-- PURPOSE: Public Tests entrypoint for Lux library
-- STATUS: Active - Public test interface
-- DEPENDENCIES: All test modules
--
-- Provides public access to all test suites

{-# OPTIONS --cubical --without-K #-}

module Lux.Tests.Entrypoint where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import Lux.Foundations.Types
open import Lux.Core.Kernel
open import Lux.Tests.Utils.ComprehensiveTestRunner
open import Lux.Tests.Utils.ExpandedTestRunner
open import Lux.Tests.Utils.EnhancedTestFramework

-- Main test runner for all expanded tests (Lux Axioms + Lux Core + Lux Ops + Truth Theorems)
run-all-expanded-tests-entrypoint : ∀ (core-kernel : CoreKernelStructure) → List EnhancedTestSuite
run-all-expanded-tests-entrypoint = expanded-test-suites

-- Test validation and monitoring
validate-all-tests-entrypoint : List TestSuiteResult → Bool
validate-all-tests-entrypoint = validate-enhanced-tests

-- Performance monitoring
monitor-test-performance-entrypoint : List TestSuiteResult → ℕ
monitor-test-performance-entrypoint = monitor-enhanced-test-performance

-- Test status summary
test-status-summary : String
test-status-summary = "Test Status Summary Available"

