-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - Test Entrypoint
--
-- PURPOSE: Public Tests entrypoint for Lux library
-- STATUS: Active - Public test interface
-- DEPENDENCIES: All test modules
--
-- Provides public access to all test suites

module Lux.Tests.Entrypoint where

open import Lux.Tests.Utils.ComprehensiveTestRunner
open import Lux.Tests.Utils.ExpandedTestRunner
open import Lux.Tests.Utils.EnhancedTestFramework

-- Main test runner for all expanded tests (V2 + V10 + Truth Theorems)
run-all-expanded-tests : TestSuiteResult
run-all-expanded-tests = run-expanded-test-suites

-- Test validation and monitoring
validate-all-tests : Bool
validate-all-tests = validate-enhanced-tests

-- Performance monitoring
monitor-test-performance : TestSuiteResult → String
monitor-test-performance = monitor-enhanced-test-performance

-- Test status summary
test-status-summary : String
test-status-summary = 
  let v2-result = run-all-v2-tests
      expanded-result = run-all-expanded-tests
      validation = validate-all-tests
  in 
    "V2 Tests: " ++ (if TestSuiteResult.all-passed v2-result then "PASSED" else "FAILED") ++
    " | Expanded Tests: " ++ (if TestSuiteResult.all-passed expanded-result then "PASSED" else "FAILED") ++
    " | Validation: " ++ (if validation then "PASSED" else "FAILED")

