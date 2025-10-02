module tests.TestRunner where

open import tests.CoreTests
open import tests.PropertyTests
open import tests.IntegrationTests

-- CLEAN v10 Test Runner

-- Run all tests
run-all-tests : Set
run-all-tests = test-header-addition-correct