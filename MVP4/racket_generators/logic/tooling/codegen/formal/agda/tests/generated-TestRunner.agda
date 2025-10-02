module tests.generated-TestRunner where

open import tests.generated-CoreTests
open import tests.generated-PropertyTests
open import tests.generated-IntegrationTests

-- CLEAN v10 Test Runner

-- Run all tests
run-all-tests : Set
run-all-tests = test-header-addition-correct