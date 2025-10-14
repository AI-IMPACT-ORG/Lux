-- Simple test to check compilation
module Lux.Tests.SimpleTest where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

-- Define our own natural numbers
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- Simple test case
record SimpleTestCase : Set where
  field
    name : String
    value : ℕ

-- Simple test suite
record SimpleTestSuite : Set where
  field
    suite-name : String
    test-cases : List SimpleTestCase
    timeout : ℕ

-- Test function
test-function : SimpleTestSuite
test-function = record
  { suite-name = "Simple Test"
  ; test-cases = []
  ; timeout = suc zero
  }
