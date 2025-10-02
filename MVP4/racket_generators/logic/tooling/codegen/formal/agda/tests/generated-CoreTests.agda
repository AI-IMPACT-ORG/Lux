module tests.generated-CoreTests where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

-- CLEAN v10 Core Mathematical Tests

-- Test 1: Basic Type Definitions
data TestSort : Set where
  L B R I : TestSort

-- Test 2: Simple Properties
test-reflexivity : ∀ {A : Set} (x : A) → x ≡ x
test-reflexivity x = refl

-- Test 3: Basic Logic
test-simple-function : Nat → Nat
test-simple-function n = n