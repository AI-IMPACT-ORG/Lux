module tests.CoreTests where

open import lib.generated-Core
open import lib.generated-Observers
open import lib.generated-Kernels
open import lib.generated-NormalForms
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

-- CLEAN v10 Core Mathematical Tests

-- Test 1: Header Mathematics
test-header-addition : Header
test-header-addition = header-add (header 1.0 2.0) (header 3.0 4.0)

test-header-addition-correct : test-header-addition ≡ header 4.0 6.0
test-header-addition-correct = refl

test-header-multiplication : Header
test-header-multiplication = header-multiply (header 1.0 2.0) (header 3.0 4.0)

test-header-multiplication-correct : test-header-multiplication ≡ header 3.0 8.0
test-header-multiplication-correct = refl

-- Test 2: Observer Functions
test-observer-value : Term → Term
test-observer-value = observer-value

-- Test 3: Property-Based Testing
test-header-commutativity : ∀ h1 h2 → header-add h1 h2 ≡ header-add h2 h1
test-header-commutativity h1 h2 = refl

test-header-associativity : ∀ h1 h2 h3 → header-add (header-add h1 h2) h3 ≡ header-add h1 (header-add h2 h3)
test-header-associativity h1 h2 h3 = refl