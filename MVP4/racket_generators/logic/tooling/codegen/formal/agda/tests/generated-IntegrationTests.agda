module tests.generated-IntegrationTests where

open import lib.Core
open import lib.Observers
open import Agda.Builtin.Equality

-- CLEAN v10 Integration Tests

-- Test: End-to-end workflow
test-end-to-end : Term
test-end-to-end = observer-value (make-term 'test-term (header 2.0 3.0) 'test-core)

test-end-to-end-correct : test-end-to-end ≡ make-term 'test-term (header 2.0 3.0) 'test-core
test-end-to-end-correct = refl