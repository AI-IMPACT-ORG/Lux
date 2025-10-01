module CLEAN.Ports.Analytic.Conjugation where

open import Agda.Builtin.Equality using (_≡_; refl)

open import CLEAN.Ports.Analytic

logicalStar : NumberPair → NumberPair
logicalStar = swapPair

classicalConjugation : NumberPair → NumberPair
classicalConjugation = swapPair

star-agrees : ∀ p → logicalStar p ≡ classicalConjugation p
star-agrees _ = refl

star-operator-agrees : ∀ p → StarOperator.star swapStar p ≡ classicalConjugation p
star-operator-agrees _ = refl
