module CLEAN.Core.Guard where

open import CLEAN.Core.Diagram using (_∘_; _⊗_)
open import CLEAN.Core.System using (guardNANDᵍ; guardNegᵍ; idL; tensorLᵍ; guardNANDDerived; _⇒ᶜ*_)

-- | Package the guarded NAND derivation as a reusable witness.
record GuardedDifference : Set where
  constructor mkGuardedDifference
  field
    witness : _⇒ᶜ*_ guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))

open GuardedDifference public

guardedDifferenceWitness : GuardedDifference
guardedDifferenceWitness =
  mkGuardedDifference guardNANDDerived
