module CLEAN.Tests.GuardedNegation where

open import CLEAN.Library

-- | Guarded NAND specialises to guarded negation of the local tensor.
local-guarded-nand : _⇒ᶜ*_ guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))
local-guarded-nand = guardNANDDerived
