module CLEAN.Tests.Institutional where

open import CLEAN.Library

-- | Institutional invariant: left observer sees the recombined bulk as expected.
institutional-triality-left : _⇒ᶜ_ (νLᵍ ∘ trialityBᵍ)
                                       (νLᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ)))
institutional-triality-left = trialityLeftSound

-- | Institutional invariant: right observer behaves symmetrically.
institutional-triality-right : _⇒ᶜ_ (νRᵍ ∘ trialityBᵍ)
                                        (νRᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ)))
institutional-triality-right = trialityRightSound
