module CLEAN.Tests.Subinstitution where

open import CLEAN.Library

-- | Subinstitution lemma: conjugation commutes with the left embedding.
subinst-conj-embedL : _⇒ᶜ*_ (conjBᵍ ∘ ιLᵍ) (ιLᵍ ∘ conjLᵍ)
subinst-conj-embedL = conjEmbedL

-- | Subinstitution lemma: conjugation commutes with the right embedding.
subinst-conj-embedR : _⇒ᶜ*_ (conjBᵍ ∘ ιRᵍ) (ιRᵍ ∘ conjRᵍ)
subinst-conj-embedR = conjEmbedR

-- | Subinstitution lemma: conjugation respects the left observer.
subinst-conj-observeL : _⇒ᶜ*_ (νLᵍ ∘ conjBᵍ) (conjLᵍ ∘ νLᵍ)
subinst-conj-observeL = conjObserveL

-- | Subinstitution lemma: conjugation respects the right observer.
subinst-conj-observeR : _⇒ᶜ*_ (νRᵍ ∘ conjBᵍ) (conjRᵍ ∘ νRᵍ)
subinst-conj-observeR = conjObserveR
