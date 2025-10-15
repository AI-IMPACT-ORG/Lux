module CLEAN.Tests.Braiding where

open import CLEAN.Library

-- | Braiding on bulk wires is an involution.
braid-involutive : _⇒ᶜ*_ (braidBBᵍ ∘ braidBBᵍ) idBB
braid-involutive = braidInvolutive
