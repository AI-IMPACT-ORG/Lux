module CLEAN.Tests.Comprehensive where

open import Agda.Builtin.Sigma using (Σ; _,_)

open import CLEAN.Library
open import CLEAN.Tests.API public
open import CLEAN.Tests.Institutional public
open import CLEAN.Tests.Subinstitution public
open import CLEAN.Tests.GuardedNegation public

-- | Bundle key boundary retraction certificates for convenient reuse.
comprehensive-boundary-consistency
  : Σ (_⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL) λ _ → _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
comprehensive-boundary-consistency = (retractLId , retractRId)
