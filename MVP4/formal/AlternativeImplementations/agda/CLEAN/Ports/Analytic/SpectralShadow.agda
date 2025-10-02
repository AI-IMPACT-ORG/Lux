module CLEAN.Ports.Analytic.SpectralShadow where

-- | Minimal "spectral" summary for LogicalZeta bundles.  It captures the data
--   that future kernel/domain-map work cares about (growth/decay and Δ-flow)
--   without committing to any heavy arithmetic semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤)

open import CLEAN.Core.NormalForm
open import CLEAN.Core.Dirichlet
open import CLEAN.Ports.Analytic.ZetaDefinition

open LogicalZeta
open GrowthDecayControl

------------------------------------------------------------------------
-- Minimal spectral shadow for LogicalZeta objects.
------------------------------------------------------------------------

record KernelSpectralShadow : Set₁ where
  constructor mkShadow
  field
    Carrier           : Set
    control           : GrowthDecayControl
    dirichletSpectrum : Regulator → Carrier
    eulerSpectrum     : Regulator → Carrier
    boundsWitness     : ∀ r → Σ (Regulator.lambda r ≥ decayBound control r)
                               (λ _ → growthBound control r ≥ Regulator.lambda r)
    deltaSpectral     : ∀ r → dirichletSpectrum r ≡ eulerSpectrum r

open KernelSpectralShadow public

-- | Repackages a logical zeta bundle using the identity carrier.
canonicalShadow : LogicalZeta → KernelSpectralShadow
canonicalShadow ζ = mkShadow
  (NormalForm ⊤)
  (growthDecayControl ζ)
  (λ r → DeltaNF (evaluateSeries (dirichletSeries ζ r) r))
  (λ r → evaluateSeries (eulerSeries ζ r) r)
  (regulatorBounds (growthDecayControl ζ))
  (deltaAgreement ζ)
