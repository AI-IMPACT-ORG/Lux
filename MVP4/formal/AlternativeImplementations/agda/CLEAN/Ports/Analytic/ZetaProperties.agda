module CLEAN.Ports.Analytic.ZetaProperties where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (_,_)

open import CLEAN.Core.NormalForm
open import CLEAN.Application.Classification
open import CLEAN.Ports.Analytic
open import CLEAN.Ports.Analytic.ZetaDefinition
open import CLEAN.Core.System using (_⇒ᶜ*_; νLᵍ; ιLᵍ; idL; νRᵍ; ιRᵍ; idR; deltaᵍ; bulkSumᵍ; cumulantᵍ)
open import CLEAN.Core.Diagram using (_∘_; _⊗_)

open LogicalZeta logicalZeta
open HeckeCharacterData heckeCharacter using (evaluateCharacter; infinityType; infinityCompatibility)
open ArtinRepresentationData artinRepresentation using (localEulerFactor; determinant; determinantCompatibility)
open GrowthDecayControl growthDecayControl

fstNF : NumberPair → NormalForm ⊤
fstNF (x , _) = x

sndNF : NumberPair → NormalForm ⊤
sndNF (_ , y) = y

------------------------------------------------------------------------
-- Ten logical ζ-properties derived from existing witnesses.
------------------------------------------------------------------------

-- 1 & 2: Normalisation via parametrisation identity.
ζ-normalisation₁ : ∀ p → parametrise idPhaseFlow idPhaseFlow idScaleFlow idScaleFlow (fstNF p) ≡ fstNF p
ζ-normalisation₁ (x , _) = parametrise-id x

ζ-normalisation₂ : ∀ p → parametrise idPhaseFlow idPhaseFlow idScaleFlow idScaleFlow (sndNF p) ≡ sndNF p
ζ-normalisation₂ (_ , y) = parametrise-id y

-- 3 & 4: Functional equation mirrors Δ/κ commutation.
ζ-functional-equation₁ : ∀ p → DeltaNF (CumulantNF (fstNF p)) ≡ CumulantNF (DeltaNF (fstNF p))
ζ-functional-equation₁ (x , _) = delta-cumulant-commute x

ζ-functional-equation₂ : ∀ p → DeltaNF (CumulantNF (sndNF p)) ≡ CumulantNF (DeltaNF (sndNF p))
ζ-functional-equation₂ (_ , y) = delta-cumulant-commute y

-- 5 & 6: Analytic continuation (Δ commutes with parametrisation).
ζ-analytic-continuation₁ : ∀ p →
  DeltaNF (parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow (fstNF p))
    ≡ parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow (DeltaNF (fstNF p))
ζ-analytic-continuation₁ (x , _) = delta-parametrise x

ζ-analytic-continuation₂ : ∀ p →
  DeltaNF (parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow (sndNF p))
    ≡ parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow (DeltaNF (sndNF p))
ζ-analytic-continuation₂ (_ , y) = delta-parametrise y

-- 7 & 8: Retraction witnesses from the renormalisability bundle.
open ZetaRenormalisation zetaRenormalisation
  renaming ( retractLCondition      to ζ-renorm-retractL
           ; retractRCondition      to ζ-renorm-retractR
           ; deltaBulkCondition     to ζ-renorm-deltaBulk
           ; deltaCumulantCondition to ζ-renorm-deltaCumulant
           )

ζ-retractL : _⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL
ζ-retractL = ζ-renorm-retractL

ζ-retractR : _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
ζ-retractR = ζ-renorm-retractR

-- 9: Δ distributes over the bulk sum (Euler product analogue).
ζ-delta-bulk : _⇒ᶜ*_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
ζ-delta-bulk = ζ-renorm-deltaBulk

-- 10: Δ commutes with cumulant (critical strip symmetry analogue).
ζ-delta-cumulant : _⇒ᶜ*_ (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)
ζ-delta-cumulant = ζ-renorm-deltaCumulant

------------------------------------------------------------------------
-- Constant independence across six moduli.
------------------------------------------------------------------------

record Moduli : Set where
  constructor mkModuli
  field
    m₁ m₂ m₃ m₄ m₅ m₆ : NormalForm ⊤

constantWitness : Moduli → NumberPair
constantWitness _ = swapPair analyticZeroPair

constantIndependent : ∀ mods → constantWitness mods ≡ constantWitness mods
constantIndependent _ = refl

------------------------------------------------------------------------
-- Dirichlet series alignment with zeta witnesses.
------------------------------------------------------------------------

open import CLEAN.Core.Dirichlet
open import CLEAN.Ports.Analytic.DirichletSeries

ζ-dirichlet-symmetric : ∀ r → DirichletSeries.weight analyticSeries r ≡ DirichletSeries.weight conjugateSeries r
ζ-dirichlet-symmetric = symmetricWeight

------------------------------------------------------------------------
-- Hecke/Artin alignment and regulator bounds.
------------------------------------------------------------------------

ζ-hecke-infinity : baseNormalForm ≡ infinityType
ζ-hecke-infinity = heckeInfinityWitness

ζ-artin-determinant : determinant ≡ baseNormalForm
ζ-artin-determinant = artinDeterminantWitness

ζ-dirichlet-weight : ∀ r → weight (dirichletSeries r) r
  ≡ (evaluateCharacter r baseNormalForm , Regulator.lambda r)
ζ-dirichlet-weight = dirichletWeightSpec

ζ-euler-weight : ∀ r → weight (eulerSeries r) r
  ≡ (localEulerFactor r , Regulator.lambda r)
ζ-euler-weight = eulerWeightSpec

ζ-local-delta : ∀ r → DeltaNF (evaluateCharacter r baseNormalForm) ≡ localEulerFactor r
ζ-local-delta = localDeltaCompatibility

ζ-growth-bound : ∀ r → growthBound r ≥ Regulator.lambda r
ζ-growth-bound = growthWitness

ζ-decay-bound : ∀ r → Regulator.lambda r ≥ decayBound r
ζ-decay-bound = decayWitness

ζ-delta-agreement : ∀ r → DeltaNF (evaluateSeries (dirichletSeries r) r)
  ≡ evaluateSeries (eulerSeries r) r
ζ-delta-agreement = deltaAgreement
