module CLEAN.Ports.Analytic.GRHOutline where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Sigma using (_,_)

open import CLEAN.Core.System using (_⇒ᶜ*_; νLᵍ; ιLᵍ; idL; νRᵍ; ιRᵍ; idR; deltaᵍ; bulkSumᵍ; cumulantᵍ)
open import CLEAN.Core.Diagram using (_∘_; _⊗_)
open import CLEAN.Core.Dirichlet
open import CLEAN.Core.NormalForm
open import CLEAN.Application.Complexity using (coNPStratified)
open import CLEAN.Ports.Analytic
open import CLEAN.Ports.Analytic.ZetaDefinition

open DirichletSeries
open ZetaRenormalisation
open LogicalZeta
open GrowthDecayControl

------------------------------------------------------------------------
-- Streamlined GRH argument package built from the unified conditions.
------------------------------------------------------------------------

record StreamlinedGRH : Set₁ where
  constructor mkStreamlinedGRH
  field
    renormalisationData : ZetaRenormalisation
    zetaData            : LogicalZeta
    regulatorDomainData : Regulator → Set
    regulatorStability  : ∀ r → regulatorDomainData r
    heckeCharacterData  : HeckeCharacterData
    artinRepresentationData : ArtinRepresentationData
    growthDecayData     : GrowthDecayControl
    growthWitnessData   : ∀ r → growthBound growthDecayData r ≥ Regulator.lambda r
    decayWitnessData    : ∀ r → Regulator.lambda r ≥ decayBound growthDecayData r
    dirichletWeightData : ∀ r → weight (dirichletSeries zetaData r) r
                              ≡ (HeckeCharacterData.evaluateCharacter heckeCharacterData r (baseNormalForm zetaData)
                                 , Regulator.lambda r)
    eulerWeightData     : ∀ r → weight (eulerSeries zetaData r) r
                              ≡ (ArtinRepresentationData.localEulerFactor artinRepresentationData r
                                 , Regulator.lambda r)
    retractLeftWitness  : _⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL
    retractRightWitness : _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
    deltaBulkWitness    : _⇒ᶜ*_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
    deltaCumulantWitness : _⇒ᶜ*_ (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)
    dirichletEulerLink  : ∀ r → DeltaNF (evaluateSeries (dirichletSeries zetaData r) r)
                                       ≡ evaluateSeries (eulerSeries zetaData r) r
    criticalOutcome     : LogicOutcome coNPStratified sampleField

streamlinedGRH : StreamlinedGRH
streamlinedGRH = mkStreamlinedGRH
  zetaRenormalisation
  logicalZeta
  (regulatorDomain logicalZeta)
  (regulatorStable logicalZeta)
  (heckeCharacter logicalZeta)
  (artinRepresentation logicalZeta)
  (growthDecayControl logicalZeta)
  (growthWitness (growthDecayControl logicalZeta))
  (decayWitness (growthDecayControl logicalZeta))
  (dirichletWeightSpec logicalZeta)
  (eulerWeightSpec logicalZeta)
  (retractLCondition zetaRenormalisation)
  (retractRCondition zetaRenormalisation)
  (deltaBulkCondition zetaRenormalisation)
  (deltaCumulantCondition zetaRenormalisation)
  (deltaAgreement logicalZeta)
  godelCriticalLine
