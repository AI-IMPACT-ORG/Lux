module CLEAN.Tests.Flows where

open import CLEAN.Library
open NormalForm
open Header

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Sample phase flows adjusting the magnitude component.
phaseInc : PhaseFlow
phaseInc = phaseFlow (λ s → signed (sign s) (suc (magnitude s)))

phaseTwice : PhaseFlow
phaseTwice = phaseFlow (λ s → signed (sign s) (suc (suc (magnitude s))))

phaseShift : PhaseFlow
phaseShift = phaseFlow (λ s → signed plus (magnitude s))

-- Sample scale flows.
scaleInc : ScaleFlow
scaleInc = scaleFlow suc

scaleTwice : ScaleFlow
scaleTwice = scaleFlow (λ n → suc (suc n))

scaleId : ScaleFlow
scaleId = idScaleFlow

-- Base normal form used in RG flow tests.
baseHeader : Header
baseHeader = mkHeader (signed plus zero) (signed plus zero) zero zero

baseNF : NormalForm ⊤
baseNF = mkNF baseHeader tt

-- | Associativity of phase flows supplied by the semigroup witness.
phase-flow-assoc : (phaseInc ∘ₚ phaseTwice) ∘ₚ phaseShift ≡ phaseInc ∘ₚ (phaseTwice ∘ₚ phaseShift)
phase-flow-assoc = FlowSemigroup.assoc phaseFlowSemigroup phaseInc phaseTwice phaseShift

-- | Associativity of scale flows from their semigroup witness.
scale-flow-assoc : (scaleInc ∘ₛ scaleTwice) ∘ₛ scaleId ≡ scaleInc ∘ₛ (scaleTwice ∘ₛ scaleId)
scale-flow-assoc = FlowSemigroup.assoc scaleFlowSemigroup scaleInc scaleTwice scaleId

-- | Parametrisation composed in two steps equals parametrisation with combined flows.
rg-parametrise-compose :
  parametrise phaseInc phaseTwice scaleInc scaleTwice
    (parametrise phaseShift idPhaseFlow scaleId idScaleFlow baseNF)
  ≡ parametrise (phaseShift ∘ₚ phaseInc)
                (idPhaseFlow ∘ₚ phaseTwice)
                (scaleId ∘ₛ scaleInc)
                (idScaleFlow ∘ₛ scaleTwice)
                baseNF
rg-parametrise-compose =
  parametrise-compose phaseShift phaseInc idPhaseFlow phaseTwice scaleId scaleInc idScaleFlow scaleTwice baseNF

-- | Identity flows leave a normal form unchanged.
rg-parametrise-id : parametrise idPhaseFlow idPhaseFlow idScaleFlow idScaleFlow baseNF ≡ baseNF
rg-parametrise-id = parametrise-id baseNF

-- | Δ commutes with parametrisation for the sample normal form.
rg-delta-parametrise : DeltaNF (parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow baseNF)
                       ≡ parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow (DeltaNF baseNF)
rg-delta-parametrise = delta-parametrise baseNF

-- | Δ and cumulant commute on the sample normal form.
rg-delta-cumulant : DeltaNF (CumulantNF baseNF) ≡ CumulantNF (DeltaNF baseNF)
rg-delta-cumulant = delta-cumulant-commute baseNF

-- | Δ distributes over the bulk sum recombination.
delta-bulk-sum : _⇒ᶜ*_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
delta-bulk-sum = deltaBulkSum
