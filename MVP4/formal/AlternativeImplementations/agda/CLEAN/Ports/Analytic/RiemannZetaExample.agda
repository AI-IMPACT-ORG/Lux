module CLEAN.Ports.Analytic.RiemannZetaExample where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import CLEAN.Core.Dirichlet
open import CLEAN.Core.NormalForm
open import CLEAN.Application.Complexity using (coNPStratified)
open import CLEAN.Ports.Analytic
open import CLEAN.Ports.Analytic.ZetaDefinition
open import CLEAN.Ports.Analytic.Semantics

open LogicalZeta
open HeckeCharacterData
open ArtinRepresentationData
open GrowthDecayControl

------------------------------------------------------------------------
-- Example: classical Riemann ζ-function treated as a logical L-series.
------------------------------------------------------------------------

riemannLogicalZeta : LogicalZeta
riemannLogicalZeta = logicalZeta

riemannHeckeCharacter : HeckeCharacterData
riemannHeckeCharacter = heckeCharacter riemannLogicalZeta

riemannArtinRepresentation : ArtinRepresentationData
riemannArtinRepresentation = artinRepresentation riemannLogicalZeta

riemannGrowthDecay : GrowthDecayControl
riemannGrowthDecay = growthDecayControl riemannLogicalZeta

trivialRegulator : Regulator
trivialRegulator = mkRegulator zero

riemannDirichletSeries : DirichletSeries
riemannDirichletSeries = dirichletSeries riemannLogicalZeta trivialRegulator

riemannEulerSeries : DirichletSeries
riemannEulerSeries = eulerSeries riemannLogicalZeta trivialRegulator

riemannDirichletWeight : Weight (NormalForm ⊤)
riemannDirichletWeight = weight riemannDirichletSeries trivialRegulator

riemannEulerWeight : Weight (NormalForm ⊤)
riemannEulerWeight = weight riemannEulerSeries trivialRegulator

riemannGrowthWitness :
  growthBound riemannGrowthDecay trivialRegulator ≥ Regulator.lambda trivialRegulator
riemannGrowthWitness = growthWitness riemannGrowthDecay trivialRegulator

riemannDecayWitness :
  Regulator.lambda trivialRegulator ≥ decayBound riemannGrowthDecay trivialRegulator
riemannDecayWitness = decayWitness riemannGrowthDecay trivialRegulator

riemannDenotation : LogicalZetaDenotation
riemannDenotation = identityDenotation riemannLogicalZeta

-- Example (Δ-flow identity specialised to the Riemann ζ-series).
riemannDeltaFlowExample : ∀ r →
  DeltaNF (evaluateSeries (dirichletSeries riemannLogicalZeta r) r)
    ≡ evaluateSeries (eulerSeries riemannLogicalZeta r) r
riemannDeltaFlowExample = deltaAgreement riemannLogicalZeta

riemannDeltaAgreement :
  DeltaNF (evaluateSeries riemannDirichletSeries trivialRegulator)
    ≡ evaluateSeries riemannEulerSeries trivialRegulator
riemannDeltaAgreement = riemannDeltaFlowExample trivialRegulator

riemannRegulatorBounds : Σ (Regulator.lambda trivialRegulator ≥ decayBound riemannGrowthDecay trivialRegulator)
  (λ _ → growthBound riemannGrowthDecay trivialRegulator ≥ Regulator.lambda trivialRegulator)
riemannRegulatorBounds = regulatorBounds riemannGrowthDecay trivialRegulator

scaleSum : NormalForm ⊤ → Nat
scaleSum nf with header nf
... | h = scaleL h + scaleR h

riemannScaleDenotation : LogicalZetaDenotation
riemannScaleDenotation = interpretDenotation scaleSum riemannLogicalZeta

riemannScaleDeltaAgreement : ∀ r →
  dirichletSem riemannScaleDenotation r ≡ eulerSem riemannScaleDenotation r
riemannScaleDeltaAgreement = deltaSemantic riemannScaleDenotation

riemannCriticalLineOutcome : CLEAN.Ports.Analytic.LogicOutcome coNPStratified CLEAN.Ports.Analytic.sampleField
riemannCriticalLineOutcome = CLEAN.Ports.Analytic.godelCriticalLine
