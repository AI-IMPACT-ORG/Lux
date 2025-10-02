module CLEAN.Ports.Analytic.QuadraticCharacterExample where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import CLEAN.Core.NormalForm
open import CLEAN.Core.Dirichlet
open import CLEAN.Ports.Analytic
open import CLEAN.Ports.Analytic.ZetaDefinition
open import CLEAN.Ports.Analytic.Semantics
open import Agda.Builtin.Sigma using (Σ; _,_)
open import CLEAN.Ports.Analytic.Semantics

open LogicalZeta
open HeckeCharacterData
open ArtinRepresentationData
open GrowthDecayControl

------------------------------------------------------------------------
-- Example: toy quadratic character realised inside the logical framework.
------------------------------------------------------------------------
-- This mirrors the Riemann example but with a non-trivial phase profile:
-- the Δ-flow, regulator sandwich, and denotational views are all surfaced
-- so additional characters can follow the blueprint with minimal effort.

quadraticHeckeCharacter : HeckeCharacterData
quadraticHeckeCharacter =
  mkHeckeCharacter
    (mkRegulator zero)
    (CumulantNF analyticNF)
    (λ _ _ → CumulantNF analyticNF)
    (λ _ → refl)

quadraticArtinRepresentation : ArtinRepresentationData
quadraticArtinRepresentation =
  mkArtinRepresentation
    (suc (suc zero))
    (CumulantNF analyticNF)
    (λ _ → DeltaNF (CumulantNF analyticNF))
    (λ _ → refl)

quadraticGrowthDecay : GrowthDecayControl
quadraticGrowthDecay = defaultGrowthDecay

quadraticRegulator₀ : Regulator
quadraticRegulator₀ = mkRegulator zero

quadraticLogicalZeta : LogicalZeta
quadraticLogicalZeta = mkLogicalZeta
  (CumulantNF analyticNF)
  zetaRenormalisation
  quadraticHeckeCharacter
  quadraticArtinRepresentation
  refl
  refl
  quadraticGrowthDecay
  (λ _ → ⊤)
  (λ _ → tt)
  (λ r → heckeDirichletSeries quadraticHeckeCharacter (CumulantNF analyticNF) r)
  (λ _ → refl)
  (λ _ → refl)
  (λ r → artinEulerSeries quadraticArtinRepresentation (CumulantNF analyticNF) r)
  (λ _ → refl)
  (λ _ → refl)
  (λ _ → refl)
  (λ _ → refl)

quadraticDirichletSeries : Regulator → DirichletSeries
quadraticDirichletSeries = dirichletSeries quadraticLogicalZeta

quadraticEulerSeries : Regulator → DirichletSeries
quadraticEulerSeries = eulerSeries quadraticLogicalZeta

quadraticDenotation : LogicalZetaDenotation
quadraticDenotation = identityDenotation quadraticLogicalZeta

quadraticRegulatorBounds : Σ (Regulator.lambda quadraticRegulator₀ ≥ decayBound quadraticGrowthDecay quadraticRegulator₀)
  (λ _ → growthBound quadraticGrowthDecay quadraticRegulator₀ ≥ Regulator.lambda quadraticRegulator₀)
quadraticRegulatorBounds = regulatorBounds quadraticGrowthDecay quadraticRegulator₀

quadraticDeltaFlowExample : ∀ r →
  DeltaNF (evaluateSeries (dirichletSeries quadraticLogicalZeta r) r)
    ≡ evaluateSeries (eulerSeries quadraticLogicalZeta r) r
quadraticDeltaFlowExample = deltaAgreement quadraticLogicalZeta

quadraticDeltaAgreement :
  DeltaNF (evaluateSeries (quadraticDirichletSeries quadraticRegulator₀) quadraticRegulator₀)
    ≡ evaluateSeries (quadraticEulerSeries quadraticRegulator₀) quadraticRegulator₀
quadraticDeltaAgreement = quadraticDeltaFlowExample quadraticRegulator₀

phasePair : NormalForm ⊤ → Σ Signed (λ _ → Signed)
phasePair nf with header nf
... | h = phaseL h , phaseR h

quadraticPhaseDenotation : LogicalZetaDenotation
quadraticPhaseDenotation = interpretDenotation phasePair quadraticLogicalZeta

quadraticPhaseDeltaAgreement : ∀ r →
  dirichletSem quadraticPhaseDenotation r ≡ eulerSem quadraticPhaseDenotation r
quadraticPhaseDeltaAgreement = deltaSemantic quadraticPhaseDenotation
