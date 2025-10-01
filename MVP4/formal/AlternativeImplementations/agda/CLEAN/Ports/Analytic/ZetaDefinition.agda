module CLEAN.Ports.Analytic.ZetaDefinition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import CLEAN.Core.System using (_⇒ᶜ*_; νLᵍ; ιLᵍ; idL; νRᵍ; ιRᵍ; idR; deltaᵍ; bulkSumᵍ; cumulantᵍ)
open import CLEAN.Core.Diagram using (_∘_; _⊗_)
open import CLEAN.Core.NormalForm
open import CLEAN.Core.Renormalisability
open import CLEAN.Core.Dirichlet
open import CLEAN.Core.EulerProduct
open import CLEAN.Ports.Analytic using (analyticNF)

open DirichletSeries

private
  transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  transEq refl q = q

  congEq : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
  congEq f refl = refl

------------------------------------------------------------------------
-- Unified renormalisation data harvested from the core logic.
------------------------------------------------------------------------

record ZetaRenormalisation : Set where
  constructor mkZetaRenormalisation
  field
    retractLCondition      : _⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL
    retractRCondition      : _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
    deltaBulkCondition     : _⇒ᶜ*_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
    deltaCumulantCondition : _⇒ᶜ*_ (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)

fromWitness : RenormalisationWitness → ZetaRenormalisation
fromWitness witness =
  mkZetaRenormalisation
    (RenormalisationWitness.retractLWitness witness)
    (RenormalisationWitness.retractRWitness witness)
    (RenormalisationWitness.deltaBulkWitness witness)
    (RenormalisationWitness.deltaCumulantWitness witness)

zetaRenormalisation : ZetaRenormalisation
zetaRenormalisation = fromWitness cleanRenormalisable

------------------------------------------------------------------------
-- Hecke characters and Artin representations powering L-functions.
------------------------------------------------------------------------

record HeckeCharacterData : Set where
  constructor mkHeckeCharacter
  field
    conductor         : Regulator
    infinityType      : NormalForm ⊤
    evaluateCharacter : Regulator → NormalForm ⊤ → NormalForm ⊤
    infinityCompatibility : ∀ r →
      evaluateCharacter r infinityType ≡ infinityType

record ArtinRepresentationData : Set where
  constructor mkArtinRepresentation
  field
    degree                   : Nat
    determinant              : NormalForm ⊤
    localEulerFactor         : Regulator → NormalForm ⊤
    determinantCompatibility : ∀ r →
      localEulerFactor r ≡ DeltaNF determinant

defaultHeckeCharacter : HeckeCharacterData
defaultHeckeCharacter =
  mkHeckeCharacter
    (mkRegulator zero)
    analyticNF
    (λ _ nf → nf)
    (λ _ → refl)

defaultArtinRepresentation : ArtinRepresentationData
defaultArtinRepresentation =
  mkArtinRepresentation
    (suc zero)
    analyticNF
    (λ _ → DeltaNF analyticNF)
    (λ _ → refl)

------------------------------------------------------------------------
-- Analytic growth/decay control for regulator budgets.
------------------------------------------------------------------------

record GrowthDecayControl : Set where
  constructor mkGrowthDecay
  field
    growthBound   : Regulator → Nat
    decayBound    : Regulator → Nat
    growthWitness : ∀ r → growthBound r ≥ Regulator.lambda r
    decayWitness  : ∀ r → Regulator.lambda r ≥ decayBound r

λ≥zero : ∀ n → n ≥ zero
λ≥zero zero    = ≥-refl
λ≥zero (suc n) = ≥-step (λ≥zero n)

defaultGrowthDecay : GrowthDecayControl
defaultGrowthDecay =
  mkGrowthDecay
    (λ r → suc (Regulator.lambda r))
    (λ _ → zero)
    (λ r → ≥-step (≥-refl {n = Regulator.lambda r}))
    (λ r → λ≥zero (Regulator.lambda r))

regulatorBounds : (control : GrowthDecayControl) → ∀ r →
  Σ (Regulator.lambda r ≥ GrowthDecayControl.decayBound control r)
    (λ _ → GrowthDecayControl.growthBound control r ≥ Regulator.lambda r)
regulatorBounds control r =
  GrowthDecayControl.decayWitness control r ,
  GrowthDecayControl.growthWitness control r

------------------------------------------------------------------------
-- Logical L-function bundle integrating Hecke/Artin data.
------------------------------------------------------------------------

heckeDirichletSeries
  : HeckeCharacterData → NormalForm ⊤ → Regulator → DirichletSeries
heckeDirichletSeries χ nf r =
  mkSeries nf (λ s → (HeckeCharacterData.evaluateCharacter χ s nf , Regulator.lambda s))

artinEulerSeries
  : ArtinRepresentationData → NormalForm ⊤ → Regulator → DirichletSeries
artinEulerSeries ρ nf r =
  mkSeries nf (λ s → (ArtinRepresentationData.localEulerFactor ρ s , Regulator.lambda s))

record LogicalZeta : Set₁ where
  constructor mkLogicalZeta
  field
    baseNormalForm : NormalForm ⊤
    renormalisation : ZetaRenormalisation
    heckeCharacter  : HeckeCharacterData
    artinRepresentation : ArtinRepresentationData
    heckeInfinityWitness : baseNormalForm ≡ HeckeCharacterData.infinityType heckeCharacter
    artinDeterminantWitness :
      ArtinRepresentationData.determinant artinRepresentation ≡ baseNormalForm
    growthDecayControl : GrowthDecayControl
    regulatorDomain : Regulator → Set
    regulatorStable : ∀ r → regulatorDomain r
    dirichletSeries : Regulator → DirichletSeries
    dirichletSeriesSpec : ∀ r → dirichletSeries r ≡
      heckeDirichletSeries heckeCharacter baseNormalForm r
    dirichletWeightSpec : ∀ r → weight (dirichletSeries r) r
                           ≡ (HeckeCharacterData.evaluateCharacter heckeCharacter r baseNormalForm
                              , Regulator.lambda r)
    eulerSeries     : Regulator → DirichletSeries
    eulerSeriesSpec : ∀ r → eulerSeries r ≡
      artinEulerSeries artinRepresentation baseNormalForm r
    eulerWeightSpec : ∀ r → weight (eulerSeries r) r
                       ≡ (ArtinRepresentationData.localEulerFactor artinRepresentation r
                          , Regulator.lambda r)
    localDeltaCompatibility : ∀ r →
      DeltaNF (HeckeCharacterData.evaluateCharacter heckeCharacter r baseNormalForm)
        ≡ ArtinRepresentationData.localEulerFactor artinRepresentation r
    deltaAgreement  : ∀ r →
      DeltaNF (evaluateSeries (dirichletSeries r) r)
        ≡ evaluateSeries (eulerSeries r) r

logicalZeta : LogicalZeta
logicalZeta = mkLogicalZeta
  analyticNF
  zetaRenormalisation
  defaultHeckeCharacter
  defaultArtinRepresentation
  refl
  refl
  defaultGrowthDecay
  (λ _ → ⊤)
  (λ _ → tt)
  (λ r → heckeDirichletSeries defaultHeckeCharacter analyticNF r)
  (λ _ → refl)
  (λ _ → refl)
  (λ r → artinEulerSeries defaultArtinRepresentation analyticNF r)
  (λ _ → refl)
  (λ _ → refl)
  (λ r →
    let χ = defaultHeckeCharacter
        ρ = defaultArtinRepresentation
        hecEq = refl
        artEq = refl
        step₁ = congEq (HeckeCharacterData.evaluateCharacter χ r) hecEq
        step₂ = HeckeCharacterData.infinityCompatibility χ r
        evalStep = transEq step₁ step₂
        deltaToInfinity = congEq DeltaNF evalStep
        deltaToBase = congEq DeltaNF (sym hecEq)
        deltaToDet = congEq DeltaNF (sym artEq)
        detToEuler = sym (ArtinRepresentationData.determinantCompatibility ρ r)
        part₁ = transEq deltaToInfinity deltaToBase
        part₂ = transEq part₁ deltaToDet
    in transEq part₂ detToEuler)
  (λ _ → refl)
