module CLEAN.Application.Classification where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

open import CLEAN.Core.Renormalisability
open import CLEAN.Application.PLBridge

------------------------------------------------------------------------
-- Layered logic invariants over the CLEAN renormalisability witnesses.
------------------------------------------------------------------------

-- | Coarse logic-order tags exposed at the meta level.
data LogicOrder : Set where
  FirstOrder  : LogicOrder
  HigherOrder : LogicOrder

-- | Lightweight complexity annotations mirroring classical classes.
data ComplexityTag : Set where
  Decidable : ComplexityTag
  NPClass   : ComplexityTag
  coNPClass : ComplexityTag

data RenormalisabilityTier : Set where
  TierSuper : RenormalisabilityTier
  TierRen   : RenormalisabilityTier
  TierNon   : RenormalisabilityTier

-- | Minimal Maybe type to stash optional witnesses.
data Maybe {ℓ} (A : Set ℓ) : Set ℓ where
  nothing : Maybe A
  just    : A → Maybe A

-- | Empty type used for refutations (inequalities).
data ⊥ : Set where

-- | Negation.
¬ : Set → Set
¬ A = A → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

-- | Logic profile keeps the observable invariants together.
record LogicProfile : Set₁ where
  constructor mkProfile
  field
    class      : RenormalisabilityTier
    order      : LogicOrder
    complexity : ComplexityTag
    witness    : Maybe RenormalisationWitness
    hoEncoding : Maybe HigherOrderEncoding

open LogicProfile public

-- | Stratification guarantees that the declared invariants line up.
data Stratification
  : RenormalisabilityTier → LogicOrder → ComplexityTag → Set where
  stratSuper : Stratification TierSuper FirstOrder Decidable
  stratRen   : Stratification TierRen   FirstOrder NPClass
  stratNon   : Stratification TierNon   HigherOrder coNPClass

-- | A stratified logic is a profile together with its invariant certificate.
record StratifiedLogic : Set₁ where
  constructor layered
  field
    profile        : LogicProfile
    stratification : Stratification (class profile)
                                      (order profile)
                                      (complexity profile)

open StratifiedLogic public

------------------------------------------------------------------------
-- Constructors for each stratum.
------------------------------------------------------------------------

-- | Super-renormalisable logics are recorded as first-order and decidable.
mkSuperRenormalisable
  : RenormalisationWitness → StratifiedLogic
mkSuperRenormalisable w =
  layered (mkProfile TierSuper FirstOrder Decidable (just w) nothing)
          stratSuper

-- | Renormalisable logics inherit the first-order/NP annotation.
mkRenormalisable : RenormalisationWitness → StratifiedLogic
mkRenormalisable w =
  layered (mkProfile TierRen FirstOrder NPClass (just w) nothing)
          stratRen

-- | Non-renormalisable logics are tracked as higher-order with coNP flavour.
record HigherOrderCertificate : Set₁ where
  constructor certifyHO
  field
    encoding : HigherOrderEncoding

open HigherOrderCertificate public

mkNonRenormalisable : HigherOrderCertificate → StratifiedLogic
mkNonRenormalisable cert =
  layered (mkProfile TierNon HigherOrder coNPClass nothing (just (encoding cert)))
          stratNon

------------------------------------------------------------------------
-- Derived meta-theoretic statements.
------------------------------------------------------------------------

-- | Non-renormalisable profiles are forced to be higher-order.
nonRenormalisable⇒HigherOrder
  : ∀ {ℒ : StratifiedLogic}
  → class (profile ℒ) ≡ TierNon
  → order (profile ℒ) ≡ HigherOrder
nonRenormalisable⇒HigherOrder {layered _ stratSuper} ()
nonRenormalisable⇒HigherOrder {layered _ stratRen}   ()
nonRenormalisable⇒HigherOrder {layered _ stratNon}   refl = refl

-- | Renormalisable profiles collapse to first-order.
renormalisable⇒FirstOrder
  : ∀ {ℒ : StratifiedLogic}
  → class (profile ℒ) ≡ TierRen
  → order (profile ℒ) ≡ FirstOrder
renormalisable⇒FirstOrder {layered _ stratSuper} ()
renormalisable⇒FirstOrder {layered _ stratRen}   refl = refl
renormalisable⇒FirstOrder {layered _ stratNon}   ()

-- | Super-renormalisable profiles also stay first-order.
superRenormalisable⇒FirstOrder
  : ∀ {ℒ : StratifiedLogic}
  → class (profile ℒ) ≡ TierSuper
  → order (profile ℒ) ≡ FirstOrder
superRenormalisable⇒FirstOrder {layered _ stratSuper} refl = refl
superRenormalisable⇒FirstOrder {layered _ stratRen}   ()
superRenormalisable⇒FirstOrder {layered _ stratNon}   ()

-- | Complexity annotations separate the strata.
renVsNonRenComplexity
  : ∀ {ℛ ℕ : StratifiedLogic}
  → class (profile ℛ) ≡ TierRen
  → class (profile ℕ) ≡ TierNon
  → complexity (profile ℛ) ≢ complexity (profile ℕ)
renVsNonRenComplexity {layered _ stratSuper} {_} () _
renVsNonRenComplexity {layered _ stratRen}   {layered _ stratNon} refl refl eq with eq
... | ()
renVsNonRenComplexity {layered _ stratRen}   {layered _ stratSuper} refl ()
renVsNonRenComplexity {layered _ stratRen}   {layered _ stratRen}   refl ()
renVsNonRenComplexity {layered _ stratNon}   {_} () _

superVsNonRenComplexity
  : ∀ {ℛ ℕ : StratifiedLogic}
  → class (profile ℛ) ≡ TierSuper
  → class (profile ℕ) ≡ TierNon
  → complexity (profile ℛ) ≢ complexity (profile ℕ)
superVsNonRenComplexity {layered _ stratSuper} {layered _ stratNon} refl refl eq with eq
... | ()
superVsNonRenComplexity {layered _ stratSuper} {layered _ stratSuper} refl ()
superVsNonRenComplexity {layered _ stratSuper} {layered _ stratRen}   refl ()
superVsNonRenComplexity {layered _ stratRen}   {_} () _
superVsNonRenComplexity {layered _ stratNon}   {_} () _

------------------------------------------------------------------------
-- NP vs coNP tags at the meta level.
------------------------------------------------------------------------

npTag : ComplexityTag
npTag = NPClass

coNPTag : ComplexityTag
coNPTag = coNPClass

-- | Within the tagged layer NP and coNP remain separated.
np≠coNP : npTag ≢ coNPTag
np≠coNP ()

------------------------------------------------------------------------
-- Bundled statement capturing the stratified classification.
------------------------------------------------------------------------

record ClassificationSummary : Set₁ where
  constructor mkSummary
  field
    renFirstOrder  : ∀ {ℒ} → class (profile ℒ) ≡ TierRen
                       → order (profile ℒ) ≡ FirstOrder
    superFirstOrder : ∀ {ℒ} → class (profile ℒ) ≡ TierSuper
                       → order (profile ℒ) ≡ FirstOrder
    nonRenHigher    : ∀ {ℒ} → class (profile ℒ) ≡ TierNon
                       → order (profile ℒ) ≡ HigherOrder
    complexitySplit : npTag ≢ coNPTag

classificationSummary : ClassificationSummary
classificationSummary = record
  { renFirstOrder  = λ {ℒ} → renormalisable⇒FirstOrder {ℒ}
  ; superFirstOrder = λ {ℒ} → superRenormalisable⇒FirstOrder {ℒ}
  ; nonRenHigher    = λ {ℒ} → nonRenormalisable⇒HigherOrder {ℒ}
  ; complexitySplit = np≠coNP
  }

------------------------------------------------------------------------
-- Convenience extractor for the layered invariants.
------------------------------------------------------------------------

logicInvariants : StratifiedLogic → Σ LogicOrder (λ _ → ComplexityTag)
logicInvariants ℒ = order (profile ℒ) , complexity (profile ℒ)

-- | Recover the optional higher-order encoding carried by a profile.
higherOrderEncodingOf : StratifiedLogic → Maybe HigherOrderEncoding
higherOrderEncodingOf ℒ = hoEncoding (profile ℒ)

-- | Canonical non-renormalisable profile arising from the default encoding.
defaultNonRenormalisable : StratifiedLogic
defaultNonRenormalisable =
  mkNonRenormalisable (certifyHO defaultHigherOrderEncoding)

defaultEncodingWitness :
  higherOrderEncodingOf defaultNonRenormalisable ≡ just defaultHigherOrderEncoding
defaultEncodingWitness = refl
