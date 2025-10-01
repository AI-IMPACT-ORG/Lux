module CLEAN.Core.NormalForm where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

infixl 50 _+_
_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)

-- | Signed magnitudes for the left/right phase exponents.
data Sign : Set where
  plus minus : Sign

record Signed : Set where
  constructor signed
  field
    sign      : Sign
    magnitude : Nat

open Signed public

-- | Symmetry of equality used when shuttling PSDM proofs.
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- | Header data that tracks boundary phases and scales explicitly.
record Header : Set where
  constructor mkHeader
  field
    phaseL phaseR : Signed
    scaleL scaleR : Nat

open Header public

record NormalForm (Core : Set) : Set where
  constructor mkNF
  field
    header : Header
    core   : Core

open NormalForm public

record PhaseFlow : Set where
  constructor phaseFlow
  field actPhase : Signed → Signed

record ScaleFlow : Set where
  constructor scaleFlow
  field actScale : Nat → Nat

open PhaseFlow public
open ScaleFlow public

-- | Sequential composition of phase flows (apply the left, then the right).
_∘ₚ_ : PhaseFlow → PhaseFlow → PhaseFlow
f ∘ₚ g = phaseFlow (λ s → actPhase g (actPhase f s))

-- | Sequential composition of scale flows.
_∘ₛ_ : ScaleFlow → ScaleFlow → ScaleFlow
f ∘ₛ g = scaleFlow (λ n → actScale g (actScale f n))

-- | Identity flows leave their argument unchanged.
idPhaseFlow : PhaseFlow
idPhaseFlow = phaseFlow (λ s → s)

idScaleFlow : ScaleFlow
idScaleFlow = scaleFlow (λ n → n)

bulkPhase : Header → Signed
bulkPhase h = signed (sign (phaseL h)) (magnitude (phaseL h) + magnitude (phaseR h))

bulkScale : Header → Nat
bulkScale h = scaleL h + scaleR h

parametrise : ∀ {Core}
  → PhaseFlow → PhaseFlow
  → ScaleFlow → ScaleFlow
  → NormalForm Core
  → NormalForm Core
parametrise fL fR gL gR (mkNF h c) = mkNF h' c
  where
    h' = mkHeader (actPhase fL (phaseL h))
                  (actPhase fR (phaseR h))
                  (actScale gL (scaleL h))
                  (actScale gR (scaleR h))

-- | Parametrisation respects the composition of flows.
parametrise-compose
  : ∀ {Core}
    (fL₁ fL₂ : PhaseFlow) (fR₁ fR₂ : PhaseFlow)
    (gL₁ gL₂ : ScaleFlow)  (gR₁ gR₂ : ScaleFlow)
    (nf : NormalForm Core)
  → parametrise fL₂ fR₂ gL₂ gR₂ (parametrise fL₁ fR₁ gL₁ gR₁ nf)
    ≡ parametrise (fL₁ ∘ₚ fL₂) (fR₁ ∘ₚ fR₂) (gL₁ ∘ₛ gL₂) (gR₁ ∘ₛ gR₂) nf
parametrise-compose fL₁ fL₂ fR₁ fR₂ gL₁ gL₂ gR₁ gR₂ (mkNF h c) = refl

-- | Parametrisation with identity flows is the identity on normal forms.
parametrise-id : ∀ {Core} (nf : NormalForm Core) →
  parametrise idPhaseFlow idPhaseFlow idScaleFlow idScaleFlow nf ≡ nf
parametrise-id (mkNF h c) = refl

-- | Generic semigroup packaging for flow composition.
record FlowSemigroup (Flow : Set) : Set where
  constructor mkSemigroup
  field
    _∙_ : Flow → Flow → Flow
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

-- | Phase flows form a semigroup under sequential composition.
phaseFlowSemigroup : FlowSemigroup PhaseFlow
phaseFlowSemigroup = mkSemigroup _∘ₚ_ (λ _ _ _ → refl)

-- | Scale flows form a semigroup under sequential composition.
scaleFlowSemigroup : FlowSemigroup ScaleFlow
scaleFlowSemigroup = mkSemigroup _∘ₛ_ (λ _ _ _ → refl)

infix 4 _≥_

-- Simple ordering on Nat to speak about monotonicity.
data _≥_ : Nat → Nat → Set where
  ≥-refl : ∀ {n} → n ≥ n
  ≥-step : ∀ {m n} → m ≥ n → suc m ≥ n

-- | A phase flow is monotone when it does not shrink the magnitude.
record MonotonePhase : Set where
  constructor monotone
  field
    flow : PhaseFlow
    mono : ∀ s → magnitude (actPhase flow s) ≥ magnitude s

-- | Positive naturals (successor form) used to track regulator budgets.
data Positive : Nat → Set where
  pos-suc : ∀ n → Positive (suc n)

-- | Δ and cumulant flows acting on the header scales.
deltaFlow : ScaleFlow
deltaFlow = scaleFlow suc

cumulantFlow : ScaleFlow
cumulantFlow = scaleFlow (λ n → suc (suc n))

DeltaNF : ∀ {Core} → NormalForm Core → NormalForm Core
DeltaNF = parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow

CumulantNF : ∀ {Core} → NormalForm Core → NormalForm Core
CumulantNF = parametrise idPhaseFlow idPhaseFlow cumulantFlow cumulantFlow

-- | Δ flow commutes with another Δ parametrisation.
delta-parametrise : ∀ {Core} (nf : NormalForm Core) →
  DeltaNF (parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow nf) ≡
  parametrise idPhaseFlow idPhaseFlow deltaFlow deltaFlow (DeltaNF nf)
delta-parametrise (mkNF h c) = refl

-- | Δ and cumulant flows commute on normal forms.
delta-cumulant-commute : ∀ {Core} (nf : NormalForm Core) →
  DeltaNF (CumulantNF nf) ≡ CumulantNF (DeltaNF nf)
delta-cumulant-commute (mkNF h c) = refl



-- | Partial Stable Domain Map (PSDM) interface over normal forms.
record PSDM (Core : Set) : Set₁ where
  constructor mkPSDM
  field
    Domain         : NormalForm Core → Set
    apply          : (nf : NormalForm Core) → Domain nf → NormalForm Core
    stableDelta    : ∀ {nf} → Domain nf → Domain (DeltaNF nf)
    stableCumulant : ∀ {nf} → Domain nf → Domain (CumulantNF nf)
    commuteDelta   : ∀ {nf} (d : Domain nf) →
                     DeltaNF (apply nf d) ≡ apply (DeltaNF nf) (stableDelta d)
    commuteCumulant : ∀ {nf} (d : Domain nf) →
                      CumulantNF (apply nf d) ≡ apply (CumulantNF nf) (stableCumulant d)

open PSDM public

open import Agda.Builtin.Unit using (⊤; tt)

-- | PSDM that is total and returns its input unchanged.
identityPSDM : ∀ {Core} → PSDM Core
identityPSDM = mkPSDM
  (λ _ → ⊤)
  (λ nf _ → nf)
  (λ _ → tt)
  (λ _ → tt)
  (λ _ → refl)
  (λ _ → refl)

-- | PSDM that always applies Δ and carries a rudimentary budget witness.
deltaPSDM : ∀ {Core} → PSDM Core
deltaPSDM = mkPSDM
  (λ _ → Σ Nat Positive)
  (λ nf _ → DeltaNF nf)
  (λ {nf} d → d)
  (λ {nf} d → d)
  (λ _ → refl)
  (λ {nf} _ → delta-cumulant-commute nf)

-- | PSDM applying the cumulant flow.
cumulantPSDM : ∀ {Core} → PSDM Core
cumulantPSDM = mkPSDM
  (λ _ → Σ Nat Positive)
  (λ nf _ → CumulantNF nf)
  (λ {nf} d → d)
  (λ {nf} d → d)
  (λ {nf} _ → sym (delta-cumulant-commute nf))
  (λ _ → refl)
