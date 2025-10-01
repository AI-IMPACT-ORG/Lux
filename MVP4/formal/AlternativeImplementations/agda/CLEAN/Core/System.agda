module CLEAN.Core.System where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)

open import CLEAN.Core.Sorts
open import CLEAN.Core.Signature
open import CLEAN.Core.Diagram
open import CLEAN.Core.Rewrite
open import CLEAN.Core.NormalForm

-- Local numerals for readability.
one : Nat
one = suc zero

two : Nat
two = suc one
three : Nat
three = suc two

-- Frequently used boundary vectors.
L¹ : Vec Sort one
L¹ = L ∷ []

R¹ : Vec Sort one
R¹ = R ∷ []

B¹ : Vec Sort one
B¹ = B ∷ []

LR : Vec Sort two
LR = L ∷ (R ∷ [])

BB : Vec Sort two
BB = B ∷ (B ∷ [])
L³ : Vec Sort three
L³ = L ∷ (L ∷ (L ∷ []))

-- Shorthand boundaries.
L↦L : Boundary one one
L↦L = mkBoundary L¹ L¹

R↦R : Boundary one one
R↦R = mkBoundary R¹ R¹

L↦B : Boundary one one
L↦B = mkBoundary L¹ B¹

R↦B : Boundary one one
R↦B = mkBoundary R¹ B¹

B↦L : Boundary one one
B↦L = mkBoundary B¹ L¹

B↦R : Boundary one one
B↦R = mkBoundary B¹ R¹

B↦B : Boundary one one
B↦B = mkBoundary B¹ B¹

BB↦B : Boundary two one
BB↦B = mkBoundary BB B¹

LR↦B : Boundary two one
LR↦B = mkBoundary LR B¹
BB↦BB : Boundary two two
BB↦BB = mkBoundary BB BB
L³↦L : Boundary three one
L³↦L = mkBoundary L³ L¹

-- Identity morphisms for the boundary sectors.
idL : Diagram Σ₁₀ L¹ L¹
idL = idD {xs = L¹}

idR : Diagram Σ₁₀ R¹ R¹
idR = idD {xs = R¹}

idB : Diagram Σ₁₀ B¹ B¹
idB = idD {xs = B¹}

idBB : Diagram Σ₁₀ BB BB
idBB = idD {xs = BB}

-- Primitive generators (short names with explicit boundaries).
ιLᵍ : Diagram Σ₁₀ L¹ B¹
ιLᵍ = gen ιL

ιRᵍ : Diagram Σ₁₀ R¹ B¹
ιRᵍ = gen ιR

νLᵍ : Diagram Σ₁₀ B¹ L¹
νLᵍ = gen νL

νRᵍ : Diagram Σ₁₀ B¹ R¹
νRᵍ = gen νR

bulkSumᵍ : Diagram Σ₁₀ BB B¹
bulkSumᵍ = gen BulkSum

trialityLᵍ : Diagram Σ₁₀ B¹ L¹
trialityLᵍ = gen TrialityL

trialityRᵍ : Diagram Σ₁₀ B¹ R¹
trialityRᵍ = gen TrialityR

trialityBᵍ : Diagram Σ₁₀ LR B¹
trialityBᵍ = gen TrialityB

conjBᵍ : Diagram Σ₁₀ B¹ B¹
conjBᵍ = gen ConjB

conjLᵍ : Diagram Σ₁₀ L¹ L¹
conjLᵍ = gen ConjL

conjRᵍ : Diagram Σ₁₀ R¹ R¹
conjRᵍ = gen ConjR

tensorLᵍ : Diagram Σ₁₀ (L ∷ (L ∷ [])) (L ∷ [])
tensorLᵍ = gen TensorL

guardNegᵍ : Diagram Σ₁₀ (L ∷ (L ∷ [])) (L ∷ [])
guardNegᵍ = gen GuardNeg

guardNANDᵍ : Diagram Σ₁₀ L³ L¹
guardNANDᵍ = gen GuardNAND

braidBBᵍ : Diagram Σ₁₀ BB BB
braidBBᵍ = gen BraidBB

deltaᵍ : Diagram Σ₁₀ B¹ B¹
deltaᵍ = gen DeltaB

cumulantᵍ : Diagram Σ₁₀ B¹ B¹
cumulantᵍ = gen CumulantB


-- | Enumeration of rewriting rules mirroring the CLEAN v10 equations.
data RuleId : Set where
  RetractL RetractR : RuleId
  TrialityBulk TrialityLeft TrialityRight : RuleId
  ConjugateLeftEmbed ConjugateRightEmbed : RuleId
  ConjugateLeftObserve ConjugateRightObserve : RuleId
  GuardedNAND BraidInvolutive DeltaCumulantCommute DeltaBulkSum DeltaObserverL DeltaObserverR : RuleId

ruleOfId : RuleId → Rule Σ₁₀
ruleOfId = λ where
  RetractL → mkRule L↦L (νLᵍ ∘ ιLᵍ) idL
  RetractR → mkRule R↦R (νRᵍ ∘ ιRᵍ) idR
  TrialityBulk → mkRule LR↦B trialityBᵍ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ))
  TrialityLeft → mkRule B↦L trialityLᵍ νLᵍ
  TrialityRight → mkRule B↦R trialityRᵍ νRᵍ
  ConjugateLeftEmbed → mkRule L↦B (conjBᵍ ∘ ιLᵍ) (ιLᵍ ∘ conjLᵍ)
  ConjugateRightEmbed → mkRule R↦B (conjBᵍ ∘ ιRᵍ) (ιRᵍ ∘ conjRᵍ)
  ConjugateLeftObserve → mkRule B↦L (νLᵍ ∘ conjBᵍ) (conjLᵍ ∘ νLᵍ)
  ConjugateRightObserve → mkRule B↦R (νRᵍ ∘ conjBᵍ) (conjRᵍ ∘ νRᵍ)
  GuardedNAND → mkRule L³↦L guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))
  BraidInvolutive → mkRule BB↦BB (braidBBᵍ ∘ braidBBᵍ) idBB
  DeltaCumulantCommute → mkRule B↦B (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)
  DeltaBulkSum → mkRule BB↦B (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
  -- Δ acting on observers is modelled as an explicit identity to expose the boundary.
  DeltaObserverL → mkRule B↦L (νLᵍ ∘ deltaᵍ) (νLᵍ ∘ deltaᵍ)
  DeltaObserverR → mkRule B↦R (νRᵍ ∘ deltaᵍ) (νRᵍ ∘ deltaᵍ)


ruleFamily : RuleFamily Σ₁₀
ruleFamily = family RuleId ruleOfId

-- | Contextual rewrite relations specialised to the CLEAN rule family.
_⇒ᶜ_ : ∀ {m n} {xs : Vec Sort m} {ys : Vec Sort n}
  → Diagram Σ₁₀ xs ys → Diagram Σ₁₀ xs ys → Set
_⇒ᶜ_ = _⇒_ Σ₁₀ ruleFamily

_⇒ᶜ*_ : ∀ {m n} {xs : Vec Sort m} {ys : Vec Sort n}
  → Diagram Σ₁₀ xs ys → Diagram Σ₁₀ xs ys → Set
_⇒ᶜ*_ = _⇒*_ Σ₁₀ ruleFamily

-- | Single-step witnesses for each generator-level axiom.
retractLStep : _⇒ᶜ_ (νLᵍ ∘ ιLᵍ) idL
retractLStep = step {i = RetractL}

retractRStep : _⇒ᶜ_ (νRᵍ ∘ ιRᵍ) idR
retractRStep = step {i = RetractR}

trialityBulkStep : _⇒ᶜ_ trialityBᵍ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ))
trialityBulkStep = step {i = TrialityBulk}

conjEmbedLStep : _⇒ᶜ_ (conjBᵍ ∘ ιLᵍ) (ιLᵍ ∘ conjLᵍ)
conjEmbedLStep = step {i = ConjugateLeftEmbed}

conjEmbedRStep : _⇒ᶜ_ (conjBᵍ ∘ ιRᵍ) (ιRᵍ ∘ conjRᵍ)
conjEmbedRStep = step {i = ConjugateRightEmbed}

conjObserveLStep : _⇒ᶜ_ (νLᵍ ∘ conjBᵍ) (conjLᵍ ∘ νLᵍ)
conjObserveLStep = step {i = ConjugateLeftObserve}

conjObserveRStep : _⇒ᶜ_ (νRᵍ ∘ conjBᵍ) (conjRᵍ ∘ νRᵍ)
conjObserveRStep = step {i = ConjugateRightObserve}

guardNANDStep : _⇒ᶜ_ guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))
guardNANDStep = step {i = GuardedNAND}

braidInvolutiveStep : _⇒ᶜ_ (braidBBᵍ ∘ braidBBᵍ) idBB
braidInvolutiveStep = step {i = BraidInvolutive}

deltaCumulantStep : _⇒ᶜ_ (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)
deltaCumulantStep = step {i = DeltaCumulantCommute}

deltaBulkSumStep : _⇒ᶜ_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
deltaBulkSumStep = step {i = DeltaBulkSum}

-- | Triality bulk map respects the left observer via contextual closure.
trialityLeftSound : _⇒ᶜ_ (νLᵍ ∘ trialityBᵍ)
                              (νLᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ)))
trialityLeftSound =
  seq₂ trialityBulkStep

trialityRightSound : _⇒ᶜ_ (νRᵍ ∘ trialityBᵍ)
                               (νRᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ)))
trialityRightSound =
  seq₂ trialityBulkStep

-- | Promote the single-step witnesses to the reflexive-transitive closure.
retractLId : _⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL
retractLId = trans retractLStep refl

retractRId : _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
retractRId = trans retractRStep refl

trialityBulkFactor : _⇒ᶜ*_ trialityBᵍ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ))
trialityBulkFactor = trans trialityBulkStep refl

conjEmbedL : _⇒ᶜ*_ (conjBᵍ ∘ ιLᵍ) (ιLᵍ ∘ conjLᵍ)
conjEmbedL = trans conjEmbedLStep refl

conjEmbedR : _⇒ᶜ*_ (conjBᵍ ∘ ιRᵍ) (ιRᵍ ∘ conjRᵍ)
conjEmbedR = trans conjEmbedRStep refl

conjObserveL : _⇒ᶜ*_ (νLᵍ ∘ conjBᵍ) (conjLᵍ ∘ νLᵍ)
conjObserveL = trans conjObserveLStep refl

conjObserveR : _⇒ᶜ*_ (νRᵍ ∘ conjBᵍ) (conjRᵍ ∘ νRᵍ)
conjObserveR = trans conjObserveRStep refl

guardNANDDerived : _⇒ᶜ*_ guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))
guardNANDDerived = trans guardNANDStep refl

braidInvolutive : _⇒ᶜ*_ (braidBBᵍ ∘ braidBBᵍ) idBB
braidInvolutive = trans braidInvolutiveStep refl

deltaCumulantCommute : _⇒ᶜ*_ (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)
deltaCumulantCommute = trans deltaCumulantStep refl

deltaBulkSum : _⇒ᶜ*_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
deltaBulkSum = trans deltaBulkSumStep refl

record BulkReconstruction : Set where
  constructor mkBulkReconstruction
  field
    leftWitness  : _⇒ᶜ_ (νLᵍ ∘ trialityBᵍ) (νLᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ)))
    rightWitness : _⇒ᶜ_ (νRᵍ ∘ trialityBᵍ) (νRᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ)))

bulkReconstruction : BulkReconstruction
bulkReconstruction = mkBulkReconstruction trialityLeftSound trialityRightSound

-- | Example normal form value with a trivial core payload.
open NormalForm

trivialNF : NormalForm ⊤
trivialNF = mkNF (mkHeader basePhase basePhase baseScale baseScale) tt
  where
    basePhase = signed plus zero
    baseScale = zero
