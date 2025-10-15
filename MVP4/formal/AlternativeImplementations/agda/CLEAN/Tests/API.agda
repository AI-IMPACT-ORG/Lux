module CLEAN.Tests.API where

open import CLEAN.Library
open import CLEAN.Core.Guard
open import CLEAN.Core.Proofs.PSDM
open NormalForm
open Header

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat renaming (zero to zeroℕ; suc to sucℕ)
open BulkReconstruction bulkReconstruction using (leftWitness; rightWitness)

data ⊥ : Set where

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl
-- | API-level guarantee: observer retractions reduce to identity on boundaries.
api-retractL : _⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL
api-retractL = retractLId

api-retractR : _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
api-retractR = retractRId

-- | API-level triality guarantee: bulk projection matches explicit boundary sum.
api-triality-bulk : _⇒ᶜ*_ trialityBᵍ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ))
api-triality-bulk = trialityBulkFactor

record LRetraction : Set where
  field
    embedL    : Diagram Σ₁₀ L¹ B¹
    projectL  : Diagram Σ₁₀ B¹ L¹
    retractL  : _⇒ᶜ*_ (projectL ∘ embedL) idL

L-retraction-witness : LRetraction
L-retraction-witness = record
  { embedL   = ιLᵍ
  ; projectL = νLᵍ
  ; retractL = retractLId
  }

record RRetraction : Set where
  field
    embedR    : Diagram Σ₁₀ R¹ B¹
    projectR  : Diagram Σ₁₀ B¹ R¹
    retractR  : _⇒ᶜ*_ (projectR ∘ embedR) idR

R-retraction-witness : RRetraction
R-retraction-witness = record
  { embedR   = ιRᵍ
  ; projectR = νRᵍ
  ; retractR = retractRId
  }

record BMembership : Set where
  field
    witness : Diagram Σ₁₀ B¹ B¹

B-membership : BMembership
B-membership = record { witness = idB }

-- | Guarded difference witness exported from the core system.
guarded-difference : GuardedDifference
guarded-difference = guardedDifferenceWitness

-- | Boundary-sum soundness packaged as a witness value (mirrors API helper).
boundary-sum-sound-witness : Σ (_⇒ᶜ_ (νLᵍ ∘ trialityBᵍ)
                                    (νLᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ))))
                               λ _ → _⇒ᶜ_ (νRᵍ ∘ trialityBᵍ)
                                               (νRᵍ ∘ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ)))
boundary-sum-sound-witness = (leftWitness , rightWitness)


record DummyTerm : Set where
  constructor mkTerm
  field
    nfTerm : NormalForm ⊤

open DummyTerm

-- | Derived normal forms used to mirror the API equality tests.
signed0 : Signed
signed0 = signed plus zeroℕ

header₁ : Header
header₁ = mkHeader signed0 signed0 zeroℕ zeroℕ

header₂ : Header
header₂ = header₁

header₃ : Header
header₃ = mkHeader signed0 signed0 (sucℕ zeroℕ) zeroℕ

nf₁ : NormalForm ⊤
nf₁ = mkNF header₁ tt

nf₂ : NormalForm ⊤
nf₂ = mkNF header₂ tt

nf₃ : NormalForm ⊤
nf₃ = mkNF header₃ tt

term₁ term₂ term₃ : DummyTerm
term₁ = mkTerm nf₁
term₂ = mkTerm nf₂
term₃ = mkTerm nf₃

-- | Equality up to normal form is propositional equality of the stored NF.
equalUpToNF : DummyTerm → DummyTerm → Set
equalUpToNF t₁ t₂ = nfTerm t₁ ≡ nfTerm t₂

nfEqual : NormalForm ⊤ → NormalForm ⊤ → Set
nfEqual x y = x ≡ y

equalUpToDelta : DummyTerm → DummyTerm → Set
equalUpToDelta = equalUpToNF

-- | Reflexivity witnesses used by the Racket API tests.
term₁-nf-eq : equalUpToNF term₁ term₁
term₁-nf-eq = refl

term₁₂-nf-eq : equalUpToNF term₁ term₂
term₁₂-nf-eq = refl

nf₁-eq : nfEqual nf₁ nf₂
nf₁-eq = refl

term₁-delta-eq : equalUpToDelta term₁ term₂
term₁-delta-eq = refl

-- | Distinct headers break equality, mirroring negative rackunit checks.
suc≠zero : sucℕ zeroℕ ≡ zeroℕ → ⊥
suc≠zero ()

term₁≠term₃ : equalUpToNF term₁ term₃ → ⊥
term₁≠term₃ eq = suc≠zero (sym (cong scaleL (cong header eq)))

nf₁≠nf₃ : nfEqual nf₁ nf₃ → ⊥
nf₁≠nf₃ eq = suc≠zero (sym (cong scaleL (cong header eq)))

deltaWitness : Domain deltaPSDM nf₁
deltaWitness = (sucℕ zeroℕ , pos-suc zeroℕ)

cumulantWitness : Domain cumulantPSDM nf₁
cumulantWitness = (sucℕ zeroℕ , pos-suc zeroℕ)

psdm-id : apply identityPSDM nf₁ tt ≡ nf₁
psdm-id = psdmIdentity nf₁

deltaStableWitness : Domain deltaPSDM (DeltaNF nf₁)
deltaStableWitness = psdmDeltaStable nf₁ deltaWitness

cumulantStableWitness : Domain cumulantPSDM (CumulantNF nf₁)
cumulantStableWitness = psdmCumulantStable nf₁ cumulantWitness

psdm-delta-normal : apply deltaPSDM nf₁ deltaWitness ≡ DeltaNF nf₁
psdm-delta-normal = refl

psdm-delta-commute : DeltaNF (apply deltaPSDM nf₁ deltaWitness) ≡
  apply deltaPSDM (DeltaNF nf₁) deltaStableWitness
psdm-delta-commute = psdmDeltaCommute nf₁ deltaWitness

psdm-cumulant-normal : apply cumulantPSDM nf₁ cumulantWitness ≡ CumulantNF nf₁
psdm-cumulant-normal = refl

psdm-cumulant-commute : CumulantNF (apply cumulantPSDM nf₁ cumulantWitness) ≡
  apply cumulantPSDM (CumulantNF nf₁) cumulantStableWitness
psdm-cumulant-commute = psdmCumulantCommute nf₁ cumulantWitness
term₁≠term₃-delta : equalUpToDelta term₁ term₃ → ⊥
term₁≠term₃-delta = term₁≠term₃
