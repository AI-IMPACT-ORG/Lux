module CLEAN.Ports.Boolean where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)

open import CLEAN.Core.NormalForm
open import CLEAN.Core.Proofs.PSDM

-- | Boolean port domain: regulated normal forms with a positive budget.
BooleanDomain : ∀ {Core} → NormalForm Core → Set
BooleanDomain _ = Σ Nat Positive

-- | Boolean evaluation based on the bulk scale parity.
booleanEval : ∀ {Core} (nf : NormalForm Core) → BooleanDomain nf → Bool
booleanEval (mkNF h _) _ = parity (bulkScale h)
  where
    parity : Nat → Bool
    parity zero = false
    parity (suc n) with parity n
    ... | true  = false
    ... | false = true

-- | Δ preserves the Boolean domain.
booleanDeltaStable : ∀ {Core} (nf : NormalForm Core)
  → BooleanDomain nf → BooleanDomain (DeltaNF nf)
booleanDeltaStable nf d = psdmDeltaStable nf d

-- | Cumulant preserves the Boolean domain.
booleanCumulantStable : ∀ {Core} (nf : NormalForm Core)
  → BooleanDomain nf → BooleanDomain (CumulantNF nf)
booleanCumulantStable nf d = psdmCumulantStable nf d

-- | Δ commutes with Boolean evaluation.
booleanDeltaCommute : ∀ {Core} (nf : NormalForm Core) (d : BooleanDomain nf)
  → booleanEval (DeltaNF nf) (booleanDeltaStable nf d)
  ≡ booleanEval (apply deltaPSDM nf d) d
booleanDeltaCommute (mkNF h _) d = refl

-- | Cumulant commutes with Boolean evaluation.
booleanCumulantCommute : ∀ {Core} (nf : NormalForm Core) (d : BooleanDomain nf)
  → booleanEval (CumulantNF nf) (booleanCumulantStable nf d)
  ≡ booleanEval (apply cumulantPSDM nf d) d
booleanCumulantCommute (mkNF h _) d = refl
