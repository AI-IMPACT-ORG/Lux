module CLEAN.Tests.PSDM where

open import CLEAN.Library
open NormalForm

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat renaming (zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.Sigma using (Σ; _,_)

sampleHeader : Header
sampleHeader = mkHeader (signed plus zeroℕ) (signed plus zeroℕ) zeroℕ zeroℕ

sampleNF : NormalForm ⊤
sampleNF = mkNF sampleHeader tt

deltaWitness : Domain deltaPSDM sampleNF
deltaWitness = (sucℕ zeroℕ , pos-suc zeroℕ)

cumulantWitness : Domain cumulantPSDM sampleNF
cumulantWitness = (sucℕ zeroℕ , pos-suc zeroℕ)

deltaStableWitness : Domain deltaPSDM (DeltaNF sampleNF)
deltaStableWitness = stableDelta deltaPSDM {nf = sampleNF} deltaWitness

cumulantStableWitness : Domain cumulantPSDM (CumulantNF sampleNF)
cumulantStableWitness = stableCumulant cumulantPSDM {nf = sampleNF} cumulantWitness

-- | Identity PSDM acts as the identity map on normal forms.
psdm-id-sound : apply identityPSDM sampleNF tt ≡ sampleNF
psdm-id-sound = refl

-- | Δ-PSDM produces the Δ-normal form and enjoys delta-commutation law.
psdm-delta-commute :
  DeltaNF (apply deltaPSDM sampleNF deltaWitness) ≡
  apply deltaPSDM (DeltaNF sampleNF) deltaStableWitness
psdm-delta-commute = refl

-- | Cumulant PSDM produces the cumulant-normal form.
psdm-cumulant-commute :
  CumulantNF (apply cumulantPSDM sampleNF cumulantWitness) ≡
  apply cumulantPSDM (CumulantNF sampleNF) cumulantStableWitness
psdm-cumulant-commute = refl
