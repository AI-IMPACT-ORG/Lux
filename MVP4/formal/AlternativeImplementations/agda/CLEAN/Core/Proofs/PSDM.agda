module CLEAN.Core.Proofs.PSDM where

open import CLEAN.Core.NormalForm
open NormalForm

open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

-- | Identity PSDM acts as identity on any normal form.
psdmIdentity : ∀ {Core} (nf : NormalForm Core) → apply identityPSDM nf tt ≡ nf
psdmIdentity _ = refl

-- | Expose the Δ-PSDM stability witness from the record.
psdmDeltaStable : ∀ {Core} (nf : NormalForm Core) (d : Domain deltaPSDM nf)
  → Domain deltaPSDM (DeltaNF nf)
psdmDeltaStable nf d = stableDelta deltaPSDM {nf = nf} d

-- | Δ commutation lemma unpacked from the PSDM record.
psdmDeltaCommute : ∀ {Core} (nf : NormalForm Core) (d : Domain deltaPSDM nf)
  → DeltaNF (apply deltaPSDM nf d)
  ≡ apply deltaPSDM (DeltaNF nf) (psdmDeltaStable nf d)
psdmDeltaCommute nf d = commuteDelta deltaPSDM d

-- | Expose the cumulant PSDM stability witness from the record.
psdmCumulantStable : ∀ {Core} (nf : NormalForm Core) (d : Domain cumulantPSDM nf)
  → Domain cumulantPSDM (CumulantNF nf)
psdmCumulantStable nf d = stableCumulant cumulantPSDM {nf = nf} d

-- | Cumulant commutation lemma unpacked from the PSDM record.
psdmCumulantCommute : ∀ {Core} (nf : NormalForm Core) (d : Domain cumulantPSDM nf)
  → CumulantNF (apply cumulantPSDM nf d)
  ≡ apply cumulantPSDM (CumulantNF nf) (psdmCumulantStable nf d)
psdmCumulantCommute nf d = commuteCumulant cumulantPSDM d
