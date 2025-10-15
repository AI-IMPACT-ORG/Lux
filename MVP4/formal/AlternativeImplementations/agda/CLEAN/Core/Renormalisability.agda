module CLEAN.Core.Renormalisability where

open import CLEAN.Core.System
open CLEAN.Core.System
open import CLEAN.Core.NormalForm
open import CLEAN.Core.Rewrite
open import CLEAN.Core.Signature using (Σ₁₀)
open import CLEAN.Core.Diagram using (_∘_; _⊗_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open NormalForm

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import CLEAN.Core.Proofs.PSDM using (psdmIdentity; psdmDeltaStable; psdmDeltaCommute; psdmCumulantStable; psdmCumulantCommute)

-- | Minimal collection of rewrite witnesses required for renormalisability.
record RenormalisationWitness : Set where
  constructor mkWitness
  field
    retractLWitness        : _⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL
    retractRWitness        : _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
    trialityWitness        : _⇒ᶜ*_ trialityBᵍ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ))
    guardedWitness         : _⇒ᶜ*_ guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))
    braidWitness           : _⇒ᶜ*_ (braidBBᵍ ∘ braidBBᵍ) idBB
    deltaBulkWitness       : _⇒ᶜ*_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
    deltaCumulantWitness   : _⇒ᶜ*_ (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)

-- | The CLEAN rewrite family supplies all required witnesses.
cleanRenormalisable : RenormalisationWitness
cleanRenormalisable = mkWitness
  retractLId
  retractRId
  trialityBulkFactor
  guardNANDDerived
  braidInvolutive
  deltaBulkSum
  deltaCumulantCommute

-- | PSDM bundle showing the analytic side of renormalisability.
record PSDMRenormalisation {Core : Set} (nf : NormalForm Core) : Set where
  constructor mkPSDMRen
  field
    deltaDomain      : Domain deltaPSDM nf
    cumulantDomain   : Domain cumulantPSDM nf
    identityStable   : apply identityPSDM nf tt ≡ nf
    deltaStable      : Domain deltaPSDM (DeltaNF nf)
    cumulantStable   : Domain cumulantPSDM (CumulantNF nf)
    deltaCommutes    : DeltaNF (apply deltaPSDM nf deltaDomain)
                        ≡ apply deltaPSDM (DeltaNF nf) deltaStable
    cumulantCommutes : CumulantNF (apply cumulantPSDM nf cumulantDomain)
                        ≡ apply cumulantPSDM (CumulantNF nf) cumulantStable

-- | Instantiate the PSDM bundle with the default positive budgets.
defaultPSDMRenormalisation : ∀ {Core} (nf : NormalForm Core)
  → PSDMRenormalisation nf
defaultPSDMRenormalisation nf =
  mkPSDMRen
    (suc zero , pos-suc zero)
    (suc zero , pos-suc zero)
    (psdmIdentity nf)
    (psdmDeltaStable nf (suc zero , pos-suc zero))
    (psdmCumulantStable nf (suc zero , pos-suc zero))
    (psdmDeltaCommute nf (suc zero , pos-suc zero))
    (psdmCumulantCommute nf (suc zero , pos-suc zero))

-- | A rule family is renormalisable when it supplies the core witnesses.
record Renormalisable (F : RuleFamily Σ₁₀) : Set where
  field
    witness : RenormalisationWitness

-- | CLEAN.System is renormalisable via the default bundle.
cleanRenormalisableFamily : Renormalisable ruleFamily
cleanRenormalisableFamily = record { witness = cleanRenormalisable }

-- | Minimal rule identifiers required for renormalisability.
data MinimalRule : RuleId → Set where
  minRetractL        : MinimalRule RetractL
  minRetractR        : MinimalRule RetractR
  minTriality        : MinimalRule TrialityBulk
  minGuarded         : MinimalRule GuardedNAND
  minBraid           : MinimalRule BraidInvolutive
  minDeltaBulk       : MinimalRule DeltaBulkSum
  minDeltaCumulant   : MinimalRule DeltaCumulantCommute
