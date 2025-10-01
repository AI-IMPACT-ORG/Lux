module CLEAN.Application.KernelRenormalisability where

open import Agda.Builtin.Equality using (_≡_; refl)

open import CLEAN.Core.Renormalisability
open import CLEAN.Core.System
open import CLEAN.Core.Diagram using (_∘_; _⊗_)

------------------------------------------------------------------------
-- Kernel-flavoured derivation of the renormalisability witness.
------------------------------------------------------------------------

-- | Abstract kernel data capturing the cartesian closed flavour of CLEAN.
record KernelCCC : Set where
  constructor mkKernelCCC
  field
    kernelL          : _⇒ᶜ*_ (νLᵍ ∘ ιLᵍ) idL
    kernelR          : _⇒ᶜ*_ (νRᵍ ∘ ιRᵍ) idR
    evaluationKernel : _⇒ᶜ*_ trialityBᵍ (bulkSumᵍ ∘ (ιLᵍ ⊗ ιRᵍ))
    unitKernel       : _⇒ᶜ*_ guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))
    symmetryKernel   : _⇒ᶜ*_ (braidBBᵍ ∘ braidBBᵍ) idBB
    deltaTensor      : _⇒ᶜ*_ (deltaᵍ ∘ bulkSumᵍ) (bulkSumᵍ ∘ (deltaᵍ ⊗ deltaᵍ))
    deltaCumulant    : _⇒ᶜ*_ (deltaᵍ ∘ cumulantᵍ) (cumulantᵍ ∘ deltaᵍ)

open KernelCCC public

-- | Core derivation: a kernel-CCC bundle induces a renormalisability witness.
kernelRenormalisation : KernelCCC → RenormalisationWitness
kernelRenormalisation K =
  mkWitness
    (kernelL K)
    (kernelR K)
    (evaluationKernel K)
    (unitKernel K)
    (symmetryKernel K)
    (deltaTensor K)
    (deltaCumulant K)

-- | CLEAN furnishes the required cartesian/kernal data directly.
cleanKernelCCC : KernelCCC
cleanKernelCCC =
  mkKernelCCC
    retractLId
    retractRId
    trialityBulkFactor
    guardNANDDerived
    braidInvolutive
    deltaBulkSum
    deltaCumulantCommute

-- | Second derivation of the renormalisability witness via KernelCCC.
kernelDerivedWitness : RenormalisationWitness
kernelDerivedWitness = kernelRenormalisation cleanKernelCCC

-- | The kernel-derived witness coincides with the original construction.
kernelWitness-agrees : kernelDerivedWitness ≡ cleanRenormalisable
kernelWitness-agrees = refl
