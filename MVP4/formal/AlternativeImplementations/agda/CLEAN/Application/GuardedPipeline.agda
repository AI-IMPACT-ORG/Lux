module CLEAN.Application.GuardedPipeline where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)

open import CLEAN.Core.System using (_⇒ᶜ*_; guardNANDᵍ; guardNegᵍ; idL; tensorLᵍ; guardNANDDerived)
open import CLEAN.Core.Diagram using (_∘_; _⊗_)
open import CLEAN.Core.Renormalisability using (cleanRenormalisable)
open import CLEAN.Application.KernelRenormalisability
open import CLEAN.Application.Complexity
open import CLEAN.Application.Classification

------------------------------------------------------------------------
-- Guarded fragment pipeline tying kernel and complexity invariants together.
------------------------------------------------------------------------

record GuardedPipeline : Set₁ where
  constructor mkPipeline
  field
    guardWitness    : _⇒ᶜ*_ guardNANDᵍ (guardNegᵍ ∘ (idL ⊗ tensorLᵍ))
    kernelBundle    : KernelCCC
    kernelAgreement : kernelRenormalisation kernelBundle ≡ cleanRenormalisable
    stratifiedLogic : StratifiedLogic
    stratifiedShape : logicInvariants stratifiedLogic ≡ (FirstOrder , NPClass)
    npPort          : NPDecisionPort
    portWitness     : npPort ≡ npDecisionPort

open GuardedPipeline public

-- | The existing artefacts assemble into a single guarded pipeline certificate.
canonicalGuardedPipeline : GuardedPipeline
canonicalGuardedPipeline = mkPipeline
  guardNANDDerived
  cleanKernelCCC
  kernelWitness-agrees
  npStratified
  refl
  npDecisionPort
  refl
