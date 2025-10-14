-- Lux Logic System - Karoubi Split and 2BI Interfaces
--
-- PURPOSE: Provide concrete, definitional maps for [L], [R], and ρ using
--          the kernel's observer system, and expose a 2BI interface.
-- STATUS: Active - Definitional functions, proofs left as properties.
-- DEPENDENCIES: Lux.Core.Kernel, Lux.Foundations.Types

{-# OPTIONS --cubical --without-K #-}

module Lux.Core.Karoubi2BI where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Lux.Foundations.Types
open import Lux.Core.Kernel

-- Definitional Karoubi-split data built from the kernel
record KaroubiSplit (core : CoreKernelStructure) : Set₁ where
  open CoreKernelStructure core
  open TrialityCarriers carriers
  open BulkSemiring bulk-semiring
  open ObserverSystem observers
  field
    projectorL : Bulk → Bulk
    projectorR : Bulk → Bulk
    reconstitute : Bulk → Bulk

-- Concrete constructor for the split using kernel observers/embeddings
makeKaroubiSplit : (core : CoreKernelStructure) → KaroubiSplit core
makeKaroubiSplit core =
  let obs = CoreKernelStructure.observers core
      open ObserverSystem obs
      open TrialityCarriers (CoreKernelStructure.carriers core)
      open BulkSemiring (CoreKernelStructure.bulk-semiring core)
  in record
    { projectorL = λ t → ιL (νL t)
    ; projectorR = λ t → ιR (νR t)
    ; reconstitute = λ t → (ιL (νL t)) ⊕B (ιR (νR t))
    }

-- Interfaces for expected algebraic properties (to be supplied per model)
record KaroubiLaws (core : CoreKernelStructure) : Set₁ where
  open CoreKernelStructure core
  open TrialityCarriers carriers
  open BulkSemiring bulk-semiring
  field
    split : KaroubiSplit core
    idempotentL : ∀ t → KaroubiSplit.projectorL split (KaroubiSplit.projectorL split t) ≡ KaroubiSplit.projectorL split t
    idempotentR : ∀ t → KaroubiSplit.projectorR split (KaroubiSplit.projectorR split t) ≡ KaroubiSplit.projectorR split t
    crossAnnihilLR : ∀ t → KaroubiSplit.projectorL split (KaroubiSplit.projectorR split t) ≡ zeroB
    crossAnnihilRL : ∀ t → KaroubiSplit.projectorR split (KaroubiSplit.projectorL split t) ≡ zeroB
    reconstitutionIdempotent : ∀ t → KaroubiSplit.reconstitute split (KaroubiSplit.reconstitute split t) ≡ KaroubiSplit.reconstitute split t


-- 2BI interface: residual and a placeholder for the quotient projection
record TwoBI (core : CoreKernelStructure) (split : KaroubiSplit core) : Set₁ where
  open CoreKernelStructure core
  open TrialityCarriers carriers
  open BulkSemiring bulk-semiring
  field
    residual : Bulk → Bulk
    quotientProjection : Bulk → Bulk
    quotientRespectsReconstitution : ∀ t → quotientProjection (KaroubiSplit.reconstitute split t) ≡ quotientProjection t

-- Helper constructor providing a canonical residual
mkTwoBI : (core : CoreKernelStructure)
        → (split : KaroubiSplit core)
        → (quotientProjection : TrialityCarriers.Bulk (CoreKernelStructure.carriers core) → TrialityCarriers.Bulk (CoreKernelStructure.carriers core))
        → (qrr : ∀ t → quotientProjection (KaroubiSplit.reconstitute split t) ≡ quotientProjection t)
        → TwoBI core split
mkTwoBI core split quotientProjection qrr =
  let open CoreKernelStructure core
      open TrialityCarriers carriers
      open BulkSemiring bulk-semiring
  in record
    { residual = λ t → t ⊕B KaroubiSplit.reconstitute split t
    ; quotientProjection = quotientProjection
    ; quotientRespectsReconstitution = qrr
    }

-- Default identity constructor for TwoBI
mkTwoBI-id : (core : CoreKernelStructure) → (split : KaroubiSplit core) → TwoBI core split
mkTwoBI-id core split =
  let open CoreKernelStructure core
      open TrialityCarriers carriers
      open BulkSemiring bulk-semiring
  in mkTwoBI core split (λ t → zeroB) (λ t → refl)


