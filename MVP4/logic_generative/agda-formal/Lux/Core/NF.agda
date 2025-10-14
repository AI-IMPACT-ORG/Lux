{-# OPTIONS --cubical --without-K #-}

module Lux.Core.NF where

open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Lux.Foundations.Types
open import Lux.Core.Kernel
open import Lux.Core.Headers

-- Public NF APIs (tuple, B-valued, and 4-moduli B-valued)

record NFAPI (core : CoreKernelStructure) : Set₁ where
  open CoreKernelStructure core
  open TrialityCarriers carriers
  open BulkSemiring bulk-semiring
  open CoreSemiring core-semiring
  field
    -- Tuple NF: B → (kφ : ℤ) × (mΛ : ℤ) × Core
    NF : Bulk → ℤ × ℤ × Core

    -- B-valued NF: header-only repacking in B
    NF^B : Bulk → Bulk

    -- 4-moduli B-valued NF (boundary-aware) with integer endomorphisms
    NF^B-4mod : (fθL fθR gμL gμR : ℤ → ℤ) → Bulk → Bulk

    -- Observer invariance (header-only): ν_* commute with NF^B
    νL-commutes : ∀ t → νL (NF^B t) ≡ νL t
    νR-commutes : ∀ t → νR (NF^B t) ≡ νR t

-- Default NFAPI built from ExpLogStructure and HeaderOperations
makeNFAPI : (core : CoreKernelStructure)
          → (headers : HeaderOperations (CoreKernelStructure.carriers core)
                                       (CoreKernelStructure.left-semiring core)
                                       (CoreKernelStructure.right-semiring core)
                                       (CoreKernelStructure.bulk-semiring core)
                                       (CoreKernelStructure.observers core)
                                       (CoreKernelStructure.central-scalars core))
          → NFAPI core
makeNFAPI core headers = record
  { NF = λ t → (0ℤ , 0ℤ , oneCore)
  ; NF^B = λ t → t
  ; NF^B-4mod = λ fθL fθR gμL gμR t → t
  ; νL-commutes = λ t → refl
  ; νR-commutes = λ t → refl
  }

-- Note: This is a public API shim. Concrete models should override
-- with real dec/rec and header projections. The default preserves types
-- and header-only contract used by Core and CLASS layers.

