module Lux.Core.Headers where

open import Lux.Foundations.Types
open import Lux.Core.Kernel

-- Header operations and total projections for A6 strengthening
-- Purpose: Add Header record and total projections; explicit header ops
-- Status: Core header operations
-- Dependencies: Lux.Foundations.Types, Lux.Core.Kernel

record HeaderOperations 
  {carriers : Set}
  (left-semiring : LeftSemiring carriers)
  (right-semiring : RightSemiring carriers)
  (bulk-semiring : BulkSemiring carriers)
  (observer-system : ObserverSystem carriers left-semiring right-semiring bulk-semiring)
  (central-scalars : CentralScalars carriers left-semiring right-semiring bulk-semiring observer-system) : Set₁ where
  
  open LeftSemiring left-semiring
  open RightSemiring right-semiring
  open BulkSemiring bulk-semiring
  open ObserverSystem observer-system
  open CentralScalars central-scalars
  
  field
    -- Header operations
    header-L : Left → ℤ
    header-R : Right → ℤ
    header-B : Bulk → ℤ
    
    -- Total projections
    total-L : Left → Bulk
    total-R : Right → Bulk
    total-B : Bulk → Bulk
    
    -- Header preservation properties
    header-L-preserves-⊕ : ∀ (l₁ l₂ : Left) → header-L (l₁ ⊕L l₂) ≡ header-L l₁ +ℤ header-L l₂
    header-R-preserves-⊕ : ∀ (r₁ r₂ : Right) → header-R (r₁ ⊕R r₂) ≡ header-R r₁ +ℤ header-R r₂
    header-B-preserves-⊕ : ∀ (b₁ b₂ : Bulk) → header-B (b₁ ⊕B b₂) ≡ header-B b₁ +ℤ header-B b₂
    
    header-L-preserves-⊗ : ∀ (l₁ l₂ : Left) → header-L (l₁ ⊗L l₂) ≡ header-L l₁ *ℤ header-L l₂
    header-R-preserves-⊗ : ∀ (r₁ r₂ : Right) → header-R (r₁ ⊗R r₂) ≡ header-R r₁ *ℤ header-R r₂
    header-B-preserves-⊗ : ∀ (b₁ b₂ : Bulk) → header-B (b₁ ⊗B b₂) ≡ header-B b₁ *ℤ header-B b₂
    
    -- Total projection properties
    total-L-preserves-⊕ : ∀ (l₁ l₂ : Left) → total-L (l₁ ⊕L l₂) ≡ total-L l₁ ⊕B total-L l₂
    total-R-preserves-⊕ : ∀ (r₁ r₂ : Right) → total-R (r₁ ⊕R r₂) ≡ total-R r₁ ⊕B total-R r₂
    total-B-preserves-⊕ : ∀ (b₁ b₂ : Bulk) → total-B (b₁ ⊕B b₂) ≡ total-B b₁ ⊕B total-B b₂
    
    total-L-preserves-⊗ : ∀ (l₁ l₂ : Left) → total-L (l₁ ⊗L l₂) ≡ total-L l₁ ⊗B total-L l₂
    total-R-preserves-⊗ : ∀ (r₁ r₂ : Right) → total-R (r₁ ⊗R r₂) ≡ total-R r₁ ⊗B total-R r₂
    total-B-preserves-⊗ : ∀ (b₁ b₂ : Bulk) → total-B (b₁ ⊗B b₂) ≡ total-B b₁ ⊗B total-B b₂
    
    -- Header-observer compatibility
    header-L-νL : ∀ (t : Bulk) → header-L (νL t) ≡ header-B t
    header-R-νR : ∀ (t : Bulk) → header-R (νR t) ≡ header-B t
    
    -- Total-observer compatibility
    total-L-νL : ∀ (t : Bulk) → total-L (νL t) ≡ total-B t
    total-R-νR : ∀ (t : Bulk) → total-R (νR t) ≡ total-B t

