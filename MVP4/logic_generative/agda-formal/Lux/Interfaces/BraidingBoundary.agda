-- (c) 2025 AI.IMPACT GmbH

{-# OPTIONS --cubical --without-K #-}

module Lux.Interfaces.BraidingBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Lux.Foundations.Types
open import Lux.Core.Kernel

-- Braiding boundary interface for induced automorphisms
-- Purpose: Define adL/adR commuting squares interface
-- Status: Core interface definition
-- Dependencies: Lux.Foundations.Types, Lux.Core.Kernel

record BraidingBoundaryInterface 
  (carriers : TrialityCarriers)
  (left-semiring : LeftSemiring carriers)
  (right-semiring : RightSemiring carriers)
  (bulk-semiring : BulkSemiring carriers)
  (observer-system : ObserverSystem carriers left-semiring right-semiring bulk-semiring)
  (braiding-operations : BraidingOperations carriers bulk-semiring) : Set₁ where
  
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open RightSemiring right-semiring
  open BulkSemiring bulk-semiring
  open ObserverSystem observer-system
  open BraidingOperations braiding-operations
  
  field
    -- Induced boundary automorphisms
    adL : Left → Left
    adR : Right → Right
    
    -- Commuting squares with observers/embeddings
    adL-commutes-νL : ∀ (t : Bulk) → adL (νL t) ≡ νL (ad₀ t)
    adR-commutes-νR : ∀ (t : Bulk) → adR (νR t) ≡ νR (ad₀ t)
    
    adL-commutes-ιL : ∀ (l : Left) → ιL (adL l) ≡ ad₁ (ιL l)
    adR-commutes-ιR : ∀ (r : Right) → ιR (adR r) ≡ ad₂ (ιR r)
    
    -- Yang-Baxter compatibility
    adL-preserves-ad₀ : ∀ (t : Bulk) → ad₀ (ad₀ t) ≡ ad₀ t
    adR-preserves-ad₀ : ∀ (t : Bulk) → ad₀ (ad₀ t) ≡ ad₀ t
    
    -- Boundary preservation
    adL-preserves-boundary : ∀ (l : Left) → νL (ιL (adL l)) ≡ adL l
    adR-preserves-boundary : ∀ (r : Right) → νR (ιR (adR r)) ≡ adR r
