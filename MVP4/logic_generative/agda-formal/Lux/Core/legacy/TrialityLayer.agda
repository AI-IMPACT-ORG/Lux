-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - Triality Layer (V10 Core Constructive Logic)
--
-- PURPOSE: V10 Core constructive logic layer
-- STATUS: Active - Triality layer module
-- DEPENDENCIES: Lux.Core.Kernel
--
-- This module implements the V10 Core requirements:
-- - Triality operations (starB, starL, starR)
-- - Triality functors (T_L, T_R, T_B)
-- - Definitional on top of V2 (no new axioms)

{-# OPTIONS --cubical --without-K #-}

module Lux.Core.TrialityLayer where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Lux.Core.Kernel

-- ============================================================================
-- TRIALITY OPERATIONS
-- ============================================================================

-- Triality operations (V10 Core requirement)
record TrialityOperations (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open RightSemiring right-semiring
  open BulkSemiring bulk-semiring
  field
    starB : Bulk → Bulk
    starL : Left → Left
    starR : Right → Right
    star-involutive-B : ∀ (t : Bulk) → starB (starB t) ≡ t
    star-involutive-L : ∀ (x : Left) → starL (starL x) ≡ x
    star-involutive-R : ∀ (y : Right) → starR (starR y) ≡ y

-- ============================================================================
-- TRIALITY FUNCTORS
-- ============================================================================

-- Triality functors (V10 Core requirement)
record TrialityFunctors (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (right-semiring : RightSemiring carriers) (bulk-semiring : BulkSemiring carriers) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open RightSemiring right-semiring
  open BulkSemiring bulk-semiring
  field
    TL : Bulk → Bulk
    TR : Bulk → Bulk
    TB : Bulk → Bulk
    triality-functor-properties : ∀ (t : Bulk) → (TL t ⊕B TR t) ⊕B TB t ≡ t

-- ============================================================================
-- TRIALITY LAYER STRUCTURE
-- ============================================================================

-- Triality layer structure
record TrialityLayerStructure (core-kernel : CoreKernelStructure) : Set₁ where
  open CoreKernelStructure core-kernel
  field
    triality-ops : TrialityOperations carriers left-semiring right-semiring bulk-semiring
    triality-functors : TrialityFunctors carriers left-semiring right-semiring bulk-semiring
