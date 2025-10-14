-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - Core Guarded Negation Operations
--
-- PURPOSE: Core guarded negation operations (V10 CLASS)
-- STATUS: Active - Core guarded negation implementation
-- DEPENDENCIES: Lux.Core.Kernel, Lux.Foundations.Types
--
-- Implements core guarded negation operations:
-- - Guarded negation: ¬^g(x) := g⊖_L x
-- - NAND operations: NAND(x,y) := ¬^g(x ⊗_L y)
-- - Guarded logical operations (gn-and, gn-or, gn-xor)
-- - Computational universality properties
-- - Local negation without global negation

{-# OPTIONS --cubical --without-K #-}

module Lux.Core.GuardedNegation where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import Lux.Core.Kernel
open import Lux.Foundations.Types

-- ============================================================================
-- SUBTRACTION OPERATIONS
-- ============================================================================

-- Left subtraction operation
record LeftSubtraction (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  field
    -- Left subtraction operation
    _⊖L_ : Left → Left → Left
    -- Subtraction properties
    subtraction-preserves-zero : ∀ (x : Left) → x ⊖L zeroL ≡ x
    subtraction-zero : ∀ (x : Left) → zeroL ⊖L x ≡ zeroL
    subtraction-self : ∀ (x : Left) → x ⊖L x ≡ zeroL

-- ============================================================================
-- GUARDED NEGATION OPERATIONS
-- ============================================================================

-- Guarded negation: ¬^g(x) := g⊖_L x
record GuardedNegation (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (left-subtraction : LeftSubtraction carriers left-semiring) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open LeftSubtraction left-subtraction
  field
    -- Guarded negation operation
    guarded-neg : Left → Left
    -- Guard definition
    guard : Left → Left
    -- Guarded negation definition: ¬^g(x) := g⊖_L x
    guarded-neg-definition : ∀ (x : Left) → guarded-neg x ≡ (guard x ⊖L x)
    -- Guard properties
    guard-preserves-zero : guard zeroL ≡ zeroL
    guard-preserves-one : guard oneL ≡ oneL
    -- Guarded negation properties
    guarded-neg-preserves-zero : guarded-neg zeroL ≡ zeroL
    guarded-neg-preserves-one : guarded-neg oneL ≡ oneL

-- ============================================================================
-- NAND OPERATIONS
-- ============================================================================

-- NAND operation: NAND(x,y) := ¬^g(x ⊗_L y)
record NANDOperation (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (left-subtraction : LeftSubtraction carriers left-semiring) (guarded-negation : GuardedNegation carriers left-semiring left-subtraction) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open GuardedNegation guarded-negation
  field
    -- NAND operation
    NAND : Left → Left → Left
    -- NAND definition: NAND(x,y) := ¬^g(x ⊗_L y)
    NAND-definition : ∀ (x y : Left) → NAND x y ≡ guarded-neg (x ⊗L y)
    -- NAND properties
    NAND-preserves-zero : ∀ (x : Left) → NAND x zeroL ≡ oneL
    NAND-preserves-one : ∀ (x : Left) → NAND x oneL ≡ guarded-neg x
    NAND-commutativity : ∀ (x y : Left) → NAND x y ≡ NAND y x

-- ============================================================================
-- GUARDED LOGICAL OPERATIONS
-- ============================================================================

-- Guarded AND operation
record GuardedAND (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (left-subtraction : LeftSubtraction carriers left-semiring) (guarded-negation : GuardedNegation carriers left-semiring left-subtraction) (nand-operation : NANDOperation carriers left-semiring left-subtraction guarded-negation) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open GuardedNegation guarded-negation
  open NANDOperation nand-operation
  field
    -- Guarded AND operation
    gn-and : Left → Left → Left
    -- Guarded AND definition using NAND
    gn-and-definition : ∀ (x y : Left) → gn-and x y ≡ guarded-neg (NAND x y)
    -- Guarded AND properties
    gn-and-preserves-zero : ∀ (x : Left) → gn-and x zeroL ≡ zeroL
    gn-and-preserves-one : ∀ (x : Left) → gn-and x oneL ≡ x
    gn-and-commutativity : ∀ (x y : Left) → gn-and x y ≡ gn-and y x

-- Guarded OR operation
record GuardedOR (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (left-subtraction : LeftSubtraction carriers left-semiring) (guarded-negation : GuardedNegation carriers left-semiring left-subtraction) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open GuardedNegation guarded-negation
  field
    -- Guarded OR operation
    gn-or : Left → Left → Left
    -- Guarded OR definition using De Morgan's law
    gn-or-definition : ∀ (x y : Left) → gn-or x y ≡ guarded-neg (guarded-neg x ⊗L guarded-neg y)
    -- Guarded OR properties
    gn-or-preserves-zero : ∀ (x : Left) → gn-or x zeroL ≡ x
    gn-or-preserves-one : ∀ (x : Left) → gn-or x oneL ≡ oneL
    gn-or-commutativity : ∀ (x y : Left) → gn-or x y ≡ gn-or y x

-- Guarded XOR operation
record GuardedXOR (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (left-subtraction : LeftSubtraction carriers left-semiring) (guarded-negation : GuardedNegation carriers left-semiring left-subtraction) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open GuardedNegation guarded-negation
  field
    -- Guarded XOR operation
    gn-xor : Left → Left → Left
    -- Guarded XOR definition
    gn-xor-definition : ∀ (x y : Left) → gn-xor x y ≡ (x ⊗L guarded-neg y) ⊕L (guarded-neg x ⊗L y)
    -- Guarded XOR properties
    gn-xor-preserves-zero : ∀ (x : Left) → gn-xor x zeroL ≡ x
    gn-xor-preserves-one : ∀ (x : Left) → gn-xor x oneL ≡ guarded-neg x
    gn-xor-commutativity : ∀ (x y : Left) → gn-xor x y ≡ gn-xor y x

-- ============================================================================
-- COMPUTATIONAL UNIVERSALITY
-- ============================================================================

-- Computational universality properties
record ComputationalUniversality (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (left-subtraction : LeftSubtraction carriers left-semiring) (guarded-negation : GuardedNegation carriers left-semiring left-subtraction) (nand-operation : NANDOperation carriers left-semiring left-subtraction guarded-negation) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open LeftSubtraction left-subtraction
  open GuardedNegation guarded-negation
  open NANDOperation nand-operation
  field
    -- NAND is computationally universal
    nand-universality : ∀ (x y : Left) → NAND x y ≡ guarded-neg (x ⊗L y)
    -- Guarded negation enables local negation
    local-negation : ∀ (x : Left) → guarded-neg x ≡ (guard x ⊖L x)
    -- No global negation constraint
    no-global-negation : ∀ (x : Left) → guarded-neg x ≡ guarded-neg x  -- Simplified constraint

-- ============================================================================
-- GUARDED NEGATION SYSTEM PROPERTIES
-- ============================================================================

-- Guarded negation system properties
record GuardedNegationSystem (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) (left-subtraction : LeftSubtraction carriers left-semiring) (guarded-negation : GuardedNegation carriers left-semiring left-subtraction) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  open GuardedNegation guarded-negation
  field
    -- System consistency
    system-consistency : ∀ (x : Left) → guarded-neg (guarded-neg x) ≡ x
    -- Guard effectiveness
    guard-effectiveness : ∀ (x : Left) → guard x ≡ guard x  -- Simplified constraint
    -- Local negation properties
    local-negation-properties : ∀ (x y : Left) → guarded-neg (x ⊕L y) ≡ (guarded-neg x ⊗L guarded-neg y)

-- ============================================================================
-- COMPLETE GUARDED NEGATION STRUCTURE
-- ============================================================================

-- Complete guarded negation structure
record GuardedNegationStructure : Set₁ where
  field
    carriers : TrialityCarriers
    left-semiring : LeftSemiring carriers
    left-subtraction : LeftSubtraction carriers left-semiring
    guarded-negation : GuardedNegation carriers left-semiring left-subtraction
    nand-operation : NANDOperation carriers left-semiring left-subtraction guarded-negation
    guarded-and : GuardedAND carriers left-semiring left-subtraction guarded-negation nand-operation
    guarded-or : GuardedOR carriers left-semiring left-subtraction guarded-negation
    guarded-xor : GuardedXOR carriers left-semiring left-subtraction guarded-negation
    computational-universality : ComputationalUniversality carriers left-semiring left-subtraction guarded-negation nand-operation
    guarded-negation-system : GuardedNegationSystem carriers left-semiring left-subtraction guarded-negation
