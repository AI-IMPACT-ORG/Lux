-- Lux Logic System - Foundational Types
--
-- PURPOSE: Core foundational types and basic operations
-- STATUS: Active - Foundational types module
-- DEPENDENCIES: Minimal Agda primitives
--
-- Provides basic types needed throughout the Lux system:
-- - Product types
-- - Maybe type for partiality
-- - Natural numbers and integers
-- - Basic arithmetic operations

{-# OPTIONS --cubical --without-K #-}

module Lux.Foundations.Types where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

-- ============================================================================
-- PRODUCT TYPES
-- ============================================================================

-- Product type definition
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

-- ============================================================================
-- PARTIALITY TYPES
-- ============================================================================

-- Maybe type for partiality
data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

-- ============================================================================
-- NATURAL NUMBERS
-- ============================================================================

-- Natural numbers (minimal implementation)
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- Natural number addition
_+ℕ_ : ℕ → ℕ → ℕ
zero +ℕ m = m
suc n +ℕ m = suc (n +ℕ m)

-- ============================================================================
-- INTEGERS
-- ============================================================================

-- Integers (minimal implementation)
data ℤ : Set where
  pos : ℕ → ℤ
  neg : ℕ → ℤ

-- Natural number subtraction (returns integer)
_-ℕ_ : ℕ → ℕ → ℤ
zero -ℕ zero = pos zero
zero -ℕ suc m = neg (suc m)
suc n -ℕ zero = pos (suc n)
suc n -ℕ suc m = n -ℕ m

-- Integer addition
_+ℤ_ : ℤ → ℤ → ℤ
pos n +ℤ pos m = pos (n +ℕ m)
pos n +ℤ neg m = n -ℕ m
neg n +ℤ pos m = m -ℕ n
neg n +ℤ neg m = neg (n +ℕ m)

-- Natural number multiplication
_*ℕ_ : ℕ → ℕ → ℕ
zero *ℕ m = zero
suc n *ℕ m = m +ℕ (n *ℕ m)

-- Integer multiplication
_*ℤ_ : ℤ → ℤ → ℤ
pos n *ℤ pos m = pos (n *ℕ m)
pos n *ℤ neg m = neg (n *ℕ m)
neg n *ℤ pos m = neg (n *ℕ m)
neg n *ℤ neg m = pos (n *ℕ m)

-- ============================================================================
-- INTEGER HEADERS
-- ============================================================================

-- Integer headers for exp/log structure
record IntegerHeaders : Set where
  field
    kφ : ℤ  -- Phase header
    mz : ℤ  -- Left presentation header
    mz̄ : ℤ  -- Right presentation header

-- Scale header: m_Λ(t) := m_z(t) + m_{\bar{z}}(t) ∈ ℤ
scale-header : IntegerHeaders → ℤ
scale-header h = IntegerHeaders.mz h +ℤ IntegerHeaders.mz̄ h

