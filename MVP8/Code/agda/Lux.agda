-- Lux — Axiomatic Triality Logic Library (public entrypoint)
-- Re-exports core structures and stable interfaces.
-- Phase 2: Optimized dependency structure and minimal public API

{-# OPTIONS --cubical --without-K #-}

module Lux where

-- ============================================================================
-- CORE FOUNDATIONS (Essential Axioms A0-A7)
-- ============================================================================

-- Core mathematical foundations implementing Lux Axioms
open import Lux.Core.Kernel public

-- ============================================================================
-- CONSOLIDATED MODULES (Phase 1 & 2 Improvements)
-- ============================================================================

-- Mathematical properties derived from axioms
open import Lux.Core.MathematicalProperties public

-- Logic system for foundational logic
open import Lux.Core.LogicSystem public

-- Unified integration structure
open import Lux.Core.UnifiedStructure public

-- ============================================================================
-- SPECIALIZED INTERFACES (Optional Extensions)
-- ============================================================================

-- Normal form operations
open import Lux.Core.NF public

-- Truth theorems
open import Lux.Core.TruthTheorems public

-- ============================================================================
-- EXAMPLE MODELS (Optional Witnesses)
-- ============================================================================

-- Laurent model implementation
open import Lux.Models.LaurentModel public


