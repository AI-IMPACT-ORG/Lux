-- Lux — Axiomatic Triality Logic Library (public entrypoint)
-- Re-exports core structures and stable interfaces.

{-# OPTIONS --cubical --without-K #-}

module Lux where

-- Core foundations
open import CLEAN.Core.Kernel public
open import CLEAN.Core.TrialityOperations public
open import CLEAN.Core.ModuliSystem public
open import CLEAN.Core.AdvancedOperations public
open import CLEAN.Core.NF public

-- Interfaces / integration
open import CLEAN.Core.GuardedNegation public
open import CLEAN.Core.DomainPorts public
open import CLEAN.Core.TruthTheorems public
open import CLEAN.Core.MathematicalInsights public
open import CLEAN.Core.Karoubi2BI public

-- Example model scaffolding (optional witness)
open import CLEAN.Models.V2LaurentModel public


