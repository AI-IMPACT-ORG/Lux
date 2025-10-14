-- Lux Logic System - Performance Monitoring (Abstract)
--
-- PURPOSE: Abstract performance metrics and validators for test runs.
-- STATUS: Active - Abstract, compiles without IO.

{-# OPTIONS --cubical --without-K #-}

module Lux.Tests.Utils.PerformanceMonitoring where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true)

open import Lux.Foundations.Types

-- Abstract metric type (pure, no IO)
record Metrics : Set where
  field
    total-tests : ℕ
    passed-tests : ℕ

-- Abstract validators
record PerformanceValidators : Set where
  field
    is-healthy : Metrics → Bool
    is-regressing : Metrics → Metrics → Bool

-- Default abstract instance
default-validators : PerformanceValidators
default-validators = record
  { is-healthy = λ m → true
  ; is-regressing = λ old new → true
  }



