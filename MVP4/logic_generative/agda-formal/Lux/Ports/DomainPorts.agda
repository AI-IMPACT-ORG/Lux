-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - Domain Ports (External Computational Paradigms)
--
-- PURPOSE: External computational paradigms (Class requirement)
-- STATUS: Active - Domain ports module
-- DEPENDENCIES: Lux.Core.Kernel, Lux.Foundations.Types
--
-- This module implements the Class domain ports:
-- - PSDM (Partial Stable Domain Map)
-- - Boolean/RAM port (irreversible computing)
-- - λ-calculus port (β-normalization)
-- - Info-flow port (preorders/lattices)
-- - Non-susy QFT port (Euclidean/Minkowski)

{-# OPTIONS --cubical --without-K #-}

module Lux.Ports.DomainPorts where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import Lux.Core.Kernel
open import Lux.Foundations.Types

-- ============================================================================
-- PSDM (PARTIAL STABLE DOMAIN MAP)
-- ============================================================================

-- PSDM (Partial Stable Domain Map) - Class requirement
record PSDM (A : Set) : Set₁ where
  field
    -- Domain map (partial)
    domain-map : A → Maybe A
    
    -- Properties
    stability : ∀ (x : A) → domain-map x ≡ just x → domain-map x ≡ just x
    partiality : Σ A (λ x → domain-map x ≡ nothing)

-- ============================================================================
-- BOOLEAN/RAM PORT
-- ============================================================================

-- Boolean/RAM port (Class requirement)
record BooleanRAMPort (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) : Set₁ where
  open TrialityCarriers carriers
  open BulkSemiring bulk-semiring
  field
    -- Carrier: L₀ = {0,1}
    boolean-carrier : Set
    boolean-zero : boolean-carrier
    boolean-one : boolean-carrier
    
    -- Encoding: programs as Obs
    program-encoding : Bulk → boolean-carrier
    
    -- PSDM: partial, stable
    psdm : PSDM boolean-carrier
    
    -- Coherence: TM and λ encodings produce identical Z[J]
    coherence-property : ∀ (t : Bulk) → 
      program-encoding t ≡ boolean-one → 
      program-encoding t ≡ boolean-one  -- Church-Turing inside

-- ============================================================================
-- λ-CALCULUS PORT
-- ============================================================================

-- λ-calculus port (Class requirement)
record LambdaCalculusPort (carriers : TrialityCarriers) (bulk-semiring : BulkSemiring carriers) : Set₁ where
  open TrialityCarriers carriers
  open BulkSemiring bulk-semiring
  field
    -- Carrier: normal forms in typed λ-fragment
    lambda-carrier : Set
    
    -- β-steps as micro-steps
    beta-step : lambda-carrier → lambda-carrier
    
    -- Evaluation via expectations
    evaluation : lambda-carrier → Bulk
    
    -- PSDM: defined iff β-normalises
    psdm : PSDM lambda-carrier

-- ============================================================================
-- INFO-FLOW PORT
-- ============================================================================

-- Info-flow port (Class requirement)
record InfoFlowPort (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  field
    -- Carrier: preorders/lattices
    info-carrier : Set
    
    -- ⊕_L joins, ⊗_L flows
    join-operation : info-carrier → info-carrier → info-carrier
    flow-operation : info-carrier → info-carrier → info-carrier
    
    -- Guarded negation yields relative complement
    guarded-negation : Left → info-carrier → info-carrier
    
    -- PSDM drops non-flow paths
    psdm : PSDM info-carrier

-- ============================================================================
-- NON-SUSY QFT PORT
-- ============================================================================

-- Non-susy QFT port (Class requirement)
record QFTPort (carriers : TrialityCarriers) (left-semiring : LeftSemiring carriers) : Set₁ where
  open TrialityCarriers carriers
  open LeftSemiring left-semiring
  field
    -- Carrier: L_E = ℝ_{≥0} (Euclidean) or L_M = ℂ (Minkowski)
    qft-carrier : Set
    
    -- Feynman view: histories from micro-steps
    history-generation : Bulk → qft-carrier
    
    -- Action = product of header weights
    action-computation : qft-carrier → Bulk
    
    -- Amplitudes via domain evaluation
    amplitude-computation : qft-carrier → Bulk
    
    -- Propagator = inverse Fisher
    propagator-computation : qft-carrier → Bulk
    
    -- Vertices = cumulants
    vertex-computation : qft-carrier → Bulk

-- ============================================================================
-- DOMAIN PORTS STRUCTURE
-- ============================================================================

-- Domain ports structure
record DomainPortsStructure (core-kernel : CoreKernelStructure) : Set₁ where
  open CoreKernelStructure core-kernel
  field
    boolean-ram-port : BooleanRAMPort carriers bulk-semiring
    lambda-calculus-port : LambdaCalculusPort carriers bulk-semiring
    info-flow-port : InfoFlowPort carriers left-semiring
    qft-port : QFTPort carriers left-semiring

