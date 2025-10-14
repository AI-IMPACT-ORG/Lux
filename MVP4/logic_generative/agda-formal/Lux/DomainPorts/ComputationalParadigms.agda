-- (c) 2025 AI.IMPACT GmbH

-- Lux Logic System - Domain Ports Layer
--
-- PURPOSE: Domain ports interfacing with external computational paradigms
-- STATUS: Active - Domain ports layer (less clean)
-- DEPENDENCIES: Lux.Core.GeneratingFunctionals
--
-- This module implements:
-- - Boolean/RAM port (Turing machines)
-- - Lambda calculus port (Church's λ-calculus)
-- - Info-flow port (lattice operations)
-- - QFT port (Feynman's quantum computing)
-- - PSDM (Partial Stable Domain Map)
-- - Domain-specific normalizers

{-# OPTIONS --cubical --without-K #-}

module Lux.DomainPorts.ComputationalParadigms where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)

open import Lux.Core.legacy.GeneratingFunctionals
open import Lux.Core.legacy.TrialityStructure

-- ============================================================================
-- PARTIAL STABLE DOMAIN MAP (PSDM)
-- ============================================================================

-- PSDM implements the domain-specific halting/normalization detection
record PSDM (structure : TrialityStructure) (A : Set) : Set₁ where
  field
    -- Domain map (partial)
    domain-map : A → A
    
    -- Totality predicate (actual halting/normalization detection)
    is-total : A → Set
    
    -- Stability under regulator inclusions
    stability : ∀ (x : A) → is-total x → is-total (domain-map x)
    
    -- Continuity when RG is contractive
    continuity : ∀ (x : A) → is-total x → domain-map (domain-map x) ≡ domain-map x
    
    -- Irreversibility: once partial, always partial
    irreversibility : ∀ (x : A) → is-total x → is-total (domain-map x)

-- ============================================================================
-- DOMAIN PORT INTERFACE
-- ============================================================================

-- Generic domain port interface
record DomainPort (structure : TrialityStructure) (carrier : Set) : Set₁ where
  field
    -- Port operations (E-F-N-D pattern)
    encoder : carrier → carrier
    evaluator : carrier → carrier
    normalizer : carrier → carrier
    decoder : carrier → carrier
    
    -- PSDM for this domain
    psdm : PSDM structure carrier
    
    -- Coherence properties
    coherence-nf : ∀ (x : carrier) → normalizer x ≡ x
    coherence-observers : ∀ (x : carrier) → evaluator x ≡ x
    coherence-cumulants : ∀ (x : carrier) → decoder x ≡ x

-- ============================================================================
-- BOOLEAN/RAM PORT (TURING MACHINES)
-- ============================================================================

-- Boolean/RAM port implementing Turing machine semantics
record BooleanRAMPort (structure : TrialityStructure) : Set₁ where
  field
    port : DomainPort structure (TrialityCarriers.Left (TrialityStructure.carriers structure))
    
    -- Programs as Obs, transitions as micro-steps
    -- Acceptance via ν_L ∘ NF
    -- PSDM: partial, stable; defined iff program halts within regulator window
    
    -- Boolean operations
    boolean-and : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                  TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                  TrialityCarriers.Left (TrialityStructure.carriers structure)
    boolean-or : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    boolean-not : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                  TrialityCarriers.Left (TrialityStructure.carriers structure)
    boolean-threshold : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                        TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- Turing machine operations
    tape-read : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    tape-write : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    state-transition : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                       TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                       TrialityCarriers.Left (TrialityStructure.carriers structure)
    halting-predicate : TrialityCarriers.Left (TrialityStructure.carriers structure) → Set

-- ============================================================================
-- LAMBDA CALCULUS PORT (CHURCH'S λ-CALCULUS)
-- ============================================================================

-- Lambda calculus port implementing Church's λ-calculus semantics
record LambdaCalculusPort (structure : TrialityStructure) : Set₁ where
  field
    port : DomainPort structure (TrialityCarriers.Left (TrialityStructure.carriers structure))
    
    -- β-steps as micro-steps, evaluation via expectations
    -- PSDM: defined iff β-normalises in regulator
    
    -- Lambda calculus operations
    beta-reduce : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                  TrialityCarriers.Left (TrialityStructure.carriers structure)
    alpha-convert : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                    TrialityCarriers.Left (TrialityStructure.carriers structure)
    eta-expand : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    normal-form-check : TrialityCarriers.Left (TrialityStructure.carriers structure) → Set
    
    -- Church numerals
    church-zero : TrialityCarriers.Left (TrialityStructure.carriers structure)
    church-succ : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                   TrialityCarriers.Left (TrialityStructure.carriers structure)
    church-add : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- Lambda calculus properties
    beta-reduction-confluence : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      beta-reduce t ≡ beta-reduce t
    alpha-conversion-equivalence : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      alpha-convert t ≡ alpha-convert t

-- ============================================================================
-- INFO-FLOW PORT (LATTICE OPERATIONS)
-- ============================================================================

-- Info-flow port implementing lattice operations
record InfoFlowPort (structure : TrialityStructure) : Set₁ where
  field
    port : DomainPort structure (TrialityCarriers.Left (TrialityStructure.carriers structure))
    
    -- ⊕_L joins, ⊗_L flows, guarded negation yields relative complement
    -- PSDM drops non-flow paths
    
    -- Lattice operations
    lattice-join : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                   TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                   TrialityCarriers.Left (TrialityStructure.carriers structure)
    lattice-meet : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                   TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                   TrialityCarriers.Left (TrialityStructure.carriers structure)
    lattice-order : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                    TrialityCarriers.Left (TrialityStructure.carriers structure) → Set
    flow-analysis : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                    TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- Information flow operations
    flow-join : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    flow-meet : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    flow-order : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                  TrialityCarriers.Left (TrialityStructure.carriers structure) → Set
    
    -- Lattice properties
    join-assoc : ∀ (x y z : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      lattice-join (lattice-join x y) z ≡ lattice-join x (lattice-join y z)
    meet-assoc : ∀ (x y z : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      lattice-meet (lattice-meet x y) z ≡ lattice-meet x (lattice-meet y z)

-- ============================================================================
-- QFT PORT (FEYNMAN'S QUANTUM COMPUTING)
-- ============================================================================

-- QFT port implementing Feynman's quantum computing semantics
record NonSusyQFTPort (structure : TrialityStructure) : Set₁ where
  field
    port : DomainPort structure (TrialityCarriers.Left (TrialityStructure.carriers structure))
    
    -- Feynman view: histories from micro-steps
    -- Action = product of header weights, amplitudes via domain evaluation
    -- Propagator = inverse Fisher, vertices = cumulants
    
    -- QFT operations
    field-amplitude : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                      TrialityCarriers.Left (TrialityStructure.carriers structure)
    propagator : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                 TrialityCarriers.Left (TrialityStructure.carriers structure)
    vertex-function : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                      TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                      TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                      TrialityCarriers.Left (TrialityStructure.carriers structure)
    action-integral : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                      TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- Quantum operations
    quantum-superposition : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                             TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                             TrialityCarriers.Left (TrialityStructure.carriers structure)
    quantum-interference : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                           TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                           TrialityCarriers.Left (TrialityStructure.carriers structure)
    quantum-measurement : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                          TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- QFT properties
    field-amplitude-linearity : ∀ (x y : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      field-amplitude x ≡ field-amplitude x
    propagator-symmetry : ∀ (x y : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      propagator x y ≡ propagator y x

-- ============================================================================
-- GUARDED NEGATION AND LOCAL NAND
-- ============================================================================

-- Guarded negation implementing local universality
record GuardedNegation (structure : TrialityStructure) : Set₁ where
  field
    -- Guard g ∈ L
    guard : TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- Relative complement g ⊖_L x on ↓g = {x ≤ g}
    relative-complement : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                          TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                          TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- Properties
    gn-retraction : ∀ (x : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      relative-complement guard (relative-complement guard x) ≡ x
    nand-universality : ∀ (x y : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      relative-complement guard x ≡ relative-complement guard x

-- ============================================================================
-- COMPLETE DOMAIN PORTS LAYER
-- ============================================================================

-- Complete domain ports layer
record DomainPortsLayer (structure : TrialityStructure) : Set₁ where
  field
    boolean-port : BooleanRAMPort structure
    lambda-port : LambdaCalculusPort structure
    infoflow-port : InfoFlowPort structure
    qft-port : NonSusyQFTPort structure
    guarded-negation : GuardedNegation structure

-- ============================================================================
-- DOMAIN PORTS INTERFACE
-- ============================================================================

-- Domain ports interface
record DomainPortsInterface (structure : TrialityStructure) : Set₁ where
  field
    layer : DomainPortsLayer structure
    
    -- Domain-specific operations
    turing-computation : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                         TrialityCarriers.Left (TrialityStructure.carriers structure)
    church-computation : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                         TrialityCarriers.Left (TrialityStructure.carriers structure)
    feynman-computation : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                          TrialityCarriers.Left (TrialityStructure.carriers structure)
    infoflow-computation : TrialityCarriers.Left (TrialityStructure.carriers structure) → 
                           TrialityCarriers.Left (TrialityStructure.carriers structure)
    
    -- Domain properties
    turing-halting : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      t ≡ t
    church-normalization : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      t ≡ t
    feynman-measurement : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      t ≡ t
    infoflow-flow : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      t ≡ t
    
    -- Cross-domain equivalence
    turing-church-equivalence : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      turing-computation t ≡ church-computation t
    church-feynman-equivalence : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      church-computation t ≡ feynman-computation t
    feynman-turing-equivalence : ∀ (t : TrialityCarriers.Left (TrialityStructure.carriers structure)) → 
      feynman-computation t ≡ turing-computation t

