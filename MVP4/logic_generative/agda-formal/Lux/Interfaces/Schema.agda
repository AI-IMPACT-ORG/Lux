-- Lux Logic System - Schema Interfaces
--
-- PURPOSE: Schema interfaces for explicit parameterization
-- STATUS: Active - Core interface definitions
-- DEPENDENCIES: Lux.Foundations.Types
--
-- Replace schema placeholders with concrete interfaces

module Lux.Interfaces.Schema where

open import Lux.Foundations.Types

record SchemaInterface : Set₁ where
  field
    -- Core mathematical structures
    carriers : Set
    left-semiring : Set
    right-semiring : Set
    bulk-semiring : Set
    core-semiring : Set
    
    -- Observer and embedding system
    observer-system : Set
    
    -- Central scalars
    central-scalars : Set
    
    -- Basepoint and braiding
    basepoint-gen4 : Set
    braiding-operations : Set
    
    -- Exp/Log structure
    exp-log-structure : Set

record TrialitySchemaInterface : Set₁ where
  field
    carriers : Set
    left-semiring : Set
    right-semiring : Set
    bulk-semiring : Set
    observer-system : Set
    
    -- Triality operations
    left-projector : Set
    right-projector : Set
    bulk-projector : Set
    boundary-sum : Set
    triality-functors : Set

record ModuliSchemaInterface : Set₁ where
  field
    carriers : Set
    left-semiring : Set
    right-semiring : Set
    bulk-semiring : Set
    
    -- Moduli operations
    left-moduli : Set
    right-moduli : Set
    extended-central-scalars : Set
    parametric-normal-forms : Set
    header-endomorphisms : Set

record GuardedNegationSchemaInterface : Set₁ where
  field
    carriers : Set
    left-semiring : Set
    
    -- Guarded negation operations
    left-subtraction : Set
    guarded-negation : Set
    nand-operation : Set
    computational-universality : Set

record DomainPortsSchemaInterface : Set₁ where
  field
    carriers : Set
    bulk-semiring : Set
    
    -- Domain port operations
    psdm : Set
    domain-port-evaluation : Set
    feynman-path-integral : Set
    partition-function : Set

record TruthTheoremsSchemaInterface : Set₁ where
  field
    carriers : Set
    
    -- Truth theorem schemas
    church-turing-equivalence : Set
    eor-health : Set
    logic-zeta-critical-line : Set
    umbral-renormalization : Set
    bulk-equals-two-boundaries : Set

