-- Lux Logic System - Main Architecture Orchestrator
--
-- PURPOSE: Main orchestrator for the complete onion-style hexagonal architecture
-- STATUS: Active - Main architecture orchestrator
-- DEPENDENCIES: All Lux modules
--
-- This module orchestrates the complete architecture:
-- - Combines all layers into a cohesive system
-- - Provides hexagonal interfaces (ports/adapters)
-- - Maintains onion-style dependency flow (inward only)

{-# OPTIONS --cubical --without-K #-}

module Lux.Architecture.Main where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Lux.Core.Kernel
open import Lux.Core.TrialityLayer
open import Lux.Core.ModuliLayer
open import Lux.Ports.DomainPorts
open import Lux.Integration.Layer

-- ============================================================================
-- COMPLETE ONION-STYLE HEXAGONAL ARCHITECTURE
-- ============================================================================

-- Main architecture record
record CompleteOnionHexagonArchitecture : Set₁ where
  field
    -- Layer 1: Core Kernel (V2 Mathematical Foundations)
    core-kernel : CoreKernelStructure
    
    -- Layer 2: Triality Layer (Core Constructive Logic)
    triality-layer : TrialityLayerStructure core-kernel
    
    -- Layer 3: Moduli Layer (Parametric Normal Forms and Flows)
    moduli-layer : ModuliLayerStructure core-kernel
    
    -- Layer 4: Domain Ports (External Computational Paradigms)
    domain-ports : DomainPortsStructure core-kernel
    
    -- Layer 5: Integration Layer (Truth Theorems and Coherence)
    integration-layer : IntegrationLayerStructure core-kernel

-- ============================================================================
-- ARCHITECTURAL INTERFACES (Hexagonal Ports/Adapters)
-- ============================================================================

-- Core Kernel Interface (innermost layer)
record CoreKernelInterface (architecture : CompleteOnionHexagonArchitecture) : Set₁ where
  open CompleteOnionHexagonArchitecture architecture
  open CoreKernelStructure core-kernel
  field
    -- Access to core mathematical foundations
    carriers : TrialityCarriers
    left-semiring : LeftSemiring carriers
    right-semiring : RightSemiring carriers
    bulk-semiring : BulkSemiring carriers
    core-semiring : CoreSemiring carriers
    observers : ObserverSystem carriers left-semiring right-semiring bulk-semiring
    central-scalars : CentralScalars carriers bulk-semiring
    basepoint-gen4 : BasepointGen4 carriers bulk-semiring
    braiding : BraidingOperations carriers bulk-semiring
    exp-log : ExpLogStructure carriers bulk-semiring core-semiring

-- Triality Layer Interface
record TrialityLayerInterface (architecture : CompleteOnionHexagonArchitecture) : Set₁ where
  open CompleteOnionHexagonArchitecture architecture
  open TrialityLayerStructure triality-layer
  open CoreKernelStructure (CompleteOnionHexagonArchitecture.core-kernel architecture)
  field
    -- Access to triality operations and functors
    triality-ops : TrialityOperations carriers left-semiring right-semiring bulk-semiring
    triality-functors : TrialityFunctors carriers left-semiring right-semiring bulk-semiring

-- Moduli Layer Interface
record ModuliLayerInterface (architecture : CompleteOnionHexagonArchitecture) : Set₁ where
  open CompleteOnionHexagonArchitecture architecture
  open ModuliLayerStructure moduli-layer
  open CoreKernelStructure (CompleteOnionHexagonArchitecture.core-kernel architecture)
  field
    -- Access to parametric normal forms and flows
    four-moduli-nf : FourModuliNF carriers bulk-semiring
    auxiliary-transporter : AuxiliaryTransporter carriers bulk-semiring

-- Domain Ports Interface
record DomainPortsInterface (architecture : CompleteOnionHexagonArchitecture) : Set₁ where
  open CompleteOnionHexagonArchitecture architecture
  open DomainPortsStructure domain-ports
  open CoreKernelStructure (CompleteOnionHexagonArchitecture.core-kernel architecture)
  field
    -- Access to external computational paradigms
    boolean-ram-port : BooleanRAMPort carriers bulk-semiring
    lambda-calculus-port : LambdaCalculusPort carriers bulk-semiring
    info-flow-port : InfoFlowPort carriers left-semiring
    qft-port : QFTPort carriers left-semiring

-- Integration Layer Interface (outermost layer)
record IntegrationLayerInterface (architecture : CompleteOnionHexagonArchitecture) : Set₁ where
  open CompleteOnionHexagonArchitecture architecture
  open IntegrationLayerStructure integration-layer
  open CoreKernelStructure (CompleteOnionHexagonArchitecture.core-kernel architecture)
  field
    -- Access to truth theorems and coherence
    feynman-sum-over-histories : FeynmanSumOverHistories carriers bulk-semiring
    truth-theorems : TruthTheorems carriers bulk-semiring

