# CLEAN v10 Layered Test Architecture

## Overview

This document describes the layered (onion-style) test architecture for CLEAN v10, designed to provide clean separation of concerns and better test organization.

## Architecture Layers

### Layer 1: Core (Innermost) 🧮
**Location**: `tests/layers/core/`
**Purpose**: Tests fundamental CLEAN v10 mathematical properties
**Dependencies**: Core modules only (`core/`)
**Tests**:
- Core mathematical invariants
- Kernel composition laws
- RC-ME (Residual Invisibility)
- Bulk = Two Boundaries
- RG blocking properties
- Property-based testing
- Invariant testing

**Key Principle**: These tests should never change - they define the core invariants.

### Layer 2: Domain API 🔌
**Location**: `tests/layers/domain-api/`
**Purpose**: Tests the DomainPortAPI interface - clean boundary between core and domains
**Dependencies**: DomainPortAPI only
**Tests**:
- Domain term operations
- Domain kernel operations
- Domain header operations
- Domain normal form operations
- Domain observer operations
- Domain cumulant operations
- Domain Feynman operations
- Domain PSDM operations
- Domain RG operations
- Domain property-based testing
- Domain invariant testing

**Key Principle**: Ensures the API provides stable, consistent access to core functionality.

### Layer 3: Domain Ports 🌐
**Location**: `tests/layers/domain-ports/`
**Purpose**: Tests specific domain implementations using DomainPortAPI
**Dependencies**: DomainPortAPI + unified-port
**Tests**:
- Turing Port (q=(1,0,0) - Deterministic Models)
- Lambda Port (q=(0,1,0) - Probabilistic Models)
- Path Port (q=(0,0,1) - Stochastic Models)
- Infoflow Port (Information Measures)
- Boolean Port (Turing Port Alias)
- QFT Port (Path Port Alias)
- Domain port consistency
- Domain port q-vector alignment
- Domain port kernel integration
- Domain port totality predicates

**Key Principle**: Verifies domain-specific functionality while using the clean API.

### Layer 4: Integration (Outermost) 🔗
**Location**: `tests/layers/integration/`
**Purpose**: Tests complete system integration across all layers
**Dependencies**: All layers
**Tests**:
- End-to-end domain integration
- Cross-layer kernel integration
- Feynman integration across layers
- PSDM integration across layers
- Institution integration
- Multi-domain workflow
- Cross-domain consistency
- Property-based integration testing
- Error handling across layers
- Performance integration

**Key Principle**: Verifies end-to-end functionality and cross-layer interactions.

## DomainPortAPI Interface

The `DomainPortAPI.rkt` provides a clean interface between core logic and domain applications:

```racket
;; Core Domain Interface (Layer 1 - Innermost)
(provide ; Term operations
         make-domain-term
         domain-term?
         domain-term-name
         domain-term-header
         domain-term-core
         
         ; Kernel operations
         make-domain-kernel
         domain-kernel?
         domain-kernel-header
         domain-kernel-compose
         domain-kernel-apply
         
         ; Header operations
         make-domain-header
         domain-header?
         domain-header-phase
         domain-header-scale
         domain-header-add
         domain-header-multiply
         domain-header-equal?
         
         ; ... and more
         )
```

## Test Organization Benefits

### 1. **Clear Separation of Concerns**
- Each layer has a specific responsibility
- Tests are organized by architectural layer
- Dependencies flow inward (onion style)

### 2. **Stable Interfaces**
- DomainPortAPI provides a stable boundary
- Core tests never change (mathematical invariants)
- Domain tests can evolve without affecting core

### 3. **Better Debugging**
- Failures can be isolated to specific layers
- Clear dependency chain for troubleshooting
- Easier to identify where issues originate

### 4. **Maintainability**
- Changes to core don't affect domain tests
- Changes to domains don't affect core tests
- API changes are clearly visible

### 5. **Testability**
- Each layer can be tested independently
- Integration tests verify cross-layer functionality
- Property-based testing at appropriate layers

## Running Tests

### All Layers
```bash
racket -e "(require \"tests/layers/layered-test-runner.rkt\") (run-all-layered-tests)"
```

### Individual Layers
```bash
# Core layer only
racket -e "(require \"tests/layers/core/core-layer-tests.rkt\") (run-core-layer-tests)"

# Domain API layer only
racket -e "(require \"tests/layers/domain-api/domain-api-layer-tests.rkt\") (run-domain-api-layer-tests)"

# Domain ports layer only
racket -e "(require \"tests/layers/domain-ports/domain-ports-layer-tests.rkt\") (run-domain-ports-layer-tests)"

# Integration layer only
racket -e "(require \"tests/layers/integration/integration-layer-tests.rkt\") (run-integration-layer-tests)"
```

## Migration from Old Test Structure

The old test files have been reorganized into this layered structure:

- **Core tests**: `core/tests/` → `tests/layers/core/`
- **Comprehensive tests**: `comprehensive-tests*.rkt` → Split across layers
- **Domain tests**: `class/domain/unified-port-tests.rkt` → `tests/layers/domain-ports/`
- **API tests**: `api-extension-tests.rkt` → `tests/layers/domain-api/`
- **Integration tests**: Various → `tests/layers/integration/`

## Future Extensions

This layered architecture supports:

1. **New Domain Ports**: Add to Layer 3 without affecting core
2. **API Extensions**: Add to Layer 2 with proper testing
3. **Core Enhancements**: Add to Layer 1 with invariant preservation
4. **Integration Scenarios**: Add to Layer 4 for end-to-end testing

The architecture ensures that changes at any layer don't break tests at other layers, providing a robust foundation for CLEAN v10 development.
