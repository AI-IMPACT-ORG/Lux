<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Lux Library - CLEAN Logic System Implementation

## Overview

Lux is a comprehensive Agda implementation of the CLEAN logic system, providing formal verification of mathematical structures including semirings, observers, central scalars, braiding operations, and truth theorems.

## Architecture

The library follows an onion-style hexagonal architecture with clear separation of concerns:

- **Core**: Fundamental mathematical structures and operations
- **Interfaces**: Abstract interfaces and schemas
- **Models**: Concrete implementations and witnesses
- **Tests**: Comprehensive test suites and validation
- **Examples**: Usage demonstrations

## Key Features

- **V2 Axioms**: Complete implementation of A0-A7 axioms
- **V10 Core**: Triality operations, moduli system, advanced operations
- **V10 CLASS**: Guarded negation, domain ports, computational universality
- **Truth Theorems**: Church-Turing equivalence, EOR health, Logic-ζ critical line
- **Mathematical Coherence**: Integrated structure with explicit relationships
- **Test Framework**: Enhanced testing with Racket alignment

## Quick Start

```agda
open import Lux

-- Use the V2 Laurent model
example : Bulk
example = let core = v2-laurent-model
             open CoreKernelStructure core
         in oneB
```

## Modules

### Core Modules
- `CLEAN.Core.Kernel`: Fundamental semiring structures
- `CLEAN.Core.TrialityOperations`: Projectors, boundary sum, functors
- `CLEAN.Core.ModuliSystem`: Parametric normal forms, header operations
- `CLEAN.Core.AdvancedOperations`: Cumulants, Δ-operators, Green functions
- `CLEAN.Core.GuardedNegation`: Local negation, NAND operations
- `CLEAN.Core.DomainPorts`: PSDM, path integrals, partition functions
- `CLEAN.Core.TruthTheorems`: Mathematical consistency, diagonal properties
- `CLEAN.Core.MathematicalInsights`: Fundamental theorems
- `CLEAN.Core.IntegratedStructure`: Cross-module relationships

### Interface Modules
- `CLEAN.Interfaces.Schema`: Abstract schema interfaces
- `CLEAN.Interfaces.BraidingBoundary`: Induced automorphisms

### Model Modules
- `CLEAN.Models.V2LaurentModel`: Concrete Laurent-headers model

### Test Modules
- `CLEAN.Tests.Entrypoint`: Public test interface
- `CLEAN.Tests.Utils.*`: Test framework and runners
- `CLEAN.Tests.Foundation.*`: V2 axiom tests
- `CLEAN.Tests.V10Core.*`: V10 Core tests
- `CLEAN.Tests.V10Class.*`: V10 CLASS tests
- `CLEAN.Tests.TruthTheorems.*`: Truth theorem tests

## Status

- **Total Modules**: 101 Agda files
- **Test Coverage**: 99+ test cases across 13 suites
- **Compilation**: Core modules compile successfully
- **Mathematical Coherence**: Integrated structure with explicit relationships

## Dependencies

- Agda 2.7.0.1+
- Cubical type theory support
- Standard library (minimal usage)

## License

Open source - see individual module headers for details.

## Contributing

The library is designed for mathematical rigor and formal verification. Contributions should maintain the architectural principles and mathematical coherence established in the core modules.