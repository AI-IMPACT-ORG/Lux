<!-- (c) 2025 AI.IMPACT GmbH -->

# Lux Mathematical Logic Library

## Overview

The Lux Mathematical Logic Library is a formal Coq implementation of the Lux mathematical logic system, designed as a universal formal modeling language for AI-powered software development. This library provides a mechanized foundation for reasoning about complex mathematical structures and their computational properties.

## Purpose and Context

This library is specifically designed for **AI-powered software development**, providing:

- **Formal Verification**: Mechanized proofs of mathematical properties
- **Code Generation**: Abstract specifications that can be instantiated in various programming languages
- **Reasoning Framework**: A foundation for AI systems to reason about mathematical structures
- **Specification Language**: A universal language for describing complex mathematical relationships

## Library Structure

```
Lux/
├── Util/                           # Utility modules and abstractions
│   ├── Semiring.v                 # Basic semiring definitions
│   ├── SemiringFunctor.v          # Semiring functors and Frobenius algebras
│   ├── BraidingGeneralization.v   # Abstract braiding properties
│   ├── GeneralizedBraidingAxioms.v # Generalized Yang-Baxter relations
│   └── AdvancedAlgebra.v          # Advanced algebraic structures
├── Core/                           # Core mathematical structures
│   ├── Signature.v                # Fundamental signature (interface)
│   ├── Axioms.v                   # Core axioms (A0-A9)
│   ├── Observers.v                # Observer/embedding operations
│   ├── NF.v                       # Normal form operations
│   ├── Triality.v                 # Triality functors and conjugations
│   ├── RegulatorScheme.v          # Regulator scheme for renormalization
│   ├── Counterterm.v              # Counterterm identity and Wilson recursion
│   ├── Cumulants.v                # Cumulant generating functionals
│   ├── Truth.v                    # Truth theorems and properties
│   └── Tests/                     # Unit tests and verification
│       └── UnitCore.v             # Core unit tests
├── Karoubi2BI/                    # Karoubi and Two-Boundary-Irreducible structures
│   ├── Karoubi.v                  # Karoubi objects and projections
│   └── TwoBI.v                    # Two-boundary-irreducible ideals
└── Class/                         # Class-level features and domain-specific implementations
    ├── Moduli.v                   # Moduli spaces and flows
    ├── Guarded.v                  # Guarded negation and local operations
    ├── PSDM.v                     # Partial Stable Domain Maps
    ├── Feynman.v                  # Feynman path integrals and renormalization
    ├── Domain/                    # Domain-specific implementations
    │   ├── Boolean.v              # Boolean domain port
    │   ├── Lambda.v               # λ-calculus domain port
    │   ├── InfoFlow.v             # Information flow domain port
    │   └── QFT.v                  # Quantum Field Theory domain port
    └── Tests/                     # Integration tests
        └── IntegTruths.v          # Integration truth theorems
```

## Key Mathematical Concepts

### Core Structures
- **Four Semirings**: L, R, Core (commutative), B (Frobenius algebra)
- **Observer/Embedding Maps**: `ι_L`, `ι_R`, `ι_Core`, `ν_L`, `ν_R`
- **Central Units**: `φ`, `z`, `z̄`, `Λ` (derived from z and z̄)
- **Braiding Operations**: `ad_i` with Yang-Baxter relations

### Advanced Features
- **Exponential/Logarithmic Structure**: `dec`/`rec` with integer headers
- **Normal Forms**: Header/core NF and B-valued NF
- **Triality**: Typed conjugations and triality functors
- **Renormalization**: Regulator schemes and counterterm identities
- **Domain Ports**: Boolean, λ-calculus, Info-flow, and QFT implementations

## Manual Use Instructions

### For AI Systems

This library is designed to be consumed by AI systems for:

1. **Specification Understanding**: AI can read the formal specifications to understand mathematical relationships
2. **Code Generation**: AI can generate implementations in various programming languages based on the Coq specifications
3. **Verification**: AI can use the mechanized proofs to verify correctness of generated code
4. **Reasoning**: AI can use the formal structure to reason about complex mathematical properties

### For Human Developers

#### Building the Library

```bash
cd coq-formal
make
```

#### Using the Library

The library is organized as a collection of Coq modules that can be imported and instantiated:

```coq
From Lux.Core Require Import Signature Axioms.
From Lux.Class Require Import Moduli Feynman.

Module MyImplementation <: LuxSignature.
  (* Implement the signature with your concrete types *)
End MyImplementation.

Module MyAxioms := Axioms(MyImplementation).
```

#### Key Modules to Understand

1. **`Lux.Core.Signature`**: Start here to understand the fundamental interface
2. **`Lux.Core.Axioms`**: Core mathematical properties and relationships
3. **`Lux.Class.Feynman`**: Advanced features for path integrals and renormalization
4. **`Lux.Class.Domain.*`**: Domain-specific implementations

## Comparison with Main Paper

### Mechanization Approach

The main paper presents the Lux mathematical logic system as a theoretical framework. This Coq library provides the **mechanized implementation** with the following key differences:

#### Main Paper Focus
- **Theoretical Foundations**: Mathematical definitions and properties
- **Informal Proofs**: High-level reasoning about mathematical structures
- **Specification**: What the system should do

#### Coq Library Focus
- **Formal Verification**: Mechanized proofs of all properties
- **Implementation**: How the system actually works
- **Code Generation**: Concrete implementations that can be executed

#### Key Mechanization Benefits

1. **Verification**: Every theorem is formally proven, not just stated
2. **Consistency**: The type system ensures mathematical consistency
3. **Extraction**: Code can be extracted to various programming languages
4. **AI Integration**: Formal specifications can be consumed by AI systems

### Usage Patterns

#### For AI Systems
- **Read Specifications**: Import modules to understand mathematical relationships
- **Generate Code**: Use the formal structure to generate implementations
- **Verify Correctness**: Use mechanized proofs to ensure generated code is correct

#### For Human Developers
- **Understand Structure**: Use the formal definitions to understand the mathematical system
- **Implement Domains**: Create new domain-specific implementations
- **Extend Functionality**: Add new features while maintaining formal correctness

## Development Guidelines

### Adding New Features

1. **Start with Signature**: Define new operations in `Lux.Core.Signature`
2. **Add Axioms**: Formalize properties in `Lux.Core.Axioms`
3. **Implement Core**: Add core functionality in `Lux.Core.*`
4. **Add Class Features**: Implement advanced features in `Lux.Class.*`
5. **Test Thoroughly**: Add tests in `Lux.Core.Tests.*` and `Lux.Class.Tests.*`

### Code Style

- Use proper Coq docstrings (`(** ... *)`) for all modules and functions
- Follow the existing naming conventions
- Ensure all proofs are complete (avoid `admit` in production code)
- Maintain compatibility with the signature interface

## Future Directions

- **Language Extraction**: Generate implementations in Haskell, OCaml, and other languages
- **AI Integration**: Develop tools for AI systems to consume and generate from this library
- **Domain Expansion**: Add more domain-specific implementations
- **Performance Optimization**: Optimize the formalization for better performance

## Contributing

This library is designed for AI-powered software development. Contributions should:

1. Maintain formal correctness
2. Follow the established module structure
3. Include comprehensive documentation
4. Add appropriate tests
5. Consider AI consumption patterns

## License

This library is part of the Lux Mathematical Logic project. See the main project for licensing information.