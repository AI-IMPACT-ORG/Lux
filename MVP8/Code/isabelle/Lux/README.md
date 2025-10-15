<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Lux Formal Logic Library - Core Implementation

This directory contains the complete Isabelle/HOL implementation of the Lux formal logic framework, featuring mathematically elegant foundational logic with pareto-minimal extensions.

## Directory Structure

- **Axioms/**: Mathematical foundations (A0-A7 axioms, semirings, observers)
- **Core/**: Definitional layer (triality, reconstitution, constructive logic)
- **Class/**: Application layer (guarded negation, PSDM, Feynman view)
- **Consistency/**: Mathematical consistency decisions and design choices
- **Ports/**: Domain-specific reasoning interfaces
- **Tests/**: Comprehensive verification and testing
- **Theorems/**: Formal proof extraction and theorem management
- **API.thy**: Main entry point and stable API façade

## Key Features

### Mathematical Elegance
- **Type Class Hierarchy**: Unified semiring framework with elegant axioms
- **Categorical Foundations**: Observer/embedding relationships as adjoint functors
- **Constructive Logic**: Residual analysis and Karoubi split for computational semantics
- **Domain Integration**: Clean interfaces to external computational domains

### Three-Layer Architecture
1. **Axioms Layer**: Mathematical foundations with semirings, observers, and braiding
2. **Core Layer**: Definitional layer with triality, reconstitution, and constructive logic
3. **Class Layer**: Application layer with guarded negation, PSDM, and domain ports

### Extensions
- **Category Theory**: Categorical foundations and explanations
- **Ring Completion**: Grothendieck completion and coefficient hull
- **R-Data System**: Scale header splitting and matrix operations
- **Domain Ports**: Boolean/RAM, Lambda, InfoFlow, QFT, Blockchain interfaces

## Usage

### Building the Library
```bash
isabelle build -s Lux_Base    # Build base axioms
isabelle build -s Lux_Core    # Build core layer  
isabelle build -s Lux_Class   # Build class layer
isabelle build -s Lux_API     # Build complete API
```

### Importing Components
```isabelle
theory MyTheory
  imports "Lux/Axioms/Atomic"  # Base axioms
  imports "Lux/Core/Shell"    # Core functionality
  imports "Lux/Class/Class"   # Application features
  imports "Lux/API"           # Complete API
begin
  (* Your theory here *)
end
```

## Mathematical Foundations

The Lux system is built on rigorous mathematical foundations:

- **Semiring Theory**: Three semirings (L, B, R) with observer/embedding relationships
- **Category Theory**: Categorical understanding of mathematical structures
- **Constructive Logic**: Residual analysis and Karoubi split
- **Domain Theory**: PSDM semantics for partial functions
- **Quantum Field Theory**: Feynman view and path integrals

## AI Integration

This library is designed for AI-powered software development:

- **Stable API**: Consistent interface for AI tooling
- **Explicit Hypotheses**: Clear dependency management
- **Domain Ports**: Integration with external computational domains
- **Mathematical Rigor**: Every choice mathematically justified

## Contributing

When extending the library:

1. Follow the three-layer architecture
2. Maintain mathematical elegance
3. Use pareto-minimal extensions
4. Include proper copyright notices
5. Update documentation
6. Add comprehensive tests

## License

Copyright (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
