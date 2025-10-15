<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Lux Formal Logic Library

A rigorous Isabelle/HOL mechanization of the Lux formal logic framework for AI-powered software development, featuring mathematically elegant foundational logic with comprehensive dependent type system and eliminated shortcuts.

## Overview

This library provides a complete formal specification of the Lux logic system, implementing the mathematical foundations described in the main paper. The mechanization captures the three-layer architecture (Axioms → Core → Class) with explicit dependent type threading, guarded negation, PSDM (Partial Stable Domain Map) semantics, and comprehensive domain-specific reasoning capabilities.

## Library Structure

```
Lux/
├── Axioms/                    # Mathematical foundations
│   ├── Atomic.thy            # Base axioms A0-A7, semirings L/B/R, observers/embeddings
│   ├── DependentTypes.thy    # Type-safe mathematical structure with eliminated shortcuts
│   └── README.md             # Axioms layer documentation
├── Core/                     # Definitional layer over Axioms  
│   ├── Shell.thy            # Triality, reconstitution, generating functional Z[J]
│   ├── Constructive_Logic.thy # Residual analysis, Karoubi split, 2BI ideal
│   └── README.md             # Core layer documentation
├── Class/                    # Application layer over Core
│   ├── Class.thy            # Guarded negation, PSDM, Feynman view
│   └── README.md             # Class layer documentation
├── Consistency/              # Mathematical consistency decisions
│   ├── Design_Decisions.thy # Mathematical justification for design choices
│   └── README.md             # Consistency documentation
├── Ports/                    # Domain-specific reasoning
│   ├── Domain_Ports.thy     # Boolean/RAM, Lambda, InfoFlow, QFT, Blockchain ports
│   └── README.md             # Ports documentation
├── Tests/                    # Comprehensive verification
│   ├── Comprehensive_Tests.thy # Systematic test suite
│   ├── DependentTypes_Tests.thy # Type-safe test suite
│   └── README.md             # Testing documentation
├── Theorems/                 # Formal proof extraction
│   ├── Extracted_Theorems.thy # Extracted theorems and proofs
│   └── README.md             # Theorems documentation
├── Category_Theory.thy       # Categorical foundations and explanations
├── Ring_Completion.thy      # Grothendieck completion and coefficient hull
├── R_Data_System.thy        # Scale header splitting and matrix operations
├── API.thy                   # Main entry point - stable API façade
├── README.md                 # Main library documentation
└── ROOT                     # Isabelle session definitions
```

## Dependency Tree

The following diagram shows the dependency relationships between theory files:

```
Main (Isabelle Standard Library)
│
├── Lux/Axioms/Atomic.thy
│   └── imports Main
│
├── Lux/Axioms/DependentTypes.thy
│   └── imports Main
│
├── Lux/Consistency/Design_Decisions.thy
│   └── imports Main
│
├── Lux/Core/Shell.thy
│   ├── imports Lux/Axioms/Atomic
│   └── imports Lux/Axioms/DependentTypes
│
├── Lux/Core/Constructive_Logic.thy
│   └── imports Lux/Core/Shell
│
├── Lux/Class/Class.thy
│   ├── imports Lux/Core/Shell
│   └── imports Lux/Axioms/DependentTypes
│
├── Lux/Ports/Domain_Ports.thy
│   └── imports Lux/Class/Class
│
├── Lux/Category_Theory.thy
│   └── imports Lux/Axioms/Atomic
│
├── Lux/Ring_Completion.thy
│   └── imports Lux/Axioms/Atomic
│
├── Lux/R_Data_System.thy
│   └── imports Lux/Core/Shell
│
├── Lux/Tests/DependentTypes_Tests.thy
│   └── imports Lux/Axioms/DependentTypes
│
├── Lux/Tests/Comprehensive_Tests.thy
│   └── imports (no dependencies)
│
├── Lux/Theorems/Extracted_Theorems.thy
│   └── imports (no dependencies)
│
└── Lux/API.thy
    └── imports (no dependencies)
```

### Dependency Layers

1. **Foundation Layer** (no internal dependencies):
   - `Atomic.thy` - Base axioms
   - `DependentTypes.thy` - Type-safe structure
   - `Design_Decisions.thy` - Consistency decisions

2. **Core Layer** (depends on Foundation):
   - `Shell.thy` - Triality and reconstitution
   - `Constructive_Logic.thy` - Residual analysis

3. **Class Layer** (depends on Core + Foundation):
   - `Class.thy` - Guarded negation and PSDM

4. **Application Layer** (depends on Class):
   - `Domain_Ports.thy` - Domain-specific reasoning

5. **Extension Layer** (depends on Foundation/Core):
   - `Category_Theory.thy` - Categorical foundations
   - `Ring_Completion.thy` - Ring completion
   - `R_Data_System.thy` - Scale header operations

6. **Testing Layer** (depends on Foundation):
   - `DependentTypes_Tests.thy` - Type-safe tests
   - `Comprehensive_Tests.thy` - Systematic tests

7. **API Layer** (standalone):
   - `API.thy` - Main entry point
   - `Extracted_Theorems.thy` - Proof extraction

## File Organization

### Active Files
All files listed above are actively maintained and part of the current implementation.

### Backup Files
Old and unnecessary files have been moved to `backup/old_files/`:
- `Atomic_clean.thy` - Old atomic axioms implementation
- `Atomic_minimal.thy` - Minimal atomic axioms implementation  
- `Atomic.thy.backup` - Backup of atomic axioms
- `Atomic.thy.bak` - Backup of atomic axioms
- `Shell.thy.bak` - Backup of shell implementation
- `DependentTypes_Tests.thy.bak*` - Multiple backups of test files

These files are preserved for reference but are not part of the active codebase.

## Key Components

### Axioms Layer (`Lux_Axioms`)
- **Three semirings**: L (left boundary), B (bulk), R (right boundary)
- **Observers/embeddings**: `ν_L : B → L`, `ι_L : L → B` with retraction properties
- **Central scalars**: φ, z, z̄ with Λ := z ⊗_B z̄
- **Exp/log structure**: Decomposition `dec : B → (H × H × H) × Core`
- **Braiding operators**: `ad₀, ad₁, ad₂, ad₃` satisfying Yang-Baxter relations
- **Generic headers**: Parameterized type `'H` for maximum generality

### Dependent Type System (`DependentTypes`)
- **Header Type**: Type-safe header components (k_phi, m_z, m_zbar)
- **BulkElement Type**: Dependent type combining headers with core data
- **BraidingOp Type**: Indexed type for all 4 braiding operators
- **ObserverProj Type**: Type-safe observer projections (NuL, NuR)
- **EmbeddingInj Type**: Type-safe embedding injections (IotaL, IotaR)
- **CentralUnit Type**: Indexed type for central units (Phi, Z, Zbar)
- **ResidualType**: Classification of residuals (Algebraic, Internal, Observable)
- **GaugeType**: Type for gauge transformations (HeaderOnly, Full, NoTransform)
- **MathProperty**: Type for mathematical properties

### Core Layer (`Lux_Core`)
- **Triality conjugations**: `starB`, `starL`, `starR` with observer coherence
- **Reconstitution**: `ρ(t) = [L](t) ⊕_B [R](t)` (bulk as two boundaries)
- **Generating functional**: `Z[J]` for cumulant machinery
- **Residual analysis**: Mathematical foundation for computational residuals
- **Karoubi split**: Categorical decomposition of observable bulk
- **2BI ideal**: Two-boundary-irreducible ideal for genuinely bulk interactions

### Class Layer (`Lux_Class`)
- **Guarded negation**: RC-GN relative complement on principal ideals ↓guard
- **PSDM semantics**: Partial stable domain maps for irreversibility
- **Dependent type threading**: Local/global type environment alignment
- **Feynman view**: Sum-over-histories façade for QFT concepts
- **Domain ports**: Interface to external computational domains

### Extensions (`Lux_Extensions`)
- **Category Theory**: Categorical foundations and explanations
- **Ring Completion**: Grothendieck completion and coefficient hull
- **R-Data System**: Scale header splitting and matrix operations
- **Domain Ports**: Boolean/RAM, Lambda, InfoFlow, QFT, Blockchain interfaces

## Mathematical Elegance

The library achieves mathematical elegance through:

1. **Type Class Hierarchy**: Unified semiring framework with elegant axioms
2. **Categorical Foundations**: Observer/embedding relationships as adjoint functors
3. **Constructive Logic**: Residual analysis and Karoubi split for computational semantics
4. **Domain Integration**: Clean interfaces to external computational domains
5. **Mathematical Rigor**: Every choice mathematically justified
6. **Dependent Type System**: Type-safe operations with eliminated shortcuts
7. **Sophisticated Operations**: Proper mathematical meaning for all operations

## AI-Powered Software Development

This mechanization is designed for AI systems that need to:

1. **Reason about computational semantics** using the Lux framework
2. **Generate verified code** that respects the three-layer architecture
3. **Perform formal verification** of properties across Axioms/Core/Class
4. **Implement domain-specific languages** with guaranteed properties
5. **Integrate with external domains** through clean port interfaces

The library provides:
- **Stable API** for consistent AI tooling integration
- **Explicit hypothesis management** for conditional theorems
- **Level distinctions** (observer vs bulk vs meta-level)
- **Status labels** (proven vs conditional vs conjectural)
- **Domain ports** for external system integration
- **Type-safe operations** with compile-time guarantees

## Instructions for Manual Use

### Building the Library

```bash
cd isabelle-formal
isabelle build -s Lux_Base    # Build base axioms
isabelle build -s Lux_Core    # Build core layer  
isabelle build -s Lux_Class   # Build class layer
isabelle build -s Lux_API     # Build complete API
```

### Using Individual Components

```isabelle
theory MyTheory
  imports "Lux/Axioms/Atomic"  # Just the base axioms
begin

locale MyExtension = Lux_Axioms +
  fixes my_operation :: "'B => 'B"
  assumes my_property: "my_operation zeroB = zeroB"
begin
  (* Your extensions here *)
end

end
```

### Extending with Core Features

```isabelle
theory MyCoreExtension  
  imports "Lux/Core/Shell"
begin

locale MyCoreExtension = Lux_Core +
  fixes my_moduli :: "'H => 'H"
  assumes my_flow: "my_moduli (addH h1 h2) = addH (my_moduli h1) (my_moduli h2)"
begin
  (* Access to triality, reconstitution, Z[J], etc. *)
end

end
```

### Using Domain Ports

```isabelle
theory MyDomainApplication
  imports "Lux/Ports/Domain_Ports"
begin

context Lux_Domain_Ports begin
  (* Access to domain-specific reasoning capabilities *)
  
  definition my_boolean_operation :: "B => boolean_carrier option" where
    "my_boolean_operation t = boolean_port t"
    
  definition my_lambda_operation :: "B => lambda_carrier option" where
    "my_lambda_operation t = lambda_port t"
end

end
```

### Using the Complete API

```isabelle
theory MyApplication
  imports "Lux/API"
begin

context Lux_Class begin
  (* Access to all features: guarded negation, PSDM, dependent types *)
  
  definition my_psdm :: "'B => 'B option" where
    "my_psdm t = (if psdm_defined t then Some t else None)"
    
  lemma my_property: "psdm_defined t ==> my_psdm t = Some t"
    by (simp add: my_psdm_def)
end

end
```

## Mechanization vs. Main Paper

### Correspondence

| Paper Section | Isabelle Theory | Key Concepts |
|---------------|-----------------|--------------|
| S02 (Formal Systems) | `Axioms/Atomic.thy` | A0-A7 axioms, semirings, observers |
| S03 (Core Logic) | `Core/Shell.thy` | Triality, reconstitution, Z[J] |
| S04 (Class Layer) | `Class/Class.thy` | Guarded negation, PSDM |
| S05 (Consistency) | `Consistency/Design_Decisions.thy` | Mathematical conventions |
| Extensions | `Core/Constructive_Logic.thy` | Residual analysis, Karoubi split |
| Extensions | `Ports/Domain_Ports.thy` | Domain-specific reasoning |
| Extensions | `Ring_Completion.thy` | Ring completion structures |
| Extensions | `R_Data_System.thy` | Scale header splitting |

### Key Differences

1. **Generic Headers**: The mechanization uses parameterized `'H` instead of fixed `int` for maximum generality
2. **Explicit Hypotheses**: All conditional theorems explicitly state their dependencies
3. **Status Labels**: Clear distinction between proven theorems, conditional theorems, and conjectures
4. **Dependent Types**: Explicit threading of local/global type environments
5. **API Façade**: Stable entry point for AI tooling integration
6. **Domain Ports**: Clean interfaces to external computational domains
7. **Mathematical Extensions**: Pareto-minimal extensions for foundational logic
8. **Shortcut Elimination**: Sophisticated operations replace simplified placeholders
9. **Type Safety**: Compile-time guarantees for all operations

### Mechanization Benefits

- **Verification**: All definitions and theorems are mechanically checked
- **Generality**: Parameterized types allow instantiation for specific domains
- **Modularity**: Clean separation between Axioms/Core/Class layers
- **Extensibility**: Easy to add new features while preserving properties
- **AI Integration**: Stable API designed for automated reasoning systems
- **Domain Integration**: Clean interfaces to external computational domains
- **Mathematical Elegance**: Pareto-minimal extensions with maximal expressiveness
- **Type Safety**: Compile-time guarantees for mathematical operations

## Development Guidelines

### Adding New Features

1. **Identify the layer**: Axioms (foundational), Core (definitional), Class (application), or Extensions
2. **Extend appropriate locale**: `Lux_Axioms`, `Lux_Core`, `Lux_Class`, or create new extension locale
3. **State explicit hypotheses**: Use conditional theorem locales when needed
4. **Add status labels**: Mark as PROVEN THEOREM, CONDITIONAL THEOREM, or CONJECTURE
5. **Update API**: Expose new features through `Lux/API.thy`
6. **Add tests**: Include comprehensive tests in `Tests/DependentTypes_Tests.thy`

### Proof Strategies

- **Use `by simp`** for basic algebraic manipulations
- **Use `by assumption`** for hypothesis-dependent results  
- **Use `sorry`** only for conjectures with clear status labels
- **Prefer abstract reasoning** over concrete instantiations
- **Use categorical foundations** where appropriate

### Testing

```bash
# Run unit tests
isabelle build -s Lux_Tests

# Check specific theories
isabelle process -T Lux/Core/Shell
isabelle process -T Lux/Class/Class
isabelle process -T Lux/Ports/Domain_Ports
```

## Contributing

When extending the library:

1. **Follow the three-layer architecture**: Axioms → Core → Class
2. **Maintain generic headers**: Use `'H` parameterization
3. **Add explicit hypotheses**: Use conditional theorem locales
4. **Update documentation**: Keep this README current
5. **Test thoroughly**: Ensure all theories compile
6. **Maintain mathematical elegance**: Use pareto-minimal extensions
7. **Include copyright notices**: All files must have proper copyright headers
8. **Eliminate shortcuts**: Replace simplified operations with proper mathematical meaning

## References

- Main paper: `../latex/sections/` (S02-S14)
- Specifications: `../CHATGPT/Lux_*.md`
- Implementation plan: `../CHATGPT/MATHEMATICAL_CONSISTENCY_DESIGN_DECISIONS.md`
- Optimization summary: `OPTIMIZATION_SUMMARY.md`
- Pareto-minimal extensions: `PARETO_MINIMAL_EXTENSIONS.md`
- Shortcuts eliminated: `SHORTCUTS_ELIMINATED_SUMMARY.md`

---

*This mechanization provides a rigorous foundation for AI-powered software development using the Lux formal logic framework, featuring mathematically elegant foundational logic with comprehensive domain-specific reasoning capabilities and a sophisticated dependent type system.*