<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Lux Formal Logic Library

A rigorous Isabelle/HOL mechanization of the Lux formal logic framework for AI-powered software development.

## Overview

This library provides a complete formal specification of the Lux logic system, implementing the mathematical foundations described in the main paper. The mechanization captures the three-layer architecture (Axioms → Core → Class) with explicit dependent type threading, guarded negation, and PSDM (Partial Stable Domain Map) semantics.

## Library Structure

```
Lux/
├── Axioms/                    # Mathematical foundations
│   └── Atomic.thy            # Base axioms A0-A7, semirings L/B/R, observers/embeddings
├── Core/                     # Definitional layer over Axioms  
│   ├── Shell.thy            # Triality, reconstitution, generating functional Z[J]
│   └── Constructive_Logic.thy # Residual properties, Karoubi split
├── Class/                    # Application layer over Core
│   └── Class.thy            # Guarded negation, PSDM, Feynman view
├── Consistency/              # Mathematical consistency decisions
│   └── Design_Decisions.thy # Ring completion, header filtering, addition conventions
├── API.thy                   # Main entry point - stable API façade
└── ROOT                     # Isabelle session definitions
```

## Key Components

### Axioms Layer (`Lux_Axioms`)
- **Three semirings**: L (left boundary), B (bulk), R (right boundary)
- **Observers/embeddings**: `ν_L : B → L`, `ι_L : L → B` with retraction properties
- **Central scalars**: φ, z, z̄ with Λ := z ⊗_B z̄
- **Exp/log structure**: Decomposition `dec : B → (H × H × H) × Core`
- **Braiding operators**: `ad₀, ad₁, ad₂, ad₃` satisfying Yang-Baxter relations
- **Generic headers**: Parameterized type `'H` for maximum generality

### Core Layer (`Lux_Core`)
- **Triality conjugations**: `starB`, `starL`, `starR` with observer coherence
- **Reconstitution**: `ρ(t) = [L](t) ⊕_B [R](t)` (bulk as two boundaries)
- **Generating functional**: `Z[J]` for cumulant machinery
- **Regulator window**: Generic `('H => bool)` predicates for truncation
- **Counterterm identity**: Scheme independence via R-data

### Class Layer (`Lux_Class`)
- **Guarded negation**: RC-GN relative complement on principal ideals ↓guard
- **PSDM semantics**: Partial stable domain maps for irreversibility
- **Dependent type threading**: Local/global type environment alignment
- **Feynman view**: Sum-over-histories façade for QFT concepts

## AI-Powered Software Development

This mechanization is designed for AI systems that need to:

1. **Reason about computational semantics** using the Lux framework
2. **Generate verified code** that respects the three-layer architecture
3. **Perform formal verification** of properties across Axioms/Core/Class
4. **Implement domain-specific languages** with guaranteed properties

The library provides:
- **Stable API** for consistent AI tooling integration
- **Explicit hypothesis management** for conditional theorems
- **Level distinctions** (observer vs bulk vs meta-level)
- **Status labels** (proven vs conditional vs conjectural)

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

### Key Differences

1. **Generic Headers**: The mechanization uses parameterized `'H` instead of fixed `int` for maximum generality
2. **Explicit Hypotheses**: All conditional theorems explicitly state their dependencies
3. **Status Labels**: Clear distinction between proven theorems, conditional theorems, and conjectures
4. **Dependent Types**: Explicit threading of local/global type environments
5. **API Façade**: Stable entry point for AI tooling integration

### Mechanization Benefits

- **Verification**: All definitions and theorems are mechanically checked
- **Generality**: Parameterized types allow instantiation for specific domains
- **Modularity**: Clean separation between Axioms/Core/Class layers
- **Extensibility**: Easy to add new features while preserving properties
- **AI Integration**: Stable API designed for automated reasoning systems

## Development Guidelines

### Adding New Features

1. **Identify the layer**: Axioms (foundational), Core (definitional), or Class (application)
2. **Extend appropriate locale**: `Lux_Axioms`, `Lux_Core`, or `Lux_Class`
3. **State explicit hypotheses**: Use conditional theorem locales when needed
4. **Add status labels**: Mark as PROVEN THEOREM, CONDITIONAL THEOREM, or CONJECTURE
5. **Update API**: Expose new features through `Lux/API.thy`

### Proof Strategies

- **Use `by simp`** for basic algebraic manipulations
- **Use `by assumption`** for hypothesis-dependent results  
- **Use `sorry`** only for conjectures with clear status labels
- **Prefer abstract reasoning** over concrete instantiations

### Testing

```bash
# Run unit tests
isabelle build -s Lux_Tests

# Check specific theories
isabelle process -T Lux/Core/Shell
isabelle process -T Lux/Class/Class
```

## Contributing

When extending the library:

1. **Follow the three-layer architecture**: Axioms → Core → Class
2. **Maintain generic headers**: Use `'H` parameterization
3. **Add explicit hypotheses**: Use conditional theorem locales
4. **Update documentation**: Keep this README current
5. **Test thoroughly**: Ensure all theories compile

## References

- Main paper: `../latex/sections/` (S02-S14)
- Specifications: `../CHATGPT/Lux_*.md`
- Implementation plan: `../CHATGPT/MATHEMATICAL_CONSISTENCY_DESIGN_DECISIONS.md`

---

*This mechanization provides a rigorous foundation for AI-powered software development using the Lux formal logic framework.*
