<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Lux Axioms - Mathematical Foundations

This directory contains the mathematical foundations of the Lux formal logic system, implementing the A0-A7 axioms with elegant type class hierarchies and categorical foundations.

## Files

- **Atomic.thy**: Base axioms A0-A7, semirings L/B/R, observers/embeddings, braiding operators

## Key Components

### Type Class Hierarchy
- **Semiring Type Class**: Unified algebraic structure with elegant axioms
- **Observer/Embedding Locale**: Categorical framework for boundary-bulk relationships
- **Braiding System**: Yang-Baxter relationships for quantum group theoretic structure
- **Decomposition System**: Exponential/logarithmic structure for computational semantics
- **Central Scalar System**: Commutative elements for measurement and observation

### Mathematical Structures
- **Three Semirings**: L (left boundary), B (bulk), R (right boundary)
- **Observers/Embeddings**: `ν_L : B → L`, `ι_L : L → B` with retraction properties
- **Central Scalars**: φ, z, z̄ with Λ := z ⊗_B z̄
- **Exp/Log Structure**: Decomposition `dec : B → (H × H × H) × Core`
- **Braiding Operators**: `ad₀, ad₁, ad₂, ad₃` satisfying Yang-Baxter relations

### Mathematical Elegance
- **Unified Semiring Framework**: Single type class for all semiring structures
- **Categorical Foundations**: Observer/embedding relationships as adjoint functors
- **Minimal Axioms**: Each axiom serves a clear mathematical purpose
- **Clean Separation**: Each mathematical concept is isolated and well-defined
- **Maximal Expressiveness**: Minimal axioms provide maximal mathematical power

## Usage

### Importing Axioms
```isabelle
theory MyTheory
  imports "Lux/Axioms/Atomic"
begin

context Lux_Axioms begin
  (* Access to all axiom definitions and theorems *)
  
  lemma example: "addB x y = addB y x"
    by (simp add: addB_comm)
end

end
```

### Extending Axioms
```isabelle
theory MyExtension
  imports "Lux/Axioms/Atomic"
begin

locale MyExtension = Lux_Axioms +
  fixes my_operation :: "'B => 'B"
  assumes my_property: "my_operation zeroB = zeroB"
begin
  (* Your extensions here *)
end

end
```

## Mathematical Principles

1. **Structure over Syntax**: Focus on mathematical relationships
2. **Abstraction over Concretion**: Use type classes and locales
3. **Elegance over Verbosity**: Concise, clear definitions
4. **Consistency over Convenience**: Mathematically sound foundations

## License

Copyright (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
