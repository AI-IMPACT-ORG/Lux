<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Lux Tests - Comprehensive Verification

This directory contains comprehensive verification and testing for the Lux formal logic system, providing systematic verification of all components and their interactions.

## Files

- **Comprehensive_Tests.thy**: Systematic test suite for all Lux components

## Key Components

### Test Framework
- **Systematic Coverage**: Tests cover all major components and their interactions
- **Mathematical Verification**: Tests verify mathematical properties and theorems
- **Computational Verification**: Tests verify computational semantics and behavior
- **Integration Testing**: Tests verify integration between different components

### Axiom Tests
- **Semiring Properties**: Tests for associativity, commutativity, distributivity
- **Observer Coherence**: Tests for observer/embedding relationships
- **Central Scalar Properties**: Tests for centrality and commutativity
- **Braiding Relations**: Tests for Yang-Baxter equations
- **Decomposition Bijectivity**: Tests for exp/log isomorphism

### Core Tests
- **Triality Properties**: Tests for triality involutiveness and observer coherence
- **Reconstitution Properties**: Tests for reconstitution idempotence and orthogonality
- **Normal Form Properties**: Tests for normal form idempotence and structure preservation
- **Generating Functional Properties**: Tests for generating functional linearity and multiplicativity
- **Residual Analysis**: Tests for residual invisibility and properties

### Class Tests
- **Guarded Negation**: Tests for logical operations and properties
- **PSDM Semantics**: Tests for PSDM definedness and stability
- **Dependent Types**: Tests for type alignment and preservation
- **Feynman View**: Tests for quantum field theoretic semantics
- **Domain Ports**: Tests for domain-specific reasoning capabilities

### Integration Tests
- **Cross-Layer Integration**: Tests for integration between Axioms, Core, and Class
- **Domain Port Integration**: Tests for integration with external domains
- **Mathematical Consistency**: Tests for mathematical consistency across all components
- **Computational Soundness**: Tests for computational soundness and correctness

## Usage

### Running Tests
```bash
# Run all tests
isabelle build -s Lux_Tests

# Run specific test categories
isabelle process -T Lux/Tests/Comprehensive_Tests
```

### Adding New Tests
```isabelle
theory MyNewTests
  imports "Lux/Tests/Comprehensive_Tests"
begin

(* Add your new tests here *)

lemma my_new_test: "my_property"
  by (simp add: my_proof)

end
```

### Test Categories
- **Unit Tests**: Tests for individual components
- **Integration Tests**: Tests for component interactions
- **Regression Tests**: Tests to prevent regressions
- **Performance Tests**: Tests for computational performance
- **Correctness Tests**: Tests for mathematical correctness

## Mathematical Principles

1. **Comprehensive Coverage**: Tests cover all major components and interactions
2. **Mathematical Rigor**: Tests verify mathematical properties and theorems
3. **Computational Soundness**: Tests verify computational semantics and behavior
4. **Integration Verification**: Tests verify integration between components
5. **Regression Prevention**: Tests prevent regressions and ensure stability

## License

Copyright (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
