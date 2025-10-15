<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Lux Class - Application Layer

This directory contains the application layer of the Lux formal logic system, providing foundational logic, computational semantics, and domain-specific reasoning over the Core definitions.

## Files

- **Class.thy**: Guarded negation, PSDM semantics, dependent types, Feynman view, domain ports, computational universality

## Key Components

### Foundational Logic
- **Guarded Negation**: RC-GN relative complement on principal ideals
- **Logical Operations**: `gn_and`, `gn_or`, `gn_implies`, `gn_iff`, `gn_nand`
- **Computational Universality**: NAND-based universal computation
- **Logical Properties**: Involutive negation, commutative operations

### PSDM Semantics
- **Partial Stable Domain Maps**: Mathematical foundation for partial functions
- **PSDM Operations**: `psdm_defined`, `psdm_apply`, `psdm_compose`
- **PSDM Properties**: Stability, halting, computational coherence
- **Irreversible Computation**: Clean handling of non-terminating processes

### Dependent Type System
- **Type Environments**: Local and global type environments
- **Type Alignment**: `type_aligned t ≡ local_type_env t = global_type_env t`
- **Type Preservation**: Operations preserve type alignment
- **Type Safety**: Ensures computational correctness

### Feynman View
- **Sum-over-Histories**: Quantum field theoretic computational semantics
- **History Weight**: `history_weight t` for computation path weights
- **Path Integral**: `path_integral f` for sum over all computation paths
- **Feynman Propagator**: Transition amplitude between states
- **Feynman Amplitude**: Total amplitude for computational processes

### Domain Ports
- **Turing Machine Port**: Simulation of Turing machines
- **Lambda Calculus Port**: Simulation of lambda calculus
- **Quantum Field Theory Port**: QFT simulation
- **Blockchain Port**: Consensus simulation
- **Domain Integration**: Clean interfaces to external computational domains

## Mathematical Foundations

### Guarded Negation
- **Relative Complement**: `relative_complement g x = g + x * g`
- **Guarded Negation**: `gn_not x = relative_complement guard x`
- **Lattice Theoretic Foundation**: Based on relative complement in lattice theory
- **Logical Soundness**: Avoids classical negation paradoxes

### PSDM Semantics
- **Domain Theoretic Foundation**: Based on partial functions in domain theory
- **PSDM Definedness**: `psdm_defined f ≡ f * f = f`
- **PSDM Application**: `psdm_apply f x = (if psdm_defined f then Some (f * x) else None)`
- **Computational Naturalness**: Models defined/undefined states in computational processes

### Feynman View
- **Quantum Field Theoretic Foundation**: Based on path integrals in quantum field theory
- **History Weight**: `history_weight t = pow phi k * pow (z * zbar) (mz + mbar)`
- **Path Integral**: `path_integral f = f 0 + f 1`
- **Quantum Computational Naturalness**: Models quantum computational processes

## Usage

### Importing Class
```isabelle
theory MyTheory
  imports "Lux/Class/Class"
begin

context Lux_Class begin
  (* Access to all application-level features *)
  
  lemma example: "gn_not (gn_not x) = x"
    by (simp add: gn_not_involutive)
end

end
```

### Using Guarded Negation
```isabelle
context Lux_Class begin
  definition my_logical_operation :: "L => L => L" where
    "my_logical_operation x y = gn_and (gn_not x) y"
    
  lemma my_property: "my_logical_operation x x = gn_not x"
    by (simp add: my_logical_operation_def gn_and_def gn_not_def)
end
```

### Using PSDM
```isabelle
context Lux_Class begin
  definition my_psdm_operation :: "B => B option" where
    "my_psdm_operation t = psdm_apply t t"
    
  lemma my_psdm_property: "psdm_defined t ==> my_psdm_operation t = Some (t * t)"
    by (simp add: my_psdm_operation_def psdm_apply_def)
end
```

### Using Domain Ports
```isabelle
context Lux_Class begin
  definition my_boolean_operation :: "B => boolean_carrier option" where
    "my_boolean_operation t = boolean_port t"
    
  definition my_lambda_operation :: "B => lambda_carrier option" where
    "my_lambda_operation t = lambda_port t"
end
```

## Mathematical Principles

1. **Foundational Logic**: Guarded negation provides sound logical foundations
2. **Computational Semantics**: PSDM provides clear computational meaning
3. **Type Safety**: Dependent types ensure computational correctness
4. **Quantum Foundations**: Feynman view provides quantum field theoretic semantics
5. **Domain Integration**: Clean interfaces to external computational domains

## License

Copyright (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
