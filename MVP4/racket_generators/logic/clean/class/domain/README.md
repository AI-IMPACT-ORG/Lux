# Domain Ports Overview

## Renamed Port Folders

All domain port folders have been renamed to be more recognizable and descriptive:

### Original → New Names
- `boolean` → `boolean-logic`
- `lambda` → `lambda-calculus` 
- `infoflow` → `information-theory`
- `qft` → `quantum-field-theory`
- `computation` → `computational-complexity`
- `ant` → `analytic-number-theory`
- `kernel` → `operating-systems`
- `metamath` → `formal-mathematics`

## Port Descriptions

Each port folder now contains a comprehensive README.md file explaining:

### 1. Boolean Logic Port (`boolean-logic/`)
- **Scope**: Boolean algebra and RAM-based computation
- **Features**: AND, OR, NOT, NAND, NOR, XOR operations, memory access patterns
- **Use Cases**: Digital circuit design, SAT problem analysis, logical reasoning

### 2. Lambda Calculus Port (`lambda-calculus/`)
- **Scope**: λ-calculus computation and functional programming
- **Features**: Variable binding, beta reduction, alpha conversion, Church encoding
- **Use Cases**: Functional programming semantics, computability theory, type theory

### 3. Information Theory Port (`information-theory/`)
- **Scope**: Shannon entropy and information theory
- **Features**: H(X), I(X;Y), channel capacity, kernel gap analysis, Kolmogorov complexity
- **Use Cases**: Data compression, communication analysis, machine learning

### 4. Quantum Field Theory Port (`quantum-field-theory/`)
- **Scope**: Quantum field theory and particle physics
- **Features**: Propagators, QFT axioms, cosmological constant, effective CPT
- **Use Cases**: Particle physics, cosmological models, high-energy physics

### 5. Computational Complexity Port (`computational-complexity/`)
- **Scope**: Computational complexity theory
- **Features**: P, NP, PSPACE, EXP classification, Church-Turing equivalence
- **Use Cases**: Algorithm analysis, complexity verification, program correctness

### 6. Analytic Number Theory Port (`analytic-number-theory/`)
- **Scope**: Analytic number theory and unsolved problems
- **Features**: Riemann zeta, Goldbach's conjecture, Collatz conjecture, fundamental theorems
- **Use Cases**: Number theory research, conjecture analysis, spectral analysis

### 7. Operating Systems Port (`operating-systems/`)
- **Scope**: Operating system concepts and kernel functionality
- **Features**: System calls, process management, memory management, device access
- **Use Cases**: OS design, kernel modeling, system call verification

### 8. Formal Mathematics Port (`formal-mathematics/`)
- **Scope**: Formal mathematics and proof systems
- **Features**: Metamath integration, formal proofs, axiom systems, theorem proving
- **Use Cases**: Formal mathematics research, proof verification, automated theorem proving

## Updated API

The API has been updated to reflect the new port names:
- `port-boolean-logic()`
- `port-lambda-calculus()`
- `port-information-theory()`
- `port-quantum-field-theory()`
- `port-computation()`
- `port-analytic-number-theory()`
- `port-operating-systems()`
- `port-formal-mathematics()`

## Integration

All ports seamlessly integrate with the CLEAN v10 framework's:
- Normal form computation
- Boundary sum properties
- Renormalization flow
- Observer invisibility principles

Each port provides domain-specific operations while maintaining mathematical consistency with the underlying framework.
