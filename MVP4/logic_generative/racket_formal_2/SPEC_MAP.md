<!-- (c) 2025 AI.IMPACT GmbH -->

# SPEC → Code Map (Lux)

This document maps sections from the MVP4/CHATGPT specification to the Racket presentation in `racket_formal_2`.

- A0 Semiring structures
  - Code: `src/algebra/algebraic-structures.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-semiring-structure-tests)

- A1 Central scalars (φ, z, z̄, Λ)
  - Code: `src/algebra/central-scalars.rkt`, `src/algebra/explog-decomposition.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-central-scalars-tests)

- A2 Observers/Embeddings and Homomorphisms
  - Code: `src/algebra/algebraic-structures.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-homomorphisms-tests)

- A3 Cross-centrality
  - Code: `src/foundation/v2-axioms.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-cross-centrality-tests)

- A4 Connectives (guarded negation)
  - Code: `src/logic/guarded-negation.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-connective-axioms-tests)

- A5 Braided operators (ad₀…ad₃), Yang–Baxter and commutation
  - Code: `src/algebra/braided-operators.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-braided-operators-tests)

- A6 Exp/Log isomorphism (dec/rec, NF^B)
  - Code: `src/algebra/explog-decomposition.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-exp-log-isomorphism-tests)

- A7 Basepoint/Gen4 axiom
  - Code: `src/core.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-basepoint-tests)

- V10 Core (projectors, bulk=two boundaries, residual)
  - Code: `src/algebra/boundary-decomposition.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (spec-aligned-v10-core-tests)

- CLASS (computational layer, guarded negation universality, ports as outputs)
  - Code: `src/ports/domain-registry.rkt`, `src/physics/feynman-path-integral.rkt`
  - Tests: `tests/spec-aligned-comprehensive-tests.rkt` (V10-Class section)

- Ports – Evidence (Outputs, isomorphisms)
  - Code: `src/ports/evidence/isomorphisms.rkt`, `src/ports/evidence/*-iso.rkt`
  - Verification: `src/verification/verify.rkt`

- Analytic Number Theory (symbolic, RG-controlled)
  - Code: `src/ports/analytic-number-theory/common.rkt`, `rc-scheme.rkt`, `symbolic-dirichlet.rkt`, `symbolic-evidence.rkt`, `zeta-gf.rkt`
  - Verification: `src/ports/analytic-number-theory/evidence.rkt`, `src/verification/verify.rkt`

Meta
- Unified API: `src/main.rkt`
- Language reader: `Lux/lang/reader.rkt`
- Tests: `tests/clean-test-suite.rkt`, `tests/spec-aligned-comprehensive-tests.rkt`
