# Racket Generators

This directory hosts a lightweight Racket implementation of the interacting positive logic described in `MVP4/ChatGPT`.  It follows the MDE pyramid layout with logic kernels, DSL front-ends, derived generators, and simple exporters.

## Highlights

- `logic/` contains the signature registry, SMC term syntax, normalization kernels, equality predicates, and the normalized `Gen4` primitive with its braided basepoint collapse.
- `logic/derived.rkt` exposes macros for the derived generating functionals (`Noe5`, `CS5`, `Rice6`, `NR6`).
- `dsl/left.rkt` and `dsl/right.rkt` offer thin boundary DSL helpers wrapping the boolean semiring surfaces.
- `export/` holds Agda/Coq emitters plus a Metamath framework generator that materialises the logic’s signature, axioms, and theorem stubs.
- `tooling/tests.rkt` provides rackunit-based smoke tests that exercise the scale gauge, `Gen4` normalization, and derived operators.

To run the tests:

```bash
raco test tooling/tests.rkt
```

## Example Usage

```racket
#lang racket
(require "logic/signature.rkt"
         "logic/syntax.rkt"
         "logic/derived.rkt"
         "logic/rewrite.rkt")

(define sig (primitive-signature))
(define a0 (make-const-term sig 'a_0))
(define mu (make-const-term sig '1_B))
(define noe (noe5 sig 'e0 a0 a0 a0 a0))
(define cs  (cs5 sig a0 a0 a0 a0 mu))
(normalize/raw sig (app '⊕B (list noe cs)))
```

This evaluates to a canonical bulk term in the normalized calculus.

### Emitting Metamath Framework Files

```racket
#lang racket
(require "logic/signature.rkt"
         "export/metamath.rkt")

(define sig (primitive-signature))
(export-metamath-framework sig "metamath_out")
```

The call writes `metamath_out/framework.mm` (type declarations, formation rules, and axioms) and one stub file per named theorem from the specification. Each theorem file includes `framework.mm` and states the target wff, leaving the proof script for future work.

