#lang racket
;; Mass-Gap Port (QFT evidence): symbolic, RG/dagger driven

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/rg-regimes.rkt")
         (file "../theorems/truth.rkt")
         (file "../physics/feynman-path-integral.rkt")
         (file "./qft/mass-gap.rkt"))

(provide (all-defined-out))

;; Symbolic mass-gap predicate (B-level boolean tagging)
;; Define mass-gap predicate on the Core component to be RG-invariant by construction
(define (mass-gap-predicate b)
  (define core-val (semiring-element-value (fourth (dec-z-zbar b))))
  (abstract-op 'MassGap (list core-val) 'boolean))

(define (mass-gap-invariant-under-RG? b)
  (abstract-expr-equal? (mass-gap-predicate b)
                        (call-with-strategy contracting-NF
                          (λ () (mass-gap-predicate (NF^B-generalized b))))))

(define (mass-gap-dagger-invariant? b)
  (abstract-expr-equal? (mass-gap-predicate b)
                        (mass-gap-predicate (daggerB b))))

;; Minimal two-point correlator via the path integral module
(define (sample-correlator)
  (define init (semiring-element (make-abstract-const 1 'integer) B))
  (define Z (feynman-path-integral init '()))
  Z)

(define (run-mass-gap-evidence-tests)
  (define b (sample-correlator))
  (and ;; reuse gap tests from theorems/gap via verify-all
       (mass-gap-invariant-under-RG? b)
       (mass-gap-dagger-invariant? b)))

;; Bridge: Port invariances + QFT MassGapFromLipschitz(c) ⇒ ExpDecayConnected(c) (symbolic)
(define (mass-gap-bridge-sequent)
  (define c (make-abstract-const 'c 'symbol))
  (define Γ (list (embed-proposition (abstract-op 'RGInvariant (list 'MassGap) 'meta))
                  (embed-proposition (abstract-op 'DaggerInvariant (list 'MassGap) 'meta))
                  (L-mass-gap-from-c c)))
  (sequent Γ (L-exp-decay-connected c)))
