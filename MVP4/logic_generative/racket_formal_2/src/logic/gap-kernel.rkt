#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Gap Kernel: a single abstract witness and reusable invariants

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/internalize.rkt")
         (file "../theorems/gap.rkt")
         (file "../rewrite/engine.rkt"))

(provide (all-defined-out))

;; Abstract, model-agnostic logic gap witness (L-level proposition)
(define (gap-witness)
  (embed-proposition (abstract-op 'LogicGap '() 'meta)))

;; Core invariants associated with the gap, all abstract (no numerics)
;; Returns an association list of (name . ok?)
(define (gap-properties)
  (list
   (cons 'non-expansive (contraction-gap-witness))
   (cons 'dnf-idempotent (dnf-idempotent?))
   (cons 'dnf-transport-invariant (dnf-transport-invariant?))
   (cons 'rewrite-roundtrip (rewrite-eq-roundtrip?))
   (cons 'rewrite-metric-monotone (rewrite-metric-monotone?))
   (cons 'rewrite-red-noninvertible (rewrite-red-noninvertible?))))
