#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Shared utilities (abstract, no numeric evaluation)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../moduli/moduli-system.rkt"))

(provide (all-defined-out))

;; Semiring element equality (type + abstract expr)
(define (equal-el? a b)
  (abstract-semiring-equal? a b))

;; Equality/Truth helpers (non‑collapsing)
;; 1) Definitional equality (algebraic): raw equality under ACU+distributivity.
(define (eq-def? a b)
  (abstract-semiring-equal? a b))

;; 2) Observational equality: via observers, optionally after NF^B.
(define (eq-obs-L? a b #:nf? [nf? #f])
  (define (obs x) (if nf? (ν_L (NF^B-generalized x)) (ν_L x)))
  (eq-def? (obs a) (obs b)))

(define (eq-obs-R? a b #:nf? [nf? #f])
  (define (obs x) (if nf? (ν_R (NF^B-generalized x)) (ν_R x)))
  (eq-def? (obs a) (obs b)))

;; 3) Gauge equality on B (headers only): NF^B‑equivalence.
(define (eq-NF? a b)
  (eq-def? (NF^B-generalized a) (NF^B-generalized b)))

;; Distance on B as an uninterpreted metric symbol Bdist(vx, vy)
(define (b-distance x y)
  (abstract-expr 'Bdist (list (origin-strip-value (semiring-element-value x))
                              (origin-strip-value (semiring-element-value y)))
                 'metric))

;; Constructors
(define (mkB v) (semiring-element (make-abstract-const v 'integer) B))
;; Symbolic B element constructor (no numeric coding)
(define (mkB-sym s)
  (semiring-element (make-abstract-symbol s) B))
(define (mkL v) (semiring-element (make-abstract-const v 'integer) L))

;; Raw observers (value-level projection without origin tracking)
(define (nu-L-raw b) (semiring-element (origin-strip-value (semiring-element-value b)) L))
(define (nu-R-raw b) (semiring-element (origin-strip-value (semiring-element-value b)) R))
