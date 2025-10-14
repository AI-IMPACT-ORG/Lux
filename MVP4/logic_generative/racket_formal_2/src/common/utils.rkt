#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Shared utilities (abstract, no numeric evaluation)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt"))

(provide (all-defined-out))

;; Semiring element equality (type + abstract expr)
(define (equal-el? a b)
  (abstract-semiring-equal? a b))

;; Distance on B as an uninterpreted metric symbol Bdist(vx, vy)
(define (b-distance x y)
  (abstract-expr 'Bdist (list (semiring-element-value x)
                              (semiring-element-value y))
                 'metric))

;; Constructors
(define (mkB v) (semiring-element (make-abstract-const v 'integer) B))
;; Symbolic B element constructor (no numeric coding)
(define (mkB-sym s)
  (semiring-element (make-abstract-symbol s) B))
(define (mkL v) (semiring-element (make-abstract-const v 'integer) L))

;; Raw observers (value-level projection without origin tracking)
(define (nu-L-raw b) (semiring-element (semiring-element-value b) L))
(define (nu-R-raw b) (semiring-element (semiring-element-value b) R))
