#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Observer-level identity/idempotence utilities for reuse across domain maps

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../common/utils.rkt"))

(provide (all-defined-out))

(define (observer-equal? x y)
  (and (abstract-semiring-equal? (nu-L-raw x) (nu-L-raw y))
       (abstract-semiring-equal? (nu-R-raw x) (nu-R-raw y))))

(define (observer-idempotent-under nf reps)
  (for/and ([b reps])
    (let ([h1 (nf b)] [h2 (nf (nf b))])
      (observer-equal? h2 h1))) )

