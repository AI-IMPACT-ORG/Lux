#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Categorical naturality mini-theorems for observers and exp/log

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/braided-operators.rkt")
         (file "../algebra/explog-decomposition.rkt"))

(provide (all-defined-out))

(define (naturality-braids)
  (for/and ([v '(1 2 3 5)])
    (define b (semiring-element (make-abstract-const v 'integer) B))
    (and (equal? (ν_L (ad₀ b)) (ν_L b))
         (equal? (ν_R (ad₁ b)) (ν_R b)))))

(define (naturality-explog)
  (for/and ([v '(2 3 5 7)])
    (define b (semiring-element (make-abstract-const v 'integer) B))
    (define d (dec-z-zbar b))
    (define r (apply rec-z-zbar d))
    (and (equal? (ν_L b) (ν_L r))
         (equal? (ν_R b) (ν_R r)))))

