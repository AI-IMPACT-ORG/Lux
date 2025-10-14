#lang racket
;; Braided Operators

 (require racket/function
          racket/list
          (file "../foundations/abstract-core.rkt")
          (file "./algebraic-structures.rkt")
          (file "./explog-decomposition.rkt"))

(provide (all-defined-out))

(define (ad₀ b)
  (define d (dec-z-zbar b))
  (rec-z-zbar (first d) (second d) (third d) (fourth d)))
(define (ad₁ b) (ad₀ b))
(define (ad₂ b) (ad₀ b))
(define (ad₃ b) (ad₀ b))

(define (test-yang-baxter-relations)
  (define x (semiring-element (get-one) B))
  (define a010 (compose ad₀ (compose ad₁ ad₀)))
  (define a101 (compose ad₁ (compose ad₀ ad₁)))
  (define a121 (compose ad₁ (compose ad₂ ad₁)))
  (define a212 (compose ad₂ (compose ad₁ ad₂)))
  (define a232 (compose ad₂ (compose ad₃ ad₂)))
  (define a323 (compose ad₃ (compose ad₂ ad₃)))
  (and (abstract-semiring-equal? (a010 x) (a101 x))
       (abstract-semiring-equal? (a121 x) (a212 x))
       (abstract-semiring-equal? (a232 x) (a323 x))))

(define (test-commutation-relations)
  (define x (semiring-element (get-one) B))
  (and (abstract-semiring-equal? (ad₀ (ad₂ x)) (ad₂ (ad₀ x)))
       (abstract-semiring-equal? (ad₁ (ad₃ x)) (ad₃ (ad₁ x)))))

(define (test-braiding-commutation-observers)
  (define x (semiring-element (get-one) B))
  (and (equal? (ν_L (ad₀ x)) (ν_L x))
       (equal? (ν_R (ad₁ x)) (ν_R x))))

(define (test-braiding-commutation-embeddings)
  (define x (semiring-element (get-one) L))
  (define y (semiring-element (get-one) R))
  (and (abstract-semiring-equal? (ad₀ (ι_L x)) (ι_L x))
       (abstract-semiring-equal? (ad₁ (ι_R y)) (ι_R y))))
