#lang racket
; (c) 2025 AI.IMPACT GmbH

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/boundary-decomposition.rkt")
         (file "../algebra/braided-operators.rkt"))

(provide (all-defined-out))

;; Theorem: Categorical logic coherence holds (appendix)
;; Use the canonical categorical-logic port to extract coherence checks and require all hold.


(define (categorical-logic-detailed)
  (define l1 (semiring-element (get-one) L))
  (define r1 (semiring-element (get-one) R))
  (define b (semiring-element (get-three) B))
  (list
   (test-retraction-left l1)
   (test-retraction-right r1)
   (test-projector-idempotence b)
   (equal? (ν_L (ι_L l1)) l1)
   (equal? (ν_R (ι_R r1)) r1)
   (equal? (ν_L (ad₀ b)) (ν_L b))
   (equal? (ν_R (ad₁ b)) (ν_R b))
   (test-bulk-equals-boundaries b)))

(define (verify-categorical-logic)
  (for/and ([b (in-list (categorical-logic-detailed))]) b))
