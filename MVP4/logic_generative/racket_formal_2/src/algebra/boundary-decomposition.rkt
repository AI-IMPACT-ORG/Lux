#lang racket
;; Boundary Decomposition and Reconstitution

(require (file "../foundations/abstract-core.rkt")
         (file "./algebraic-structures.rkt"))

(provide (all-defined-out))

(define (projector-L b) (ι_L (ν_L b)))
(define (projector-R b) (ι_R (ν_R b)))

(define (reconstitute b)
  (define l (projector-L b))
  (define r (projector-R b))
  ((semiring-ops-add B-ops) l r))

(define (residual b)
  ((semiring-ops-add B-ops) b (reconstitute b)))

(define (test-projector-idempotence b)
  (and (abstract-semiring-equal? (projector-L (projector-L b)) (projector-L b))
       (abstract-semiring-equal? (projector-R (projector-R b)) (projector-R b))) )

(define (test-bulk-equals-boundaries b)
  (and (equal? (ν_L b) (ν_L (reconstitute b)))
       (equal? (ν_R b) (ν_R (reconstitute b)))) )

(define (test-residual-properties b)
  (define rb (residual b))
  (define l (ν_L b)) (define r (ν_R b))
  (and (semiring-element? rb)
       (equal? (ν_L rb) ((semiring-ops-add L-ops) l l))
       (equal? (ν_R rb) ((semiring-ops-add R-ops) r r))))

(define (test-residual-invisibility-model-specific b)
  (define rb (residual b))
  (and (semiring-element? (ν_L rb)) (semiring-element? (ν_R rb))))

(define (test-bulk-two-boundaries b)
  (define ρ (reconstitute b))
  (and (semiring-element? (ν_L ρ)) (semiring-element? (ν_R ρ))))

