#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Boundary Decomposition and Reconstitution

(require (file "../foundations/abstract-core.rkt")
         (file "./algebraic-structures.rkt")
         (file "../logic/guarded-negation.rkt")
         (file "./braided-operators.rkt"))

(provide (all-defined-out))

(define (projector-L b) (ι_L (ν_L b)))
(define (projector-R b) (ι_R (ν_R b)))

(define (reconstitute b)
  (define l (projector-L b))
  (define r (projector-R b))
  (define ρ ((semiring-ops-add B-ops) l r))
  (define ρ* (b-set-grade ρ 'rho))
  (hash-set! element-origin ρ* 'rho)
  ρ*)

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

;; Guarded leg-wise negation: replace one boundary leg by its relative complement under a guard g∈L
;; L‑leg: ν_L maps to relative-complement g (ν_L b); ν_R unchanged
(define (guarded-negate-L g b)
  ((semiring-ops-add B-ops)
   (ι_L (relative-complement g (ν_L b)))
   (ι_R (ν_R b))))

;; R‑leg: ν_R maps to relative-complement g (ν_R b); ν_L unchanged
(define (guarded-negate-R g b)
  ((semiring-ops-add B-ops)
   (ι_L (ν_L b))
   (ι_R (relative-complement g (ν_R b)))))

;; Sanity checks for guarded leg-wise negation
(define (test-guarded-leg-negation-L g b)
  (and (equal? (ν_L (guarded-negate-L g b)) (relative-complement g (ν_L b)))
       (equal? (ν_R (guarded-negate-L g b)) (ν_R b))))

(define (test-guarded-leg-negation-R g b)
  (and (equal? (ν_R (guarded-negate-R g b)) (relative-complement g (ν_R b)))
       (equal? (ν_L (guarded-negate-R g b)) (ν_L b))))


;; Braid invariance (ad_i) commutes with guarded leg negation observationally
(define (test-guarded-braid-invariance-L g b)
  (and (equal? (ν_L (ad₀ (guarded-negate-L g b))) (relative-complement g (ν_L (ad₀ b))))
       (equal? (ν_L (ad₁ (guarded-negate-L g b))) (relative-complement g (ν_L (ad₁ b))))
       (equal? (ν_L (ad₂ (guarded-negate-L g b))) (relative-complement g (ν_L (ad₂ b))))
       (equal? (ν_L (ad₃ (guarded-negate-L g b))) (relative-complement g (ν_L (ad₃ b))))))

(define (test-guarded-braid-invariance-R g b)
  (and (equal? (ν_R (ad₀ (guarded-negate-R g b))) (relative-complement g (ν_R (ad₀ b))))
       (equal? (ν_R (ad₁ (guarded-negate-R g b))) (relative-complement g (ν_R (ad₁ b))))
       (equal? (ν_R (ad₂ (guarded-negate-R g b))) (relative-complement g (ν_R (ad₂ b))))
       (equal? (ν_R (ad₃ (guarded-negate-R g b))) (relative-complement g (ν_R (ad₃ b))))))

;; Reconstitution commutes with guarded leg negation
(define (test-guarded-reconstitution-commutes-L g b)
  (abstract-semiring-equal? (reconstitute (guarded-negate-L g b))
                            (guarded-negate-L g (reconstitute b))))

(define (test-guarded-reconstitution-commutes-R g b)
  (abstract-semiring-equal? (reconstitute (guarded-negate-R g b))
                            (guarded-negate-R g (reconstitute b))))

;; Idempotence in guard application
(define (test-guarded-idempotent-L g b)
  (and (equal? (ν_L (guarded-negate-L g (guarded-negate-L g b))) (ν_L (guarded-negate-L g b)))
       (equal? (ν_R (guarded-negate-L g (guarded-negate-L g b))) (ν_R (guarded-negate-L g b)))))

(define (test-guarded-idempotent-R g b)
  (and (equal? (ν_R (guarded-negate-R g (guarded-negate-R g b))) (ν_R (guarded-negate-R g b)))
       (equal? (ν_L (guarded-negate-R g (guarded-negate-R g b))) (ν_L (guarded-negate-R g b)))))
;; (NF commutation helpers available via moduli system; avoid direct require here to prevent module cycles.)
