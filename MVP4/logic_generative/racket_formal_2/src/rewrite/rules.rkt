#lang racket
;; Two-tier rewrite rules: equational ('eq) vs reduction ('red)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/proof.rkt"))

(provide (all-defined-out))

;; A rewrite rule acts on a semiring-element and returns a semiring-element
(struct rewrite-rule (name class guard apply) #:transparent)

;; Helpers
(define (L? x) (and (semiring-element? x) (eq? (semiring-element-semiring-type x) L)))
(define (B? x) (and (semiring-element? x) (eq? (semiring-element-semiring-type x) B)))

;; Extract a boolean expr from an L-element tagged by embed-proposition
(define (extract-boolean-expr Lx)
  (define v (semiring-element-value Lx))
  (if (and (abstract-op? v) (eq? (abstract-op-operator v) 'prop))
      (first (abstract-op-operands v))
      v))

;; Equational rules ('eq)

;; E1: Boolean simplification at L-level (De Morgan, idempotence, etc.)
(define rule-E-boolean
  (rewrite-rule 'E:boolean 'eq L?
    (λ (x)
      (define e (extract-boolean-expr x))
      (embed-proposition (simplify-boolean e)))))

;; E2: exp/log round-trip on B (dec ∘ rec identity canonicalization)
(define rule-E-explog
  (rewrite-rule 'E:explog 'eq B?
    (λ (x)
      (apply rec-z-zbar (dec-z-zbar x)))))

(define eq-rules (list rule-E-boolean rule-E-explog))

;; Reduction rules ('red)

;; R1: RG normal form at B-level (uses current strategy)
(define rule-R-rg
  (rewrite-rule 'R:rg 'red B?
    (λ (x) (NF^B-generalized x))))

(define red-rules (list rule-R-rg))

