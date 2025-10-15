#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../algebra/braided-operators.rkt")
         (file "../logic/guarded-negation.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt"))

(provide (all-defined-out))

;; Transport invariance: for L-level sequent witnesses built from internal rules, 
;; ν_L∘ι_L acts as identity (global lift and reflect does not change the proof object)

(define (transport-invariance-mp)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define ctx '())
  (define w (rule-mp ctx P Q))
  (abstract-semiring-equal? (ν_L (ι_L w)) w))

(define (transport-invariance-and-intro)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define ctx '())
  (define w (rule-and-intro ctx P Q))
  (abstract-semiring-equal? (ν_L (ι_L w)) w))

;; Global (B-level) equalities induce local (L-level) instances by ν_L
(define (global-to-local-naturality)
  (define b (semiring-element (get-three) B))
  (and (equal? (ν_L (ad₀ b)) (ν_L b))
       (equal? (ν_R (ad₁ b)) (ν_R b))))

;; NF^B stability under lift-reflect
(define (nf-lift-stability)
  (define b (semiring-element (get-five) B))
  (define lhs (ν_L (NF^B-generalized b)))
  (define rhs (ν_L (NF^B-generalized (ι_L (ν_L b)))))
  (abstract-semiring-equal? lhs rhs))

;; Local boundary uniqueness via reconstitution
(require (file "../algebra/boundary-decomposition.rkt"))

(define (local-boundary-uniqueness)
  (define b (semiring-element (get-three) B))
  (define rec (reconstitute b))
  (and (equal? (ν_L b) (ν_L rec))
       (equal? (ν_R b) (ν_R rec))))

;; Local exp/log coherence: L/R projections unchanged under dec∘rec
(define (local-explog-coherence)
  (define b (semiring-element (make-abstract-const 7 'integer) B))
  (define d (dec-z-zbar b))
  (define r (apply rec-z-zbar d))
  (and (equal? (ν_L b) (ν_L r))
       (equal? (ν_R b) (ν_R r))))

;; Boundary uniqueness up to NF: reconstructing from local boundaries yields same NF^B
(define (global-uniqueness-up-to-nf)
  (define b (semiring-element (get-five) B))
  (define d (dec-z-zbar b))
  (define b2 (apply rec-z-zbar d))
  (abstract-semiring-equal? (NF^B-generalized b) (NF^B-generalized b2)))
