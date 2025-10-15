#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Symbolic beta-system and Callan–Symanzik identity (header-level)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../common/utils.rkt"))

(provide (all-defined-out))

;; Headers: k (phase), mz, mzb; core stays separate.
;; We model β-functions as abstract header updates and γ as a core scale.

;; Use moduli flows as parameterized β/γ (one-step flows)
(define (zero-like? x)
  (and (abstract-const? x) (equal? (abstract-const-value x) 0)))
(define (safe-apply f x) (if (zero-like? x) x (f x)))
(define (beta-k k) (safe-apply (moduli-flow-flow-fn θ_L) k))
(define (beta-mz mz) (safe-apply (moduli-flow-flow-fn μ_L) mz))
(define (beta-mzb mzb) (safe-apply (moduli-flow-flow-fn μ_R) mzb))
(define (gamma-core core) core)

;; One RG step on headers via β/γ (symbolic)
(define (RG-step-headers b)
  (define d (dec-z-zbar b))
  (define k (first d))
  (define mz (second d))
  (define mzb (third d))
  (define core (fourth d))
  (rec-z-zbar (beta-k k) (beta-mz mz) (beta-mzb mzb) (gamma-core core)))

;; Observational equality via ν_L and ν_R
(define (obs-equal? x y)
  (and (abstract-semiring-equal? (nu-L-raw x) (nu-L-raw y))
       (abstract-semiring-equal? (nu-R-raw x) (nu-R-raw y))))

;; Callan–Symanzik identity (observables invariant under header-only changes)
(define (callan-symanzik-identity-holds b)
  (define dl (dec-z-zbar (RG-step-headers b)))
  (define dr (dec-z-zbar (RG-step-headers (NF^B-generalized b))))
  (and (equal? (first dl) (first dr))
       (equal? (second dl) (second dr))
       (equal? (third dl) (third dr))))

;; Header gauge commutation: header-only NF commutes with dec/rec projections
(define (header-gauge-commutation b)
  (define d (dec-z-zbar b))
  (define d2 (dec-z-zbar (apply rec-z-zbar d)))
  (and (equal? (first d) (first d2))
       (equal? (second d) (second d2))
       (equal? (third d) (third d2))))

;; Sanity pack (sampled)
(define (beta-system-sanity)
  (define b B-one)
  (and (callan-symanzik-identity-holds b)
       (header-gauge-commutation b)))
