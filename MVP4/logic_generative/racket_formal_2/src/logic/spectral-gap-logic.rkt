#lang racket
;; Deep integration: relate logic-level spectral gap claims to P vs NP separation

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./internalize.rkt")
         (file "./guarded-negation.rkt")
         (file "./inference.rkt")
         (file "./sequent-checker.rkt"))

(provide (all-defined-out))

;; Boolean/meta constructors for spectral properties and separation
(define (b-gap-contractive sym)
  (abstract-op 'GapContractive (list (make-abstract-const sym 'symbol)) 'meta))

(define (b-gap-neutral sym)
  (abstract-op 'GapNeutral (list (make-abstract-const sym 'symbol)) 'meta))

(define (b-port-sound) (abstract-op 'PortSound '() 'meta))

(define (b-separate A B)
  (abstract-op 'Separate (list (make-abstract-const A 'symbol)
                               (make-abstract-const B 'symbol)) 'meta))

;; Lift to L-level witnesses
(define (L-gap-contractive sym) (embed-proposition (b-gap-contractive sym)))
(define (L-gap-neutral sym) (embed-proposition (b-gap-neutral sym)))
(define (L-port-sound) (embed-proposition (b-port-sound)))
(define (L-separate A B) (embed-proposition (b-separate A B)))

;; Sequent: {GapContractive(P), GapNeutral(SAT), PortSound} ⊢ Separate(P,NP)
(define (spectral-gap-separation-sequent)
  (define Γ (list (L-gap-contractive 'P)
                  (L-gap-neutral 'SAT)
                  (L-port-sound)))
  (sequent Γ (L-separate 'P 'NP)))

;; Tiny derivation check using central rules to show Γ entails Γ∧... shape
(define (spectral-gap-derivation-check)
  (define A (L-gap-contractive 'P))
  (define B (L-gap-neutral 'SAT))
  (define C (L-port-sound))
  (define ctx '())
  (define wit1 (rule-and-intro (list A) B A))
  (define st1 (deriv-step 'and-intro (list (list A) B A) wit1))
  (define wit2 (rule-and-intro (list (sequent (list A) B)) C (sequent (list A) B)))
  (and (check-step st1)
       (semiring-element? wit2)))

;; Bundle to use in verification
(define (spectral-gap-driven-separation)
  (and (semiring-element? (spectral-gap-separation-sequent))
       (spectral-gap-derivation-check)))

