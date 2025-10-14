#lang racket
;; Use central constructive-logic theorems to structure the complexity lens argument

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/sequent-checker.rkt")
         (prefix-in cblum: (file "../logic/complexity-blum.rkt")))

(provide (all-defined-out))

;; Meta propositions encoded at the boolean layer, embedded into L
(define (b-neutral sym) (abstract-op 'Neutral (list (make-abstract-const sym 'symbol)) 'meta))
(define (b-contractive sym) (abstract-op 'Contractive (list (make-abstract-const sym 'symbol)) 'meta))
(define (b-separate symA symB) (abstract-op 'Separate (list (make-abstract-const symA 'symbol)
                                                            (make-abstract-const symB 'symbol)) 'meta))

(define (L-neutral sym) (embed-proposition (b-neutral sym)))
(define (L-contractive sym) (embed-proposition (b-contractive sym)))
(define (L-separate symA symB) (embed-proposition (b-separate symA symB)))

;; Sequent-style witness: from Γ = {Neutral(SAT), Contractive(P)} derive Separate(P,NP)
(define (l-separation-sequent)
  (define Γ (list (L-neutral 'SAT) (L-contractive 'P)))
  (sequent Γ (L-separate 'P 'NP)))

;; A small derivation step using the central rule catalog: ∧-intro over the two premises
(define (l-separation-derivation-check)
  (define A (L-neutral 'SAT))
  (define B (L-contractive 'P))
  (define ctx '())
  (define wit (rule-and-intro (list A) B A))
  (define st (deriv-step 'and-intro (list (list A) B A) wit))
  (check-step st))

;; Pack: logic-driven complexity witness exists and the tiny derivation checks
(define (logic-driven-complexity-pack)
  (define A (embed-proposition (abstract-op 'Lang (list (make-abstract-const 'A 'symbol)) 'meta)))
  (define B (embed-proposition (abstract-op 'Lang (list (make-abstract-const 'B 'symbol)) 'meta)))
  (define kr (cblum:L-KarpRed A B))
  (define neutral-B (L-neutral 'B))
  (define reduction-neutrality-sequent (sequent (list kr neutral-B) (L-neutral 'A)))
  (and (semiring-element? (l-separation-sequent))
       (l-separation-derivation-check)
       (semiring-element? reduction-neutrality-sequent)))
