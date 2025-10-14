#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Generic, reusable lens + metric framework at the L-level (constructive)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./internalize.rkt")
         (file "./inference.rkt")
         (file "./sequent-checker.rkt"))
         
(require (file "./traced-operators.rkt"))

(provide (all-defined-out))

;; Meta constructors
(define (b-lens name)           (abstract-op 'Lens (list (make-abstract-const name 'symbol)) 'meta))
(define (b-neutral-lens name)   (abstract-op 'NeutralLens (list (make-abstract-const name 'symbol)) 'meta))
(define (b-contract-lens name c)(abstract-op 'ContractiveLens (list (make-abstract-const name 'symbol)
                                                                    (make-abstract-const c 'real)) 'meta))
(define (b-domain-metric dom)   (abstract-op 'DomainMetric (list (make-abstract-const dom 'symbol)) 'meta))
(define (b-commute f g)         (abstract-op 'Commutes (list (make-abstract-const f 'symbol)
                                                             (make-abstract-const g 'symbol)) 'meta))

;; L-lifts
(define (L-lens name)           (embed-proposition (b-lens name)))
(define (L-neutral-lens name)   (embed-proposition (b-neutral-lens name)))
(define (L-contract-lens name c)(embed-proposition (b-contract-lens name c)))
(define (L-domain-metric dom)   (embed-proposition (b-domain-metric dom)))
(define (L-commute f g)         (embed-proposition (b-commute f g)))

;; Sequent templates (constructive witnesses)
(define (lens-lipschitz-sequent lens-name c dom)
  ;; Bind lens-name to a traced operator F_lens and hidden wire X_lens
  (define F (string->symbol (format "F_~a" lens-name)))
  (define X (string->symbol (format "X_~a" lens-name)))
  (define Γ (list (L-lens lens-name)
                  (L-domain-metric dom)
                  (L-trace F X)))
  (sequent Γ (L-contract-lens lens-name c)))

(define (lens-neutrality-sequent lens-name)
  (define F (string->symbol (format "F_~a" lens-name)))
  (define X (string->symbol (format "X_~a" lens-name)))
  (sequent (list (L-lens lens-name)
                 (L-trace F X))
           (L-neutral-lens lens-name)))

(define (lens-commute-sequent f g)
  (sequent (list (L-lens f) (L-lens g)) (L-commute f g)))

(define (lens-framework-pack)
  (and (semiring-element? (lens-lipschitz-sequent 'Rdet (make-abstract-const 9/10 'real) 'B))
       (semiring-element? (lens-neutrality-sequent 'Rnd))
       (semiring-element? (lens-commute-sequent 'Red 'Rdet))
       (traced-operators-pack)))
