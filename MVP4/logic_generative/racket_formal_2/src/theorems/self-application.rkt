#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Self-application: use the rule catalog and sequent-checker to validate
;; rules-as-theorems end-to-end without duplicating machinery.

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/guarded-negation.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/rule-catalog.rkt")
         (file "../logic/sequent-checker.rkt"))

(provide (all-defined-out))

(define (sample-P) (embed-proposition (make-abstract-const 'P 'symbol)))
(define (sample-Q) (embed-proposition (make-abstract-const 'Q 'symbol)))
(define (sample-R) (embed-proposition (make-abstract-const 'R 'symbol)))
(define (sample-G) (embed-proposition (make-abstract-const 'G 'symbol)))
(define empty-ctx '())

;; Build deriv-steps for a representative subset of rules
(define (build-steps)
  (define P (sample-P))
  (define Q (sample-Q))
  (define R (sample-R))
  (define G (sample-G))
  (list
   (let ([wit (rule-and-intro empty-ctx P Q)])
     (deriv-step 'and-intro (list empty-ctx P Q) wit))
   (let ([wit (rule-and-elim-left empty-ctx P Q)])
     (deriv-step 'and-elim-left (list empty-ctx P Q) wit))
   (let ([wit (rule-and-elim-right empty-ctx P Q)])
     (deriv-step 'and-elim-right (list empty-ctx P Q) wit))
   (let ([wit (rule-or-intro-left empty-ctx P Q)])
     (deriv-step 'or-intro-left (list empty-ctx P Q) wit))
   (let ([wit (rule-or-intro-right empty-ctx P Q)])
     (deriv-step 'or-intro-right (list empty-ctx P Q) wit))
   (let ([wit (rule-imp-intro empty-ctx P Q)])
     (deriv-step 'imp-intro (list empty-ctx P Q) wit))
   (let ([wit (rule-imp-trans empty-ctx P Q R)])
     (deriv-step 'imp-trans (list empty-ctx P Q R) wit))
   (let ([wit (rule-imp-ante-strengthen empty-ctx P Q R)])
     (deriv-step 'imp-ante-strengthen (list empty-ctx P Q R) wit))
   (let ([wit (rule-imp-conj empty-ctx P Q R)])
     (deriv-step 'imp-conj (list empty-ctx P Q R) wit))
   (let ([wit (rule-imp-monotone-guarded empty-ctx G P Q)])
     (deriv-step 'imp-monotone-guarded (list empty-ctx G P Q) wit))))

;; Check that for each deriv-step, the sequent-checker’s expected witness
;; equals the catalog-generated witness (rule->witness).
(define (self-apply-ruleset)
  (for/and ([st (build-steps)])
    (check-step st)))

