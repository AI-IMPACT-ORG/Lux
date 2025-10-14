#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Conservativity demo: adding ZFC axioms to context does not affect derivability of core propositional theorems

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./guarded-negation.rkt")
         (file "./internalize.rkt")
         (file "./inference.rkt")
         (file "./sequent-checker.rkt")
         (file "../set/zfc.rkt"))

(provide (all-defined-out))

;; Build derivation steps that weaken an empty-context theorem into one with axioms in context
(define (weaken-steps-for φ axioms)
  (define steps '())
  (define ctx '())
  (for ([ax axioms])
    (define w (rule-weakening ctx φ (cdr ax)))
    (set! steps (append steps (list (deriv-step 'weakening (list ctx φ (cdr ax)) w))))
    (set! ctx (cons (cdr ax) ctx)))
  steps)

;; Demo for implication transitivity φ = (P⇒R)
(define (conservativity-demo-implies-trans)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define R (embed-proposition (make-abstract-const 'R 'symbol)))
  (define φ (gn-implies P R))
  (check-derivation (weaken-steps-for φ (zfc-axioms))))

