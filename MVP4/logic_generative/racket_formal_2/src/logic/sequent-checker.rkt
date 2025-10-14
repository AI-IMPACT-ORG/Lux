#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Internal sequent derivation checker (stays inside Lux, uses L-level rules)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./guarded-negation.rkt")
         (file "./internalize.rkt")
         (file "./inference.rkt")
         (file "./rule-catalog.rkt"))

(provide (all-defined-out))

;; A derivation step records a rule tag, its arguments, and the provided L-witness
(struct deriv-step (rule args witness) #:transparent)

;; Compute the expected witness for a rule
(define (expected-witness step)
  (rule->witness (deriv-step-rule step) (deriv-step-args step)))

;; Check a single step (L-witness must equal the expected one)
(define (check-step step)
  (define got (deriv-step-witness step))
  (define exp (expected-witness step))
  (and (semiring-element? got)
       (semiring-element? exp)
       (eq? (semiring-element-semiring-type got) L)
       (eq? (semiring-element-semiring-type exp) L)
       (abstract-expr-equal? (semiring-element-value got)
                             (semiring-element-value exp))))

;; Check a derivation (all steps individually check out)
(define (check-derivation steps)
  (andmap check-step steps))
