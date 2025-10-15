#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; ANT model declarations: allow dagger at the model level (port-only)

(require (file "../../foundations/abstract-core.rkt")
         (file "../assumptions.rkt")
         (file "../../semantics/categorical-model.rkt")
         (file "../../logic/internalize.rkt"))

(provide (all-defined-out))

;; Register that the ANT port operates with a dagger-enabled concrete model.
(define (register-ant-model!)
  (register-port-model! 'analytic-number-theory '((dagger . #t))))

;; Simple predicate: is ANT model declared with dagger?
(define (ant-dagger-allowed?)
  (port-assumption? 'analytic-number-theory 'dagger))

;; Optional: expose an L-level witness that "ANT model has dagger" when declared.
(define (ant-dagger-assumption-L)
  (if (ant-dagger-allowed?)
      (L-model-assumption 'analytic-number-theory 'dagger)
      (embed-proposition (abstract-op 'NoAssumption '() 'boolean))))
