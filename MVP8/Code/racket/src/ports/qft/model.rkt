#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; QFT model declarations: allow dagger and metric at the model level (port-only)

(require (file "../assumptions.rkt")
         (file "../../foundations/abstract-core.rkt")
         (file "../../logic/internalize.rkt"))

(provide (all-defined-out))

(define (register-qft-model!)
  (register-port-model! 'qft '((dagger . #t)
                               (metric . #t))))

(define (qft-dagger-allowed?) (port-assumption? 'qft 'dagger))
(define (qft-metric-allowed?) (port-assumption? 'qft 'metric))

(define (qft-dagger-assumption-L)
  (if (qft-dagger-allowed?)
      (L-model-assumption 'qft 'dagger)
      (embed-proposition (abstract-op 'NoAssumption '() 'boolean))))

(define (qft-metric-assumption-L)
  (if (qft-metric-allowed?)
      (L-model-assumption 'qft 'metric)
      (embed-proposition (abstract-op 'NoAssumption '() 'boolean))))

