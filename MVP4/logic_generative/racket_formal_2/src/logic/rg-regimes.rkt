#lang racket
; (c) 2025 AI.IMPACT GmbH
;; RG regime helpers: shared strategy utilities

(require (file "../moduli/moduli-system.rkt"))

(provide (all-defined-out))

;; Build expanding/contracting normal-form strategies from parametric strategies
(define expanding-NF (normal-form-strategy 'expanding (parametric-nf-fn expanding-parametric-strategy) '()))
(define contracting-NF (normal-form-strategy 'contracting (parametric-nf-fn contracting-parametric-strategy) '()))

(define (call-with-strategy strategy th)
  (define old *current-normal-form-strategy*)
  (set-normal-form-strategy! strategy)
  (define out (th))
  (set-normal-form-strategy! old)
  out)

