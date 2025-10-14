#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
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

