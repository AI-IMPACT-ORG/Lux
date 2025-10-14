#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Gap → QFT consequences (symbolic sequents)

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "./mass-gap.rkt"))

(provide (all-defined-out))

(define (gap->qft)
  (define c (make-abstract-const 'c 'symbol))
  (define lbl 'qft-default)
  (list
   ;; Model assumption tags (fine-grained)
   (cons 'reflection-positivity (L-reflection-positivity lbl))
   (cons 'spectral (L-spectral-condition lbl))
   (cons 'cluster (L-cluster-decomposition lbl))
   ;; Gap‑driven manifestations
   (cons 'mass-gap-from-lipschitz (qft-mass-gap-sequent c))
   (cons 'exp-decay-connected (qft-exp-decay-sequent c))))
