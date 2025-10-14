#lang racket
;; Gap → QFT consequences (symbolic sequents)

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "./mass-gap.rkt"))

(provide (all-defined-out))

(define (gap->qft)
  (define c (make-abstract-const 'c 'symbol))
  (list
   (cons 'mass-gap-from-lipschitz (qft-mass-gap-sequent c))
   (cons 'exp-decay-connected (qft-exp-decay-sequent c))))

