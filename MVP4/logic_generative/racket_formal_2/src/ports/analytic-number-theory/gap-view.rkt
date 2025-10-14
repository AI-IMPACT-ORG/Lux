#lang racket
;; Gap → ANT consequences (symbolic, port-level)

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "./rc-scheme.rkt")
         (file "./hilbert-polya.rkt"))

(provide (all-defined-out))

(define (gap->ant)
  (define scheme (make-rc-scheme #:label 'ant-default))
  (define s (make-abstract-const 's 'symbol))
  (list
   (cons 'hp-def (hp-definition-sequent))
   (cons 'hp-selfadjoint (hp-selfadjoint-sequent))
   (cons 'resolvent-link (hp-resolvent-trace-sequent scheme s))
   (cons 'xi-hadamard (xi-hadamard-sequent scheme))))

