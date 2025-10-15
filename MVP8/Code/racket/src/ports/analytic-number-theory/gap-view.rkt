#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Gap → ANT consequences (symbolic, port-level)

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../logic/internalize.rkt")
         (file "./rc-scheme.rkt")
         (file "./hilbert-polya.rkt"))

(provide (all-defined-out))

(define (gap->ant)
  (define scheme (make-rc-scheme #:label 'ant-default))
  (define s (make-abstract-const 's 'symbol))
  (define ant-ants (rc-antecedents-L scheme))
  (list
   ;; RC + ξ tags (fine-grained)
   (cons 'rc-euler-dirichlet-eq (list-ref ant-ants 0))
   (cons 'rc-universal (list-ref ant-ants 1))
   (cons 'xi-sym (list-ref ant-ants 2))
   (cons 'xi-hadamard (xi-hadamard-sequent scheme))
   (cons 'xi-completed (embed-proposition (abstract-op 'XiCompleted (list (make-abstract-const (rc-scheme-label scheme) 'symbol)) 'meta)))
   ;; HP route manifestations
   (cons 'hp-def (hp-definition-sequent))
   (cons 'hp-selfadjoint (hp-selfadjoint-sequent))
   (cons 'resolvent-link (hp-resolvent-trace-sequent scheme s))))
