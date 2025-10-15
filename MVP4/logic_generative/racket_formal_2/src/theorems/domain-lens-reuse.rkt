#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Reusable lens semantics across domain maps (QFT, Analytic Number Theory)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/lens-framework.rkt")
         (file "../semantics/observer-identity.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../ports/domain-registry.rkt"))

(provide (all-defined-out))

;; QFT: use RG lens (contractive) and Gauge-only lens (neutral)
(define (qft-lens-pack)
  (and (semiring-element? (lens-lipschitz-sequent 'RG_QFT (make-abstract-const 9/10 'real) 'B))
       (semiring-element? (lens-neutrality-sequent 'GaugeOnly))))

;; ANT: RC normalization lens (contractive) and Header-only lens (neutral)
(define (ant-lens-pack)
  (and (semiring-element? (lens-lipschitz-sequent 'RC_ANT (make-abstract-const 9/10 'real) 'B))
       (semiring-element? (lens-neutrality-sequent 'HeaderOnly))))

(define (domain-lens-reuse-pack)
  (and (qft-lens-pack)
       (ant-lens-pack)))

