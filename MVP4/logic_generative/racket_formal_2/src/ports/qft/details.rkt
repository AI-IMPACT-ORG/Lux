#lang racket
; (c) 2025 AI.IMPACT GmbH
;; QFT detailed producer: returns Z with L-level model/semantics witnesses

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../semantics/categorical-model.rkt")
         (file "../domain-registry.rkt")
         (file "./model.rkt")
         (file "./evidence.rkt"))

(provide produce-qft-detailed)

(define (produce-qft-detailed)
  (register-qft-model!)
  (define port (make-qft-port))
  (let* ([enc ((domain-port-encoder port) 'unit)]
         [Z   ((domain-port-evaluator port) enc)]
         [l-dag (L-dagger-smc)]
         [l-met (L-lawvere-metric 'B)]
         [m-dag (qft-dagger-assumption-L)]
         [m-met (qft-metric-assumption-L)]
         [evs (qft-evidence-witnesses #:label 'qft-default)])
    (append (list Z l-dag l-met m-dag m-met) evs))
)
