#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Information metric monotonicity along RG (symbolic)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/traced-operators.rkt"))

(provide (all-defined-out))

(define (L-fisher-metric) (embed-proposition (abstract-op 'FisherMetric '() 'meta)))
(define (L-info-monotone) (embed-proposition (abstract-op 'InfoMonotone '() 'meta)))

;; Sequent: Trace/Lip(RG,c) ∧ FisherMetric ⊢ InfoMonotone
(define (fisher-monotone-sequent c)
  (define Γ (list (L-trace 'Rdet 'X_RG)
                  (L-trace-lipschitz 'Rdet 'X_RG c)
                  (L-fisher-metric)))
  (sequent Γ (L-info-monotone)))

(define (info-metric-pack)
  (semiring-element? (fisher-monotone-sequent (make-abstract-const 9/10 'real))))

