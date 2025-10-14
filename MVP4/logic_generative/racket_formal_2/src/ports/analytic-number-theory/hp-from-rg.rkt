#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Bridge module: encode that the logic-level RG operator induces
;; a Hilbert–Pólya candidate at the ANT domain map level.

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../logic/internalize.rkt")
         (file "../../logic/inference.rkt")
         (file "../../logic/traced-operators.rkt")
         (file "../../semantics/categorical-model.rkt")
         (file "../assumptions.rkt")
         (file "./model.rkt")
         (file "./rc-scheme.rkt")
         (file "./hilbert-polya.rkt"))

(provide rg-to-hp-selfadjoint-sequent
         rg-to-hp-resolvent-trace-sequent
         hp-from-rg-pack)

;; Logic-level symbol for RG (deterministic flow) and a witness of tracing
(define RG 'Rdet)
(define X_witness 'X_RG)

;; Sequent: (Trace(RG,X) ∧ Lipschitz(RG,c)) ∧ DaggerSMC ∧ ANT‑Dagger ⇒ SelfAdjoint(HP_ANT)
(define (rg-to-hp-selfadjoint-sequent c)
  (define Γ (list (L-trace RG X_witness)
                  (L-trace-lipschitz RG X_witness c)
                  (L-dagger-smc)
                  (ant-dagger-assumption-L)))
  (sequent Γ (L-selfadjoint (b-hp-operator))))

;; Sequent: RC invariants ∧ Trace(RG,X) ⇒ TraceResolvent(HP_ANT,s) = −d/ds log ξ(s) (symbolic)
(define (rg-to-hp-resolvent-trace-sequent scheme s)
  (define Γ (list (embed-proposition (abstract-op 'RCInvariant (list (make-abstract-const (rc-scheme-label scheme) 'symbol)) 'meta))
                  (L-trace RG X_witness)))
  (sequent Γ (L-resolvent-trace-equals (b-hp-operator) s)))

(define (hp-from-rg-pack)
  (define scheme (make-rc-scheme #:label 'ant-default))
  (and (semiring-element? (rg-to-hp-selfadjoint-sequent (make-abstract-const 9/10 'real)))
       (semiring-element? (rg-to-hp-resolvent-trace-sequent scheme (make-abstract-const 's 'symbol)))))
