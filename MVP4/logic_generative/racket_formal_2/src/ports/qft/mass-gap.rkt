#lang racket
;; QFT mass-gap bridge: logic RG (trace/Lipschitz) + model assumptions ⇒ MassGap and ExpDecay

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../logic/internalize.rkt")
         (file "../../logic/inference.rkt")
         (file "../../logic/traced-operators.rkt")
         (file "../../semantics/categorical-model.rkt")
         (file "./evidence.rkt"))

(provide (all-defined-out))

;; Symbols
(define RG 'Rdet)
(define X_RG 'X_RG)

;; Convenience constructors
(define (L-reflection-positivity label)
  (embed-proposition (abstract-op 'ReflectionPositivity (list (make-abstract-const label 'symbol)) 'meta)))
(define (L-spectral-condition label)
  (embed-proposition (abstract-op 'SpectralCondition (list (make-abstract-const label 'symbol)) 'meta)))
(define (L-cluster-decomposition label)
  (embed-proposition (abstract-op 'ClusterDecomposition (list (make-abstract-const label 'symbol)) 'meta)))

;; Gap/decay targets (symbolic at L)
(define (L-mass-gap-from-c c)
  (embed-proposition (abstract-op 'MassGapFromLipschitz (list c) 'meta)))

(define (L-exp-decay-connected c)
  (embed-proposition (abstract-op 'ExpDecayConnected (list (make-abstract-const 'ConnectedCorrelators 'symbol) c) 'meta)))

;; Sequent: DaggerSMC ∧ ReflectionPositivity ∧ Trace(RG,X) ∧ Lipschitz(RG,c) ⊢ MassGapFromLipschitz(c)
(define (qft-mass-gap-sequent c #:label [label 'qft-default])
  (define Γ (list (L-dagger-smc)
                  (L-reflection-positivity label)
                  (L-trace RG X_RG)
                  (L-trace-lipschitz RG X_RG c)))
  (sequent Γ (L-mass-gap-from-c c)))

;; Sequent: MassGapFromLipschitz(c) ∧ SpectralCondition ∧ ClusterDecomposition ⊢ ExpDecayConnected(c)
(define (qft-exp-decay-sequent c #:label [label 'qft-default])
  (define Γ (list (L-mass-gap-from-c c)
                  (L-spectral-condition label)
                  (L-cluster-decomposition label)))
  (sequent Γ (L-exp-decay-connected c)))

;; Bundle pack
(define (qft-gap-pack)
  (define c (make-abstract-const 'c 'symbol))
  (and (semiring-element? (qft-mass-gap-sequent c))
       (semiring-element? (qft-exp-decay-sequent c))))
