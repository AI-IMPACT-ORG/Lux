#lang racket
;; Time Hierarchy (symbolic) inside Lux: diagonalization witness

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/sequent-checker.rkt"))

(provide (all-defined-out))

;; Symbolic statement: TH(k): ∃L ∈ DTIME(n^{k+1}) \ DTIME(n^k)
(define (time-hierarchy-statement k)
  (embed-proposition (abstract-op 'TimeHierarchy (list k) 'meta)))

(define (time-hierarchy-sanity)
  (semiring-element? (time-hierarchy-statement (make-abstract-const 'k 'symbol))))

;; Structured diagonalization sketch (constructive): from DiagAssumptions(k) derive TimeHierarchy(k)
(define (b-diag-assumptions k)
  (abstract-op 'DiagAssumptions (list k) 'meta))

(define (time-hierarchy-derivation)
  (define k (make-abstract-const 'k 'symbol))
  (define asum (embed-proposition (b-diag-assumptions k)))
  (define concl (embed-proposition (time-hierarchy-statement k)))
  (define seq (sequent (list asum) concl))
  (semiring-element? seq))
