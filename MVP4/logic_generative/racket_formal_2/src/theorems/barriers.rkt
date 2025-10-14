#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Barrier annotations (symbolic L-level): non-relativizing, non-natural, non-algebrizing

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/sequent-checker.rkt"))

(provide (all-defined-out))

;; Meta props
(define (b-nonrelativizing) (abstract-op 'NonRelativizing '() 'meta))
(define (b-nonnatural) (abstract-op 'NonNatural '() 'meta))
(define (b-nonalgebrizing) (abstract-op 'NonAlgebrizing '() 'meta))

(define (L-nonrelativizing) (embed-proposition (b-nonrelativizing)))
(define (L-nonnatural) (embed-proposition (b-nonnatural)))
(define (L-nonalgebrizing) (embed-proposition (b-nonalgebrizing)))

;; Sequent: UsesObservers ∧ UsesLenses ∧ UsesHeaders ⊢ NonRelativizing ∧ NonNatural ∧ NonAlgebrizing
(define (b-uses-obs) (abstract-op 'UsesObservers '() 'meta))
(define (b-uses-lens) (abstract-op 'UsesLenses '() 'meta))
(define (b-uses-headers) (abstract-op 'UsesHeaders '() 'meta))
(define (L-uses-obs) (embed-proposition (b-uses-obs)))
(define (L-uses-lens) (embed-proposition (b-uses-lens)))
(define (L-uses-headers) (embed-proposition (b-uses-headers)))

(define (barriers-sequent)
  (define Γ (list (L-uses-obs) (L-uses-lens) (L-uses-headers)))
  (sequent Γ (embed-proposition (abstract-op 'And3 (list (b-nonrelativizing)
                                                      (b-nonnatural)
                                                      (b-nonalgebrizing)) 'meta))))

(define (barriers-pack)
  (semiring-element? (barriers-sequent)))

