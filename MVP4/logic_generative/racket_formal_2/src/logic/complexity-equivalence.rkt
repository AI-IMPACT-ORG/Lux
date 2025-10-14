#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Blum-style equivalence (up to poly factors) between Lux predicates and standard classes (symbolic, L-level)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./internalize.rkt")
         (file "./inference.rkt")
         (file "./sequent-checker.rkt")
         (prefix-in cblum: (file "./complexity-blum.rkt")))

(provide (all-defined-out))

;; Meta props
(define (b-equivpoly std Lux)
  (abstract-op 'EquivPoly (list (make-abstract-const std 'symbol)
                                (make-abstract-const Lux 'symbol)) 'meta))
(define (b-portsound) (abstract-op 'PortSound '() 'meta))

;; L lifts
(define (L-equivpoly std Lux) (embed-proposition (b-equivpoly std Lux)))
(define (L-portsound) (embed-proposition (b-portsound)))

;; Sequent: PortSound ∧ EquivPoly(DTIME,L-DTIME) ∧ EquivPoly(NTIME,L-NTIME) ⊢ EquivPoly(P,stdP)
(define (equivalence-sequent)
  (define Γ (list (L-portsound)
                  (L-equivpoly 'DTIME 'L-DTIME)
                  (L-equivpoly 'NTIME 'L-NTIME)))
  (sequent Γ (L-equivpoly 'P 'stdP)))

(define (equivalence-pack)
  (semiring-element? (equivalence-sequent)))
