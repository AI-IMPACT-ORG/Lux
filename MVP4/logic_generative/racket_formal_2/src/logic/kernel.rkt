#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Kernel-level tautologies and constructions (L-level)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./guarded-negation.rkt")
         (file "./internalize.rkt"))

(provide (all-defined-out))

;; Variables as embedded propositions
(define (P) (embed-proposition (make-abstract-const 'P 'symbol)))
(define (Q) (embed-proposition (make-abstract-const 'Q 'symbol)))

;; Basic tautologies (as L-level witnesses)
(define (taut-reflexivity)
  (gn-implies (P) (P)))

(define (taut-and-intro)
  (gn-implies (P) (gn-implies (Q) (gn-and (P) (Q)))))

(define (taut-and-elim-left)
  (gn-implies (gn-and (P) (Q)) (P)))

(define (taut-and-elim-right)
  (gn-implies (gn-and (P) (Q)) (Q)))

(define (taut-or-intro-left)
  (gn-implies (P) (gn-or (P) (Q))))

(define (taut-or-intro-right)
  (gn-implies (Q) (gn-or (P) (Q))))

(define (taut-double-negation)
  (gn-iff (gn-not (gn-not (P))) (P)))

(define (taut-de-morgan-and)
  (gn-iff (gn-not (gn-and (P) (Q)))
          (gn-or (gn-not (P)) (gn-not (Q)))))

(define (kernel-basics)
  (list (cons 'reflexivity (taut-reflexivity))
        (cons 'and-intro (taut-and-intro))
        (cons 'and-elim-left (taut-and-elim-left))
        (cons 'and-elim-right (taut-and-elim-right))
        (cons 'or-intro-left (taut-or-intro-left))
        (cons 'or-intro-right (taut-or-intro-right))
        (cons 'double-negation (taut-double-negation))
        (cons 'de-morgan-and (taut-de-morgan-and))))

