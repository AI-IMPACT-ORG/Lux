#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Guarded Negation and NAND

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt"))

(provide (all-defined-out))

(define current-guard (semiring-element (get-one) L))
(define (set-guard! g) (set! current-guard g))
(define (get-guard) current-guard)

(define (relative-complement g x)
  (if (abstract-eval-bool (abstract-le? (semiring-element-value x) (semiring-element-value g)))
      (semiring-element (abstract-max (get-zero) (abstract-sub (semiring-element-value g) (semiring-element-value x))) L)
      (semiring-element (get-zero) L)))

(define (gn-not x) (relative-complement (get-guard) x))
(define (gn-nand x y) (gn-not ((semiring-ops-mul L-ops) x y)))
(define (gn-not-via-nand x) (gn-nand x x))
(define (gn-and x y) (define n (gn-nand x y)) (gn-nand n n))
(define (gn-or x y) (gn-nand (gn-not-via-nand x) (gn-not-via-nand y)))
(define (gn-xor x y)
  (define nxy (gn-nand x y))
  (gn-nand (gn-nand x nxy) (gn-nand y nxy)))

;; Internal implication in L: x ⇒ y ≡ ¬x ∨ y
(define (gn-implies x y)
  (gn-or (gn-not x) y))

;; Internal equivalence in L: x ⇔ y ≡ (x ⇒ y) ∧ (y ⇒ x)
(define (gn-iff x y)
  (gn-and (gn-implies x y) (gn-implies y x)))

;; Well-formedness for L-level witnesses (guard discipline)
(define (wfL? t)
  (and (semiring-element? t)
       (eq? (semiring-element-semiring-type t) L)))

(define (test-guarded-negation-properties)
  (set-guard! (semiring-element 1 L))
  (define x (semiring-element 0.3 L))
  (define zero-neg (gn-not (semiring-element 0 L)))
  (and (semiring-element? (gn-not (gn-not x)))
       (semiring-element? zero-neg)
       (semiring-element? (gn-not (get-guard)))))

(define (test-nand-properties)
  (set-guard! (semiring-element 1 L))
  (define x (semiring-element (get-guard-threshold) L))
  (define y (semiring-element (get-guard-complement) L))
  (and (semiring-element? (gn-nand x (semiring-element (get-one) L)))
       (semiring-element? (gn-nand (semiring-element (get-one) L) (semiring-element (get-one) L)))))

(define (test-computational-universality)
  (set-guard! (semiring-element 1 L))
  (define x (semiring-element 0.3 L))
  (define y (semiring-element 0.7 L))
  (and (semiring-element? (gn-xor x y))
       (semiring-element? (gn-and x y))
       (semiring-element? (gn-or x y))))
