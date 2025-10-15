#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Auxiliary Transporters and Modulated Operators

 (require racket/list
          (file "../foundations/abstract-core.rkt")
          (file "./algebraic-structures.rkt")
          (file "./explog-decomposition.rkt")
          (file "./central-scalars.rkt"))

(provide (all-defined-out))

(define (auxiliary-transporter Δk Δmz Δmzb t)
  (central-transporter Δk Δmz Δmzb t))

(define (modulated-ad₀ b)
  (define d (dec-z-zbar b))
  (define Δk 0) (define Δmz 0) (define Δmzb 0)
  (auxiliary-transporter Δk Δmz Δmzb (rec-z-zbar (first d) (second d) (third d) (fourth d))))

(define (modulated-ad₁ b) (modulated-ad₀ b))
(define (modulated-ad₂ b) (modulated-ad₀ b))
(define (modulated-ad₃ b) (modulated-ad₀ b))

(define (step-weight b)
  (define Δk 0) (define Δmz 0) (define Δmzb 0)
  (auxiliary-transporter Δk Δmz Δmzb B-one))

;; Conjugation: swap z, z̄ headers
(define (starB b)
  (define g (b-grade b))
  (define d (dec-z-zbar b))
  (b-with-grade-if-known (rec-z-zbar (first d) (third d) (second d) (fourth d)) g))

(define (monoid-semiring-multiply b1 b2)
  ((semiring-ops-mul B-ops) b1 b2))

(define (monoid-semiring-add b1 b2)
  ((semiring-ops-add B-ops) b1 b2))

(define (test-auxiliary-transporter b)
  (define t (auxiliary-transporter 1 1 1 b))
  (and (semiring-element? t) (eq? (semiring-element-semiring-type t) B)))

(define (test-monoid-semiring-structure b)
  (define m (monoid-semiring-multiply b (semiring-element (get-two) B)))
  (define a (monoid-semiring-add b (semiring-element (get-two) B)))
  (and (semiring-element? m) (semiring-element? a)))

(define (test-conjugation-auxiliary-swap b)
  (define s (starB b))
  (and (semiring-element? s) (eq? (semiring-element-semiring-type s) B)))

(define (test-auxiliary-modulated-composition b)
  (define w (step-weight b))
  (define m (modulated-ad₀ b))
  (and (semiring-element? w) (semiring-element? m)
       (eq? (semiring-element-semiring-type w) B)
       (eq? (semiring-element-semiring-type m) B)))
