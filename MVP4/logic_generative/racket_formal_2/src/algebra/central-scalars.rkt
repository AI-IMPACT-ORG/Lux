#lang racket
;; Central Scalars (φ, z, z̄, Λ)

(require (file "../foundations/abstract-core.rkt")
         (file "./algebraic-structures.rkt"))

(provide (all-defined-out))

(struct central-scalar-system (φ z z̄ Λ) #:transparent)

(define default-central-scalars
  (central-scalar-system (get-two) (get-three) (get-five) (get-fifteen)))

(define symbolic-central-scalars
  (central-scalar-system (make-abstract-symbol 'φ)
                         (make-abstract-symbol 'z)
                         (make-abstract-symbol 'z̄)
                         (make-abstract-symbol 'Λ)))

;; Use symbolic central scalars by default to avoid numeric codings.
(define *current-central-scalars* symbolic-central-scalars)
(define (set-central-scalar-system! s) (set! *current-central-scalars* s))
(define (get-current-central-scalars) *current-central-scalars*)

(define (get-φ) (central-scalar-system-φ *current-central-scalars*))
(define (get-z) (central-scalar-system-z *current-central-scalars*))
(define (get-z̄) (central-scalar-system-z̄ *current-central-scalars*))
(define (get-Λ) (central-scalar-system-Λ *current-central-scalars*))

(define φ (semiring-element (get-φ) B))
(define z (semiring-element (get-z) B))
(define z̄ (semiring-element (get-z̄) B))
(define Λ (semiring-element (get-Λ) B))

(define (central-transporter Δk Δmz Δmzb t)
  (define v (semiring-element-value t))
  (semiring-element
   (abstract-mul (abstract-mul (abstract-expt (get-φ) Δk)
                               (abstract-expt (get-z) Δmz))
                 (abstract-mul (abstract-expt (get-z̄) Δmzb) v))
   B))

(define (gauge-transform t Δk Δmz Δmzb)
  (central-transporter Δk Δmz Δmzb t))
