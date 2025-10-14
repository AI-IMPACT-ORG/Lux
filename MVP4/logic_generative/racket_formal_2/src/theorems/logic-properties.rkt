#lang racket
; (c) 2025 AI.IMPACT GmbH

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/guarded-negation.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/proof.rkt"))

(provide (all-defined-out))

(define (prop-implies-trans)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define R (embed-proposition (make-abstract-const 'R 'symbol)))
  (rule-imp-trans '() P Q R))

(define (prop-imp-ante-strengthen)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define R (embed-proposition (make-abstract-const 'R 'symbol)))
  (rule-imp-ante-strengthen '() P R Q))

(define (prop-cut)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (rule-cut '() P Q))

(define (prop-imp-distribute-right)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define R (embed-proposition (make-abstract-const 'R 'symbol)))
  ;; ⊢ ((P⇒Q) ∧ (P⇒R)) ⇒ (P⇒(Q ∧ R))
  (rule-imp-conj '() P Q R))

(define (prop-reflect-L-B)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define s (sequent '() P))
  (abstract-semiring-equal? (ν_L (ι_L s)) s))

(define (prop-context-normalization)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define ctx (list P Q P))
  (define s1 (sequent ctx P))
  (define s2 (sequent (ctx-normalize ctx) P))
  (equal-L? s1 s2))

;; Guarded monotonicity of implication: ⊢ (P⇒Q) ⇒ ((G⇒P) ⇒ (G⇒Q))
(define (prop-guarded-imp-monotone)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define G (embed-proposition (make-abstract-const 'G 'symbol)))
  (rule-imp-monotone-guarded '() G P Q))
