#lang racket

;; Kernel-level step proofs for ∧/∨ via axiom instances

(require (file "../src/foundations/abstract-core.rkt")
         (file "../src/logic/kernel-checker.rkt"))

(provide run-kernel-step-proofs)

(define (ensure b msg)
  (unless b (error 'kernel-step-proofs msg)))

(define (run-kernel-step-proofs)
  (displayln "=== kernel step proofs (axiom instances) ===")
  (define P (abstract-op 'var (list (make-abstract-const 'P 'symbol)) 'boolean))
  (define Q (abstract-op 'var (list (make-abstract-const 'Q 'symbol)) 'boolean))
  ;; ∧-intro: P ⇒ (Q ⇒ (P ∧ Q))
  (let* ([goal (abstract-op 'implies (list P (abstract-op 'implies (list Q (abstract-op 'and (list P Q) 'boolean)) 'boolean)) 'boolean)]
         [steps (prove-and-intro P Q)])
    (ensure (kernel-check steps goal) "kernel and-intro"))
  ;; ∧-elim left: (P ∧ Q) ⇒ P
  (let* ([goal (abstract-op 'implies (list (abstract-op 'and (list P Q) 'boolean) P) 'boolean)]
         [steps (prove-and-elim-left P Q)])
    (ensure (kernel-check steps goal) "kernel and-elim-left"))
  ;; ∨-intro left: P ⇒ (P ∨ Q)
  (let* ([goal (abstract-op 'implies (list P (abstract-op 'or (list P Q) 'boolean)) 'boolean)]
         [steps (prove-or-intro-left P Q)])
    (ensure (kernel-check steps goal) "kernel or-intro-left"))
  (displayln "=== kernel step proofs: all checks passed ===")
  #t)
