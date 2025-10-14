#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Central rule catalog: single source of truth from axioms → rules → checkers

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./guarded-negation.rkt")
         (file "./internalize.rkt")
         (file "./inference.rkt")
         (prefix-in q: (file "./quantifiers.rkt")))

(provide (all-defined-out))

;; A mapping from rule-symbol → function that takes (list args) and returns an L-witness
;; Each rule function in inference.rkt has the shape (ctx φ ψ ...) → L-witness,
;; so we can apply directly via (apply f args).

(define rule-table
  (hash
   'mp                 (λ (args) (apply rule-mp args))
   'contraction        (λ (args) (apply rule-contraction args))
   'exchange           (λ (args) (apply rule-exchange args))
   'and-intro          (λ (args) (apply rule-and-intro args))
   'and-elim-left      (λ (args) (apply rule-and-elim-left args))
   'and-elim-right     (λ (args) (apply rule-and-elim-right args))
   'or-intro-left      (λ (args) (apply rule-or-intro-left args))
   'or-intro-right     (λ (args) (apply rule-or-intro-right args))
   'imp-intro          (λ (args) (apply rule-imp-intro args))
   'weakening          (λ (args) (apply rule-weakening args))
   'cut                (λ (args) (apply rule-cut args))
   'imp-trans          (λ (args) (apply rule-imp-trans args))
   'imp-ante-strengthen (λ (args) (apply rule-imp-ante-strengthen args))
   'imp-conj           (λ (args) (apply rule-imp-conj args))
   'imp-monotone-guarded (λ (args) (apply rule-imp-monotone-guarded args))
   ;; Quantifier rules (symbolic guard side-conditions)
   'forall-intro       (λ (args) (apply q:rule-forall-intro args))
   'forall-elim        (λ (args) (apply q:rule-forall-elim args))
   'exists-intro       (λ (args) (apply q:rule-exists-intro args))
   'exists-elim        (λ (args) (apply q:rule-exists-elim args))))

(define (rule-names)
  (hash-keys rule-table))

(define (rule->witness name args)
  (define f (hash-ref rule-table name #f))
  (if f
      (f args)
      (semiring-element (abstract-op 'unknown '() 'boolean) L)))
