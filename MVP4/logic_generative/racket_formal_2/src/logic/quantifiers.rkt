#lang racket
;; Guarded quantifiers (symbolic) and internal sequent-style rules

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./guarded-negation.rkt")
         (file "./internalize.rkt"))

(provide (all-defined-out))

;; Boolean constructors for quantifiers (remain symbolic at the boolean layer)
(define (b-forall var pred) (abstract-op 'forall (list var pred) 'boolean))
(define (b-exists var pred) (abstract-op 'exists (list var pred) 'boolean))

;; Variables and propositional embedding
(define (b-var sym) (abstract-op 'var (list (make-abstract-const sym 'symbol)) 'boolean))
(define (asL e) (embed-proposition e))

;; Guard wf predicate (symbolic at boolean layer), internalized to L
(define (guard-wf G)
  (asL (abstract-op 'GuardWF (list G) 'boolean)))

;; Sequent encoding: Γ ⊢ φ as (∧Γ) ⇒ φ
(define (conjL xs) (foldl gn-and (semiring-element (get-one) L) xs))
(define (sequent ctx phi) (gn-implies (conjL ctx) phi))

;; Freshness: compute symbol-freeness of var in boolean expressions underlying Γ
;; Extract underlying boolean from an L-embedded proposition, when possible
(define (L->bool e)
  (cond
    [(and (semiring-element? e)
          (eq? (semiring-element-semiring-type e) L))
     (define v (semiring-element-value e))
     (if (and (abstract-op? v) (eq? (abstract-op-operator v) 'prop))
         (first (abstract-op-operands v))
         v)]
    [else e]))

(define (occurs? var-expr expr)
  (cond
    [(equal? var-expr expr) #t]
    [(abstract-op? expr) (ormap (λ (x) (occurs? var-expr x)) (abstract-op-operands expr))]
    [else #f]))

(define (fresh? var ctx)
  (not (ormap (λ (e) (occurs? var (L->bool e))) ctx)))

(define (L-fresh var ctx)
  (if (fresh? var ctx) (semiring-element (get-one) L) (semiring-element (get-zero) L)))

(define (rule-forall-intro ctx var phi)
  ;; freshness side-condition computed + internalized
  (define Γφ (sequent ctx (asL (abstract-op 'holds (list var phi) 'boolean))))
  (gn-implies (gn-and (L-fresh var ctx) Γφ)
              (sequent ctx (asL (b-forall var phi)))))

;; ∀-elimination: from Γ ⊢ ∀x φ(x) derive Γ ⊢ φ(t)
(define (rule-forall-elim ctx var phi term)
  (define Γ∀ (sequent ctx (asL (b-forall var phi))))
  (gn-implies Γ∀ (sequent ctx (asL (abstract-op 'holds (list term phi) 'boolean)))))

;; ∃-introduction: from Γ ⊢ φ(t) derive Γ ⊢ ∃x φ(x)
(define (rule-exists-intro ctx var phi term)
  (define Γφt (sequent ctx (asL (abstract-op 'holds (list term phi) 'boolean))))
  (gn-implies Γφt (sequent ctx (asL (b-exists var phi)))))

;; ∃-elimination (schema): (Γ ⊢ ∃x φ(x)) ∧ (Γ,φ(x) ⊢ ψ) ⇒ (Γ ⊢ ψ)
(define (rule-exists-elim ctx var phi psi)
  (define Γ∃ (sequent ctx (asL (b-exists var phi))))
  (define Γφ→ψ (sequent (cons (asL (abstract-op 'holds (list var phi) 'boolean)) ctx) psi))
  (gn-implies (gn-and Γ∃ Γφ→ψ)
              (sequent ctx psi)))
