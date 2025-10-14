#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Internal inference rules (sequent-style) encoded inside Lux (L-level)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./guarded-negation.rkt")
         (file "./internalize.rkt"))

(provide (all-defined-out))

;; Contexts and sequents
(define (conjL xs)
  (foldl gn-and (L-true) xs))

(define (sequent ctx phi)
  ;; Γ ⊢ φ is represented as (∧Γ) ⇒ φ, with canonicalized context
  (gn-implies (conjL (ctx-normalize ctx)) phi))

;; Context normalization and structural rules
(define (equal-L? a b)
  (and (semiring-element? a) (semiring-element? b)
       (eq? (semiring-element-semiring-type a) L)
       (eq? (semiring-element-semiring-type b) L)
       (abstract-expr-equal? (semiring-element-value a)
                             (semiring-element-value b))))

(define (ctx-normalize ctx)
  (define out '())
  (for ([e ctx])
    (unless (ormap (λ (x) (equal-L? x e)) out)
      (set! out (append out (list e)))))
  out)

;; Contraction: from Γ,φ,φ ⊢ ψ derive Γ,φ ⊢ ψ (as an implication of sequents)
(define (rule-contraction ctx φ ψ)
  (define Γφφ→ψ (sequent (list* φ φ ctx) ψ))
  (gn-implies Γφφ→ψ (sequent (cons φ ctx) ψ)))

;; Exchange: Γ,φ,ψ,Δ ⊢ χ implies Γ,ψ,φ,Δ ⊢ χ (encoded as equivalence of sequents)
(define (rule-exchange ctx-left φ ψ ctx-right χ)
  (define seq1 (sequent (append ctx-left (list φ ψ) ctx-right) χ))
  (define seq2 (sequent (append ctx-left (list ψ φ) ctx-right) χ))
  (gn-iff seq1 seq2))

;; Tactics: small composition helper (MP twice)
(define (tactic-mp2 ctx φ ψ χ)
  ;; From Γ⊢φ, Γ⊢(φ⇒ψ), Γ⊢(ψ⇒χ) derive Γ⊢χ
  (define Γφ (sequent ctx φ))
  (define Γφ⇒ψ (sequent ctx (gn-implies φ ψ)))
  (define Γψ⇒χ (sequent ctx (gn-implies ψ χ)))
  (define step1 (rule-mp ctx φ ψ))
  (define step2 (rule-mp ctx ψ χ))
  ;; Combine witnesses: (Γφ ∧ Γφ⇒ψ) ⇒ Γψ and (Γψ ∧ Γψ⇒χ) ⇒ Γχ
  ;; Return a composed implication (Γφ ∧ Γφ⇒ψ ∧ Γψ⇒χ) ⇒ Γχ
  (gn-implies (gn-and Γφ (gn-and Γφ⇒ψ Γψ⇒χ))
              (sequent ctx χ)))

;; Cut-like admissibility: (Γ⊢φ ∧ Γ,φ⊢ψ) ⇒ Γ⊢ψ
(define (rule-cut ctx φ ψ)
  (define Γφ (sequent ctx φ))
  (define Γφ→ψ (sequent (cons φ ctx) ψ))
  (gn-implies (gn-and Γφ Γφ→ψ)
              (sequent ctx ψ)))

;; Implication transitivity: (Γ⊢(φ⇒ψ) ∧ Γ⊢(ψ⇒χ)) ⇒ Γ⊢(φ⇒χ)
(define (rule-imp-trans ctx φ ψ χ)
  (define Γφ⇒ψ (sequent ctx (gn-implies φ ψ)))
  (define Γψ⇒χ (sequent ctx (gn-implies ψ χ)))
  (gn-implies (gn-and Γφ⇒ψ Γψ⇒χ)
              (sequent ctx (gn-implies φ χ))))

;; Strengthen antecedent: Γ⊢(φ⇒ψ) ⇒ Γ⊢((φ∧ρ)⇒ψ)
(define (rule-imp-ante-strengthen ctx φ ρ ψ)
  (define Γφ⇒ψ (sequent ctx (gn-implies φ ψ)))
  (define lemma (sequent ctx (gn-implies (gn-and φ ρ) φ)))
  ;; From Γ, get (φ∧ρ)⇒φ by ∧-elim-left; combine with φ⇒ψ to get (φ∧ρ)⇒ψ
  (gn-implies Γφ⇒ψ (sequent ctx (gn-implies (gn-and φ ρ) ψ))))

;; From Γ⊢(φ⇒ψ) and Γ⊢(φ⇒ρ) derive Γ⊢(φ⇒(ψ∧ρ))
(define (rule-imp-conj ctx φ ψ ρ)
  (define Γφ⇒ψ (sequent ctx (gn-implies φ ψ)))
  (define Γφ⇒ρ (sequent ctx (gn-implies φ ρ)))
  (gn-implies (gn-and Γφ⇒ψ Γφ⇒ρ)
              (sequent ctx (gn-implies φ (gn-and ψ ρ)))))

;; Guarded monotonicity of implication:
;; From Γ ⊢ (φ⇒ψ), derive Γ ⊢ ((G⇒φ) ⇒ (G⇒ψ)) for any guard G
(define (rule-imp-monotone-guarded ctx G φ ψ)
  (define Γφ⇒ψ (sequent ctx (gn-implies φ ψ)))
  (define target (sequent ctx (gn-implies (gn-implies G φ)
                                          (gn-implies G ψ))))
  (gn-implies Γφ⇒ψ target))


;; Standard rules as internal theorems (L-level)

;; Modus Ponens: from Γ⊢φ and Γ⊢(φ⇒ψ) derive Γ⊢ψ, encoded as a single implication
(define (rule-mp ctx φ ψ)
  (define Γφ (sequent ctx φ))
  (define Γφ→ψ (sequent ctx (gn-implies φ ψ)))
  (gn-implies (gn-and Γφ Γφ→ψ)
              (sequent ctx ψ)))

;; ∧-introduction: from Γ⊢φ and Γ⊢ψ derive Γ⊢(φ∧ψ)
(define (rule-and-intro ctx φ ψ)
  (define Γφ (sequent ctx φ))
  (define Γψ (sequent ctx ψ))
  (gn-implies (gn-and Γφ Γψ)
              (sequent ctx (gn-and φ ψ))))

;; ∧-elimination (left/right)
(define (rule-and-elim-left ctx φ ψ)
  (define Γφ∧ψ (sequent ctx (gn-and φ ψ)))
  (gn-implies Γφ∧ψ (sequent ctx φ)))

(define (rule-and-elim-right ctx φ ψ)
  (define Γφ∧ψ (sequent ctx (gn-and φ ψ)))
  (gn-implies Γφ∧ψ (sequent ctx ψ)))

;; ∨-introduction (left/right)
(define (rule-or-intro-left ctx φ ψ)
  (define Γφ (sequent ctx φ))
  (gn-implies Γφ (sequent ctx (gn-or φ ψ))))

(define (rule-or-intro-right ctx φ ψ)
  (define Γψ (sequent ctx ψ))
  (gn-implies Γψ (sequent ctx (gn-or φ ψ))))

;; ⇒-introduction: from Γ,φ ⊢ ψ derive Γ ⊢ (φ⇒ψ)
(define (rule-imp-intro ctx φ ψ)
  (define Γ∧φ→ψ (sequent (cons φ ctx) ψ))
  (gn-implies Γ∧φ→ψ (sequent ctx (gn-implies φ ψ))))

;; Structural rules
(define (rule-weakening ctx φ ψ)
  ;; From Γ ⊢ φ derive Γ,ψ ⊢ φ
  (define Γφ (sequent ctx φ))
  (gn-implies Γφ (sequent (cons ψ ctx) φ)))

;; Basic sample pack on empty context
(define (inference-basics)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define Γ '())
  (list (cons 'mp (rule-mp Γ P Q))
        (cons 'and-intro (rule-and-intro Γ P Q))
        (cons 'and-elim-left (rule-and-elim-left Γ P Q))
        (cons 'and-elim-right (rule-and-elim-right Γ P Q))
        (cons 'or-intro-left (rule-or-intro-left Γ P Q))
        (cons 'or-intro-right (rule-or-intro-right Γ P Q))
        (cons 'imp-intro (rule-imp-intro Γ P Q))
        (cons 'weakening (rule-weakening Γ P Q))))
