#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Tiny Hilbert-style kernel: axioms + modus ponens + substitution

(require (file "../foundations/abstract-core.rkt"))

(provide (all-defined-out))

;; Boolean constructors (symbolic layer)
(define (b-implies a b) (abstract-op 'implies (list a b) 'boolean))
(define (b-not a)       (abstract-op 'not (list a) 'boolean))
(define (b-and a b)     (abstract-op 'and (list a b) 'boolean))
(define (b-or a b)      (abstract-op 'or (list a b) 'boolean))

;; Variables as abstract ops: (var 'P)
(define (b-var sym) (abstract-op 'var (list (make-abstract-const sym 'symbol)) 'boolean))
(define (b-var? e)
  (and (abstract-op? e)
       (eq? (abstract-op-operator e) 'var)))
(define (b-var-name e) (abstract-const-value (first (abstract-op-operands e))))

;; Substitution: map symbols → boolean expressions
(define (subst expr env)
  (cond
    [(b-var? expr)
     (hash-ref env (b-var-name expr) expr)]
    [(abstract-op? expr)
     (abstract-op (abstract-op-operator expr)
                  (map (λ (x) (subst x env)) (abstract-op-operands expr))
                  (abstract-op-type expr))]
    [else expr]))

;; Axiom schemas (Hilbert):
;; A1: P ⇒ (Q ⇒ P)
(define (axiom-A1) (b-implies (b-var 'P) (b-implies (b-var 'Q) (b-var 'P))))
;; A2: (P ⇒ (Q ⇒ R)) ⇒ ((P ⇒ Q) ⇒ (P ⇒ R))
(define (axiom-A2)
  (b-implies (b-implies (b-var 'P) (b-implies (b-var 'Q) (b-var 'R)))
             (b-implies (b-implies (b-var 'P) (b-var 'Q))
                        (b-implies (b-var 'P) (b-var 'R)))))

;; Additional axiom templates for ∧/∨ intro/elim (kernel-friendly)
(define (axiom-AND-I)
  (b-implies (b-var 'P) (b-implies (b-var 'Q) (b-and (b-var 'P) (b-var 'Q)))))
(define (axiom-AND-EL)
  (b-implies (b-and (b-var 'P) (b-var 'Q)) (b-var 'P)))
(define (axiom-AND-ER)
  (b-implies (b-and (b-var 'P) (b-var 'Q)) (b-var 'Q)))
(define (axiom-OR-IL)
  (b-implies (b-var 'P) (b-or (b-var 'P) (b-var 'Q))))
(define (axiom-OR-IR)
  (b-implies (b-var 'Q) (b-or (b-var 'P) (b-var 'Q))))

;; Steps
(struct ax-step (schema env formula) #:transparent)  ; axiom instance via substitution
(struct mp-step (i j formula) #:transparent)         ; MP from step i: φ and step j: (φ⇒ψ) yields ψ

;; Kernel checker
(define (kernel-check steps conclusion)
  (define table (make-hash))
  (for ([st (in-indexed steps)])
    (define idx (add1 (car st)))
    (define s (cdr st))
    (cond
      [(ax-step? s)
       (define schema (ax-step-schema s))
       (define inst (subst (case schema
                             [(A1) (axiom-A1)]
                             [(A2) (axiom-A2)]
                             [(AND-I) (axiom-AND-I)]
                             [(AND-EL) (axiom-AND-EL)]
                             [(AND-ER) (axiom-AND-ER)]
                             [(OR-IL) (axiom-OR-IL)]
                             [(OR-IR) (axiom-OR-IR)]
                             [else (axiom-A1)])
                           (ax-step-env s)))
       (unless (abstract-expr-equal? inst (ax-step-formula s))
         (error 'kernel-check (format "axiom instance mismatch at ~a" idx)))
       (hash-set! table idx (ax-step-formula s))]
      [(mp-step? s)
       (define φ (hash-ref table (mp-step-i s) #f))
       (define φ⇒ψ (hash-ref table (mp-step-j s) #f))
       (unless (and φ φ⇒ψ (abstract-op? φ⇒ψ) (eq? (abstract-op-operator φ⇒ψ) 'implies))
         (error 'kernel-check (format "MP prerequisites missing at ~a" idx)))
       (define ante (first (abstract-op-operands φ⇒ψ)))
       (define cons (second (abstract-op-operands φ⇒ψ)))
       (unless (abstract-expr-equal? φ ante)
         (error 'kernel-check (format "MP antecedent mismatch at ~a" idx)))
       (unless (abstract-expr-equal? cons (mp-step-formula s))
         (error 'kernel-check (format "MP conclusion mismatch at ~a" idx)))
       (hash-set! table idx (mp-step-formula s))]
      [else (error 'kernel-check (format "unknown step at ~a" idx))]))
  (define last (hash-ref table (length steps) #f))
  (and last (abstract-expr-equal? last conclusion)))

;; A small derived proof: reflexivity (P ⇒ P)
(define (prove-reflexivity φ)
  ;; Steps per standard derivation:
  ;; 1. A1: P ⇒ (Q ⇒ P)
  ;; 2. A1: P ⇒ ((P ⇒ Q) ⇒ P)
  ;; 3. A2: (P ⇒ ((P ⇒ Q) ⇒ P)) ⇒ ((P ⇒ (P ⇒ Q)) ⇒ (P ⇒ P))
  ;; 4. A1: P ⇒ (P ⇒ Q)
  ;; 5. MP(2,3): (P ⇒ (P ⇒ Q)) ⇒ (P ⇒ P)
  ;; 6. MP(4,5): P ⇒ P
  (define env1 (hash 'P φ 'Q (b-var 'Q)))
  (define env2 (hash 'P φ 'Q (b-implies φ (b-var 'Q))))
  (define env3 (hash 'P φ 'Q (b-var 'Q) 'R φ))
  (define env4 (hash 'P φ 'Q (b-var 'Q)))
  (list
   (ax-step 'A1 env1 (subst (axiom-A1) env1))
   (ax-step 'A1 env2 (subst (axiom-A1) env2))
   (ax-step 'A2 env3 (subst (axiom-A2) env3))
   (ax-step 'A1 env4 (subst (axiom-A1) env4))
   (mp-step 2 3 (b-implies (b-implies φ (b-var 'Q)) (b-implies φ φ)))
   (mp-step 4 5 (b-implies φ φ))))

;; Straightforward kernel realizations via axiom instances
(define (prove-and-intro φ ψ)
  (define env (hash 'P φ 'Q ψ))
  (list (ax-step 'AND-I env (subst (axiom-AND-I) env))))

(define (prove-and-elim-left φ ψ)
  (define env (hash 'P φ 'Q ψ))
  (list (ax-step 'AND-EL env (subst (axiom-AND-EL) env))))

(define (prove-and-elim-right φ ψ)
  (define env (hash 'P φ 'Q ψ))
  (list (ax-step 'AND-ER env (subst (axiom-AND-ER) env))))

(define (prove-or-intro-left φ ψ)
  (define env (hash 'P φ 'Q ψ))
  (list (ax-step 'OR-IL env (subst (axiom-OR-IL) env))))

(define (prove-or-intro-right φ ψ)
  (define env (hash 'P φ 'Q ψ))
  (list (ax-step 'OR-IR env (subst (axiom-OR-IR) env))))
