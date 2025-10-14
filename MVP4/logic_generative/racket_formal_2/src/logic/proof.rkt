#lang racket
;; Proof objects and pretty-printing for L-level witnesses

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./internalize.rkt")
         (file "./guarded-negation.rkt")
         (file "./kernel-checker.rkt"))

(provide (all-defined-out))

;; A proof pairs a boolean formula (abstract expr) with an L-level witness
(struct proof (formula witness) #:transparent)

(define (make-proof boolean-expr)
  (proof boolean-expr (internalize-boolean boolean-expr)))

;; Build a kernel step-proof for simple shapes (currently reflexivity only)
(struct kproof (formula steps) #:transparent)

(define (make-kernel-proof boolean-expr)
  (cond
    [(and (abstract-op? boolean-expr)
          (eq? (abstract-op-operator boolean-expr) 'implies))
     (define a (first (abstract-op-operands boolean-expr)))
     (define b (second (abstract-op-operands boolean-expr)))
     (if (abstract-expr-equal? a b)
         (kproof boolean-expr (prove-reflexivity a))
         (kproof boolean-expr '()))]
    [else (kproof boolean-expr '())]))

(define (check-kernel-proof kp)
  (kernel-check (kproof-steps kp) (kproof-formula kp)))

;; Boolean formula simplifier (lightweight)
;; Helpers for constant folding and structural checks
(define (bool-const? e)
  (and (abstract-const? e) (eq? (abstract-const-type e) 'boolean)))
(define (bool-true? e) (and (bool-const? e) (abstract-const-value e)))
(define (bool-false? e) (and (bool-const? e) (not (abstract-const-value e))))

(define (simplify-boolean expr)
  (cond
    [(abstract-op? expr)
     (define op (abstract-op-operator expr))
     (define raw-args (abstract-op-operands expr))
     (define args (map simplify-boolean raw-args))
     (case op
       [(not)
        (define x (first args))
        (cond
          ;; double negation
          [(and (abstract-op? x) (eq? (abstract-op-operator x) 'not))
           (second (abstract-op-operands x))]
          ;; De Morgan
          [(and (abstract-op? x) (eq? (abstract-op-operator x) 'and))
           (abstract-op 'or (map (λ (a) (abstract-op 'not (list a) 'boolean)) (abstract-op-operands x)) 'boolean)]
          [(and (abstract-op? x) (eq? (abstract-op-operator x) 'or))
           (abstract-op 'and (map (λ (a) (abstract-op 'not (list a) 'boolean)) (abstract-op-operands x)) 'boolean)]
          ;; constant folding
          [(bool-true? x) (make-abstract-const #f 'boolean)]
          [(bool-false? x) (make-abstract-const #t 'boolean)]
          [else (abstract-op 'not (list x) 'boolean)])]
       [(implies)
        (define a (first args))
        (define b (second args))
        (simplify-boolean (abstract-op 'or (list (abstract-op 'not (list a) 'boolean) b) 'boolean))]
       [(equiv iff)
        (define a (first args))
        (define b (second args))
        (simplify-boolean (abstract-op 'and (list (abstract-op 'implies (list a b) 'boolean)
                                                  (abstract-op 'implies (list b a) 'boolean)) 'boolean))]
       [(and)
        (define a (first args))
        (define b (second args))
        (define (is-or-with a b)
          (and (abstract-op? b)
               (eq? (abstract-op-operator b) 'or)
               (let ([x (first (abstract-op-operands b))]
                     [y (second (abstract-op-operands b))])
                 (or (abstract-expr-equal? a x)
                     (abstract-expr-equal? a y)))))
        (cond
          ;; constants
          [(or (bool-false? a) (bool-false? b)) (make-abstract-const #f 'boolean)]
          [(bool-true? a) b]
          [(bool-true? b) a]
          ;; idempotence
          [(abstract-expr-equal? a b) a]
          ;; absorption: a ∧ (a ∨ b) = a; (a ∨ b) ∧ a = a
          [(is-or-with a b) a]
          [(is-or-with b a) b]
          [else (abstract-op 'and (list a b) 'boolean)])]
       [(or)
        (define a (first args))
        (define b (second args))
        (define (is-and-with a b)
          (and (abstract-op? b)
               (eq? (abstract-op-operator b) 'and)
               (let ([x (first (abstract-op-operands b))]
                     [y (second (abstract-op-operands b))])
                 (or (abstract-expr-equal? a x)
                     (abstract-expr-equal? a y)))))
        (cond
          ;; constants
          [(or (bool-true? a) (bool-true? b)) (make-abstract-const #t 'boolean)]
          [(bool-false? a) b]
          [(bool-false? b) a]
          ;; idempotence
          [(abstract-expr-equal? a b) a]
          ;; absorption: a ∨ (a ∧ b) = a; (a ∧ b) ∨ a = a
          [(is-and-with a b) a]
          [(is-and-with b a) b]
          [else (abstract-op 'or (list a b) 'boolean)])]
       [else (abstract-op op args (abstract-op-type expr))])]
    [else expr]))

;; Pretty-printer for formulas
(define (pp-expr expr)
  (cond
    [(abstract-op? expr)
     (define op (abstract-op-operator expr))
     (define args (abstract-op-operands expr))
     (case op
       [(not) (string-append "¬(" (pp-expr (first args)) ")")]
       [(and) (format "(~a ∧ ~a)" (pp-expr (first args)) (pp-expr (second args)))]
       [(or)  (format "(~a ∨ ~a)" (pp-expr (first args)) (pp-expr (second args)))]
       [(implies) (format "(~a ⇒ ~a)" (pp-expr (first args)) (pp-expr (second args)))]
       [(equiv iff) (format "(~a ⇔ ~a)" (pp-expr (first args)) (pp-expr (second args)))]
       [(Prov) (format "Prov(~a)" (pp-expr (first args)))]
       [(Consistent) "Consistent"]
       [(Property) (format "P[~a]" (pp-expr (first args)))]
       [(Holds) (format "Holds(~a, ~a)" (pp-expr (first args)) (pp-expr (second args)))]
       [(Decides) (format "Decides(~a, ~a)" (pp-expr (first args)) (pp-expr (second args)))]
       [(Nontrivial) (format "Nontrivial(~a)" (pp-expr (first args)))]
       [(Extensional) (format "Extensional(~a)" (pp-expr (first args)))]
       [(Undecidable) (format "Undecidable(~a)" (pp-expr (first args)))]
       [(ReducesToHalting) (format "ReducesToHalting(~a)" (pp-expr (first args)))]
       [(prop) (pp-expr (first args))]
       [else (~a expr)])]
    [(abstract-const? expr) (~a (abstract-const-value expr))]
    [else (~a expr)]))

(define (proof->string p)
  (pp-expr (simplify-boolean (proof-formula p))))

(define (show-proof p)
  (displayln (proof->string p))
  p)
