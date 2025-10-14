#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Abstract Core Foundations (self-contained, Lux)
;;
;; This module provides a minimal abstract-expression layer used across the
;; project. It intentionally keeps multiple truth systems first-class by:
;; - representing boolean/meta propositions as abstract expressions
;; - separating numeric carriers from logical/proof-level structures
;; - avoiding evaluation unless explicitly requested (abstract-eval-*)

(provide (all-defined-out))

;; Abstract expression datatypes
(struct abstract-const (value type) #:transparent)
(struct abstract-op    (operator operands type) #:transparent)

;; Constructors
(define (make-abstract-const v t) (abstract-const v t))
(define (make-abstract-symbol s) (abstract-const s 'symbol))
(define (abstract-expr op args type) (abstract-op op (if (list? args) args (list args)) type))

;; Note: We intentionally do not encode naturals; use abstract symbols instead.

;; General abstract expression predicate
(define (abstract-expr? x) (or (abstract-const? x) (abstract-op? x)))

;; Predicates/accessors (struct predicates are auto-provided)
(define (abstract-expr-equal? a b)
  (cond
    [(and (number? a) (number? b)) (equal? a b)]
    [(and (abstract-const? a) (number? b)) (equal? (abstract-const-value a) b)]
    [(and (number? a) (abstract-const? b)) (equal? a (abstract-const-value b))]
    [(and (abstract-const? a) (abstract-const? b))
     (and (eq? (abstract-const-type a) (abstract-const-type b))
          (equal? (abstract-const-value a) (abstract-const-value b)))]
    [(and (abstract-op? a) (abstract-op? b))
     (and (eq? (abstract-op-operator a) (abstract-op-operator b))
          (eq? (abstract-op-type a) (abstract-op-type b))
          (= (length (abstract-op-operands a)) (length (abstract-op-operands b)))
          (for/and ([x (in-list (abstract-op-operands a))]
                    [y (in-list (abstract-op-operands b))])
            (abstract-expr-equal? x y)))]
    [else (equal? a b)]))

;; Type helpers
(define (numeric-const? x)
  (and (abstract-const? x)
       (or (eq? (abstract-const-type x) 'integer)
           (eq? (abstract-const-type x) 'real))))

(define (ac-bool-const? x)
  (and (abstract-const? x) (eq? (abstract-const-type x) 'boolean)))

(define (to-number x)
  (cond
    [(number? x) x]
    [(numeric-const? x) (abstract-const-value x)]
    [else #f]))

(define (promote-type a b)
  (define ta (and (abstract-const? a) (abstract-const-type a)))
  (define tb (and (abstract-const? b) (abstract-const-type b)))
  (cond
    [(or (eq? ta 'real) (eq? tb 'real)) 'real]
    [else 'integer]))

;; Numeric primitives (symbolic where needed)
(define (abstract-add a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb)
      (make-abstract-const (+ xa xb) (promote-type a b))
      (abstract-op 'add (list a b) (promote-type a b))))

(define (abstract-sub a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb)
      (make-abstract-const (- xa xb) (promote-type a b))
      (abstract-op 'sub (list a b) (promote-type a b))))

(define (abstract-mul a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb)
      (make-abstract-const (* xa xb) (promote-type a b))
      (abstract-op 'mul (list a b) (promote-type a b))))

(define (abstract-div a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb (not (zero? xb)))
      (make-abstract-const (/ xa xb) 'real)
      (abstract-op 'div (list a b) 'real)))

(define (abstract-expt a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb)
      (make-abstract-const (expt xa xb) (if (and (integer? xa) (integer? xb)) 'integer 'real))
      (abstract-op 'expt (list a b) 'real)))

(define (abstract-floor a)
  (define xa (to-number a))
  (if xa (make-abstract-const (floor xa) 'integer) (abstract-op 'floor (list a) 'integer)))

(define (abstract-abs a)
  (define xa (to-number a))
  (if xa (make-abstract-const (abs xa) (if (integer? xa) 'integer 'real)) (abstract-op 'abs (list a) 'real)))

(define (abstract-log a)
  (define xa (to-number a))
  (if (and xa (> xa 0))
      (make-abstract-const (log xa) 'real)
      (abstract-op 'log (list a) 'real)))

(define (abstract-sin a)
  (define xa (to-number a))
  (if xa (make-abstract-const (sin xa) 'real) (abstract-op 'sin (list a) 'real)))

(define (abstract-max a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb)
      (make-abstract-const (max xa xb) (promote-type a b))
      (abstract-op 'max (list a b) (promote-type a b))))

(define (abstract-min a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb)
      (make-abstract-const (min xa xb) (promote-type a b))
      (abstract-op 'min (list a b) (promote-type a b))))

;; Order and equality (return booleans when possible)
(define (abstract-le? a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb) (<= xa xb) (let ([res (abstract-op 'le (list a b) 'boolean)]) res)))

(define (abstract-ge? a b)
  (define xa (to-number a)) (define xb (to-number b))
  (if (and xa xb) (>= xa xb) (let ([res (abstract-op 'ge (list a b) 'boolean)]) res)))

(define (abstract-eq? a b)
  (define xa (to-number a)) (define xb (to-number b))
  (cond
    [(and xa xb) (equal? xa xb)]
    [(and (abstract-const? a) (abstract-const? b) (eq? (abstract-const-type a) (abstract-const-type b)))
     (equal? (abstract-const-value a) (abstract-const-value b))]
    [else (abstract-expr-equal? a b)]))

;; Boolean evaluation (explicit)
;; Boolean evaluator: only decide ground facts; never recurse on symbolic
;; comparisons to avoid non-termination on abstract terms.
;; For unknown/symbolic cases, return #f (unknown treated as false).
(define (abstract-eval-bool x)
  (cond
    [(boolean? x) x]
    [(ac-bool-const? x) (abstract-const-value x)]
    [(abstract-op? x)
     (define op (abstract-op-operator x))
     (define args (abstract-op-operands x))
      (case op
       ;; Evaluate inequalities only when both sides are numeric;
       ;; but always accept reflexivity symbolically: x ≤ x, x ≥ x
       [(le)
        (define a (first args))
        (define b (second args))
        (cond
          [(abstract-expr-equal? a b) #t]
          [else (define xa (to-number a))
                (define xb (to-number b))
                (and xa xb (<= xa xb))])]
       [(ge)
        (define a (first args))
        (define b (second args))
        (cond
          [(abstract-expr-equal? a b) #t]
          [else (define xa (to-number a))
                (define xb (to-number b))
                (and xa xb (>= xa xb))])]
       [(and) (and (abstract-eval-bool (first args)) (abstract-eval-bool (second args)))]
       [(or)  (or  (abstract-eval-bool (first args)) (abstract-eval-bool (second args)))]
       [(not) (not (abstract-eval-bool (first args)))]
       [(implies) (or (not (abstract-eval-bool (first args))) (abstract-eval-bool (second args)))]
       [(equiv iff) (equal? (abstract-eval-bool (first args)) (abstract-eval-bool (second args)))]
       [else #f])]
    [else #f]))

;; Complex numbers (abstract)
(struct a-complex (re im) #:transparent)
(define (abstract-complex re im) (a-complex re im))
(define (abstract-complex-add z w)
  (a-complex (abstract-add (a-complex-re z) (a-complex-re w))
             (abstract-add (a-complex-im z) (a-complex-im w))))
(define (abstract-complex-mul z w)
  ;; (a+bi)(c+di) = (ac - bd) + (ad + bc)i
  (define a (a-complex-re z))
  (define b (a-complex-im z))
  (define c (a-complex-re w))
  (define d (a-complex-im w))
  (a-complex (abstract-sub (abstract-mul a c) (abstract-mul b d))
             (abstract-add (abstract-mul a d) (abstract-mul b c))))
(define (abstract-complex-exp z)
  ;; exp(x+iy) = e^x (cos y + i sin y) — keep it simple via re only if im=0
  (define x (to-number (a-complex-re z)))
  (define y (to-number (a-complex-im z)))
  (cond
    [(and x y)
     (a-complex (make-abstract-const (exp x) 'real)
                (make-abstract-const 0 'integer))]
    [else (abstract-op 'cexp (list z) 'complex)]))

;; Small numeric constants
(define (get-zero)   (make-abstract-const 0 'integer))
(define (get-one)    (make-abstract-const 1 'integer))
(define (get-two)    (make-abstract-const 2 'integer))
(define (get-three)  (make-abstract-const 3 'integer))
(define (get-four)   (make-abstract-const 4 'integer))
(define (get-five)   (make-abstract-const 5 'integer))
(define (get-fifteen) (make-abstract-const 15 'integer))

;; Guard-related defaults (for guarded negation tests)
(define (get-guard-threshold) (make-abstract-const 1 'integer))
(define (get-guard-complement) (make-abstract-const 0 'integer))

;; Physics defaults
(define (get-epsilon-real) (make-abstract-const 1e-6 'real))
(define (get-correlation-factor) (make-abstract-const 1 'integer))

;; Fast-mode regulator (environment overridable); default=true to keep checks snappy
(define (fast-mode?)
  (let ([v (getenv "LUX_FAST")])
    (if v
        (or (string-ci=? v "1") (string-ci=? v "true"))
        #f)))

;; Regulator defaults (tunable)
(define (get-default-rc-N) (if (fast-mode?) 400 2000))
(define (get-default-rc-K) (if (fast-mode?) 4 6))

(define (get-feynman-step-limit)
  (make-abstract-const (if (fast-mode?) 2 3) 'integer))
