#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Algebraic Structures (Semiring and observers)

(require racket/function
         racket/hash
         (file "../foundations/abstract-core.rkt"))

(provide (all-defined-out))

;; Semiring primitives (abstract throughout)
(struct semiring-element (value semiring-type) #:transparent)
(struct semiring-ops (add mul zero one) #:transparent)

;; Enhanced semiring element for abstract content
(struct enhanced-semiring-element (content semiring-type) #:transparent)

;; Create abstract/symbolic elements
(define (make-abstract-element expr semiring-type)
  (enhanced-semiring-element (abstract-expr 'expression expr 'abstract) semiring-type))
(define (make-symbolic-var name semiring-type)
  (enhanced-semiring-element (abstract-expr 'variable name 'symbolic) semiring-type))

(define L 'L)
(define B 'B)
(define R 'R)
(define Core 'Core)

;; Track origin for observers (identity-based to avoid collisions across equal values)
(define element-origin (make-hasheq))

;; Structural origin grading for B values via an abstract wrapper
;; OriginTag := (OriginTag grade payload)
;;  - grade ∈ {'ι_L, 'ι_R, 'mixed, 'rho, 'unknown}
;;  - payload is the underlying abstract expression (without tag)

(define (make-origin-tag grade payload)
  (abstract-op 'OriginTag (list (make-abstract-const grade 'symbol) payload) 'meta))

(define (origin-grade-of-value v)
  (cond
    [(and (abstract-op? v) (eq? (abstract-op-operator v) 'OriginTag))
     (abstract-const-value (first (abstract-op-operands v)))]
    [else 'unknown]))

(define (origin-strip-value v)
  (cond
    [(and (abstract-op? v) (eq? (abstract-op-operator v) 'OriginTag))
     (second (abstract-op-operands v))]
    [else v]))

(define (b-grade b) (origin-grade-of-value (->val b)))
(define (b-strip b) (semiring-element (origin-strip-value (->val b)) B))
(define (b-set-grade b grade)
  (semiring-element (make-origin-tag grade (origin-strip-value (->val b))) B))

(define (b-with-grade-if-known b grade)
  (if (eq? grade 'unknown) b (b-set-grade b grade)))

;; Policy: how to handle unknown grade tagging
;;  - 'none (default): never write an explicit 'unknown tag
;;  - 'keep: explicitly tag with 'unknown when requested
(define *grade-unknown-policy* (box 'keep))
(define (set-grade-unknown-policy! sym)
  (cond [(memq sym '(none keep)) (set-box! *grade-unknown-policy* sym)]
        [else (error 'set-grade-unknown-policy! "unknown policy ~a" sym)]))
(define (grade-unknown-policy) (unbox *grade-unknown-policy*))

(define (b-with-grade-policy b grade)
  (cond
    [(eq? grade 'unknown)
     (if (eq? (grade-unknown-policy) 'keep) (b-set-grade b 'unknown) b)]
    [else (b-set-grade b grade)]))

(define (grade-join g1 g2)
  (cond
    [(eq? g1 g2) g1]
    [(or (eq? g1 'rho) (eq? g2 'rho)) 'mixed]
    [(eq? g1 'unknown) g2]
    [(eq? g2 'unknown) g1]
    [else 'mixed]))

(define (grade-meet g1 g2)
  (cond
    [(and (eq? g1 'ι_L) (eq? g2 'ι_L)) 'ι_L]
    [(and (eq? g1 'ι_R) (eq? g2 'ι_R)) 'ι_R]
    [(eq? g1 'unknown) g2]
    [(eq? g2 'unknown) g1]
    [else 'mixed]))

;; Helpers
(define (->val x) (if (semiring-element? x) (semiring-element-value x) x))
(define (mk S v) (semiring-element v S))

;; Ops (all abstract)
(define L-ops (semiring-ops
               (λ (x y) (mk L (abstract-add (->val x) (->val y))))
               (λ (x y) (mk L (abstract-mul (->val x) (->val y))))
               (mk L (get-zero))
               (mk L (get-one))))

(define R-ops (semiring-ops
               (λ (x y) (mk R (abstract-add (->val x) (->val y))))
               (λ (x y) (mk R (abstract-mul (->val x) (->val y))))
               (mk R (get-zero))
               (mk R (get-one))))

(define Core-ops (semiring-ops
                  (λ (x y) (mk Core (abstract-add (->val x) (->val y))))
                  (λ (x y) (mk Core (abstract-mul (->val x) (->val y))))
                  (mk Core (get-zero))
                  (mk Core (get-one))))

(define B-zero (mk B (get-zero)))
(define B-one  (mk B (get-one)))
(hash-set! element-origin B-zero 'mixed)
(hash-set! element-origin B-one 'mixed)

(define (B-add x y)
  ;; Canonical addition with grade-aware payload: when grades differ, preserve
  ;; per-term tags inside the payload to allow observers to eliminate foreign
  ;; contributions (e.g., ν_L kills ι_R-tagged summands).
  (define xv (origin-strip-value (->val x)))
  (define yv (origin-strip-value (->val y)))
  (define xg (b-grade x))
  (define yg (b-grade y))
  (define val (if (eq? xg yg)
                  (abstract-add xv yv)
                  (abstract-op 'add (list (make-origin-tag xg xv)
                                          (make-origin-tag yg yv))
                               'abstract)))
  (b-with-grade-policy (mk B val) (grade-join xg yg)))

(define (B-mul x y)
  ;; Canonical multiplication: build canonical value and compose grades by meet.
  (define xv (origin-strip-value (->val x)))
  (define yv (origin-strip-value (->val y)))
  (define xg (b-grade x))
  (define yg (b-grade y))
  (define (flatten-mul v)
    (cond
      [(and (abstract-op? v) (eq? (abstract-op-operator v) 'mul))
       (append (flatten-mul (first (abstract-op-operands v)))
               (flatten-mul (second (abstract-op-operands v))))]
      [(and (abstract-op? v) (eq? (abstract-op-operator v) 'OriginTag))
       (flatten-mul (second (abstract-op-operands v)))]
      [else (list v)]))
  (define (build-mul factors)
    (cond
      [(null? factors) (get-one)]
      [(null? (cdr factors)) (car factors)]
      [else (foldl (λ (a acc) (abstract-mul acc a)) (car factors) (cdr factors))]))
  (define factors (append (flatten-mul xv) (flatten-mul yv)))
  (define numeric-prod 1)
  (define any-real? #f)
  (define syms '())
  (for ([f factors])
    (define n (to-number f))
    (if n
        (begin (set! numeric-prod (* numeric-prod n))
               (when (not (integer? n)) (set! any-real? #t)))
        (set! syms (cons f syms))))
  (define syms-sorted (sort syms (λ (a b) (string<? (~a a) (~a b)))))
  (define factors* (if (and (number? numeric-prod) (not (= numeric-prod 1)))
                       (cons (make-abstract-const numeric-prod (if any-real? 'real 'integer)) syms-sorted)
                       syms-sorted))
  (define val (build-mul factors*))
  (b-with-grade-policy (mk B val) (grade-meet xg yg)))
;; Pretty-printing helpers for B values with origin tags
(define (origin-tag? v)
  (and (abstract-op? v) (eq? (abstract-op-operator v) 'OriginTag)))

(define (pretty-b b)
  (define v (->val b))
  (define g (origin-grade-of-value v))
  (define core (origin-strip-value v))
  (cond
    [(eq? g 'unknown) (format "~a" core)]
    [else (format "[~a] ~a" g core)]))

(define B-ops (semiring-ops B-add B-mul B-zero B-one))

;; Observers / embeddings
(define (ι_L l)
  (define b (mk B (->val l)))
  (define tagged (b-set-grade b 'ι_L))
  (hash-set! element-origin tagged 'ι_L)
  tagged)

(define (ι_R r)
  (define b (mk B (->val r)))
  (define tagged (b-set-grade b 'ι_R))
  (hash-set! element-origin tagged 'ι_R)
  tagged)

(define (ν_L b)
  (define (observe v)
    (cond
      [(abstract-op? v)
       (define op (abstract-op-operator v))
       (define args (abstract-op-operands v))
       (case op
         [(OriginTag)
          (define gr (abstract-const-value (first args)))
          (define pv (second args))
          (if (eq? gr 'ι_R) (semiring-ops-zero L-ops) (observe pv))]
         [(add)
          ((semiring-ops-add L-ops) (observe (first args)) (observe (second args)))]
         [(mul)
          ((semiring-ops-mul L-ops) (observe (first args)) (observe (second args)))]
         [else (mk L v)])]
      [else (mk L v)]))
  (observe (->val b)))

(define (ν_R b)
  (define (observe v)
    (cond
      [(abstract-op? v)
       (define op (abstract-op-operator v))
       (define args (abstract-op-operands v))
       (case op
         [(OriginTag)
          (define gr (abstract-const-value (first args)))
          (define pv (second args))
          (if (eq? gr 'ι_L) (semiring-ops-zero R-ops) (observe pv))]
         [(add)
          ((semiring-ops-add R-ops) (observe (first args)) (observe (second args)))]
         [(mul)
          ((semiring-ops-mul R-ops) (observe (first args)) (observe (second args)))]
         [else (mk R v)])]
      [else (mk R v)]))
  (observe (->val b)))

;; Projector reconstitution ρ := ι_L∘ν_L ⊕ ι_R∘ν_R
(define (reconstitute-ρ b)
  (define sum (B-add (ι_L (ν_L b)) (ι_R (ν_R b))))
  (b-set-grade sum 'rho))

;; Observers after reconstitution: homomorphic on reconstituted terms
(define (ν_L-after-ρ b) (ν_L (reconstitute-ρ b)))
(define (ν_R-after-ρ b) (ν_R (reconstitute-ρ b)))

;; Equality helpers
(define (abstract-semiring-equal? x y)
  (and (semiring-element? x)
       (semiring-element? y)
       (eq? (semiring-element-semiring-type x)
            (semiring-element-semiring-type y))
       (abstract-expr-equal? (->val x) (->val y))) )

;; Properties
(define (test-retraction-left l) (equal? (ν_L (ι_L l)) l))
(define (test-retraction-right r) (equal? (ν_R (ι_R r)) r))

(define (test-observer-homomorphism observer)
  (define pairs '((1 2) (3 4) (5 6)))
  (for/and ([p pairs])
    (define x (mk B (make-abstract-const (first p) 'integer)))
    (define y (mk B (make-abstract-const (second p) 'integer)))
    (hash-set! element-origin x 'ι_L)
    (hash-set! element-origin y 'ι_L)
    (define add-o (observer ((semiring-ops-add B-ops) x y)))
    (define mul-o (observer ((semiring-ops-mul B-ops) x y)))
    (define S (if (eq? observer ν_L) L-ops R-ops))
    (and (abstract-semiring-equal? add-o ((semiring-ops-add S) (observer x) (observer y)))
         (abstract-semiring-equal? mul-o ((semiring-ops-mul S) (observer x) (observer y))))))
