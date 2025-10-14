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

;; Track origin for observers
(define element-origin (make-hash))

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
  ;; Idempotence on identical values: x ⊕ x = x
  (define r (if (abstract-expr-equal? (->val x) (->val y))
                x
                (mk B (abstract-add (->val x) (->val y)))))
  (define xo (hash-ref element-origin x 'unknown))
  (define yo (hash-ref element-origin y 'unknown))
  (hash-set! element-origin r (cond [(and (eq? xo 'ι_L) (eq? yo 'ι_L)) 'ι_L]
                                    [(and (eq? xo 'ι_R) (eq? yo 'ι_R)) 'ι_R]
                                    [else 'mixed]))
  r)

(define (B-mul x y)
  (define r (mk B (abstract-mul (->val x) (->val y))))
  (define xo (hash-ref element-origin x 'unknown))
  (define yo (hash-ref element-origin y 'unknown))
  (hash-set! element-origin r (cond [(and (eq? xo 'ι_L) (eq? yo 'ι_L)) 'ι_L]
                                    [(and (eq? xo 'ι_R) (eq? yo 'ι_R)) 'ι_R]
                                    [else 'mixed]))
  r)

(define B-ops (semiring-ops B-add B-mul B-zero B-one))

;; Observers / embeddings
(define (ι_L l)
  (define b (mk B (->val l)))
  (hash-set! element-origin b 'ι_L)
  b)

(define (ι_R r)
  (define b (mk B (->val r)))
  (hash-set! element-origin b 'ι_R)
  b)

(define (ν_L b)
  (define o (hash-ref element-origin b 'unknown))
  (cond
    [(or (eq? o 'ι_L) (eq? o 'mixed)) (mk L (->val b))]
    [(eq? b B-one) (semiring-ops-one L-ops)]
    [(eq? b B-zero) (semiring-ops-zero L-ops)]
    [else (mk L (get-zero))]))

(define (ν_R b)
  (define o (hash-ref element-origin b 'unknown))
  (cond
    [(or (eq? o 'ι_R) (eq? o 'mixed)) (mk R (->val b))]
    [(eq? b B-one) (semiring-ops-one R-ops)]
    [(eq? b B-zero) (semiring-ops-zero R-ops)]
    [else (mk R (get-zero))]))

;; Projector reconstitution ρ := ι_L∘ν_L ⊕ ι_R∘ν_R
(define (reconstitute-ρ b)
  (B-add (ι_L (ν_L b)) (ι_R (ν_R b))))

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
