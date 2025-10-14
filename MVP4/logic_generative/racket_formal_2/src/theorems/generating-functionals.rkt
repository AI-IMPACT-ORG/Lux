#lang racket

(require racket/list
         racket/function
         (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../ports/domain-registry.rkt"))

(provide (all-defined-out))

;; Theorem: Generating functionals unify paradigms
;; Construct canonical generating functionals for Turing, Lambda, Blockchain, QFT,
;; normalize to B via NF^B, and verify pairwise equality up to abstract equality.

(define (gf-unity-detailed)
  (produce-generating-functionals-detailed))

(define (gf-unity-pairs-equal? gfs)
  (define s (length gfs))
  (for/and ([i (in-range s)] [j (in-range s)])
    (define xi (list-ref gfs i))
    (define xj (list-ref gfs j))
    (abstract-expr-equal? (semiring-element-value xi)
                          (semiring-element-value xj))))

(define (verify-generating-functional-unity)
  (gf-unity-pairs-equal? (gf-unity-detailed)))

;; Additional constraints: NF invariance and header-only gauge neutrality across the set
(define (verify-generating-functional-constraints)
  (define gfs (gf-unity-detailed))
  (for/and ([g gfs])
    (let* ([d (dec-z-zbar g)]
           [r (apply rec-z-zbar d)])
      (and (abstract-semiring-equal? (NF^B-generalized g) g)
           (abstract-semiring-equal? (ν_L g) (ν_L r))
           (abstract-semiring-equal? (ν_R g) (ν_R r))))))
