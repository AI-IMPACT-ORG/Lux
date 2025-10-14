#lang racket
;; Internalization: map symbolic boolean expressions to L-level guarded logic terms

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./guarded-negation.rkt"))

(provide (all-defined-out))

(define (L-true) (semiring-element (get-one) L))
(define (L-false) (semiring-element (get-zero) L))

(define (embed-proposition expr)
  ;; Embed an abstract boolean/formula as an L-element via tagging
  (semiring-element (abstract-op 'prop (list expr) 'boolean) L))

(define (internalize-boolean expr)
  (cond
    [(abstract-op? expr)
     (define op (abstract-op-operator expr))
     (define args (abstract-op-operands expr))
     (case op
       [(not) (gn-not (internalize-boolean (first args)))]
       [(and) (gn-and (internalize-boolean (first args))
                      (internalize-boolean (second args)))]
       [(or)  (gn-or (internalize-boolean (first args))
                     (internalize-boolean (second args)))]
       [(implies) (gn-implies (internalize-boolean (first args))
                              (internalize-boolean (second args)))]
       [(equiv iff) (gn-iff (internalize-boolean (first args))
                            (internalize-boolean (second args)))]
       [else (embed-proposition expr)])]
    [(abstract-const? expr)
     (cond [(eq? (abstract-const-type expr) 'boolean)
            (if (abstract-const-value expr) (L-true) (L-false))]
           [else (embed-proposition expr)])]
    [else (embed-proposition expr)]))

