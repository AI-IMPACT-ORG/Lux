#lang racket
; (c) 2025 AI.IMPACT GmbH

(require racket/list
         (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt"))

(provide (all-defined-out))

;; Evidence isomorphisms: structure-preserving relabellings (or conservative extensions)
(struct evidence-iso (name forward backward) #:transparent)

;; Default identity forwards/backwards
(define (identity-forward x) x)
(define (identity-backward x) x)

;; A very small finite sample used for lightweight checks
(define (sample-elements)
  (list (semiring-element (get-zero) B)
        (semiring-element (get-one) B)
        (semiring-element (get-two) B)
        (semiring-element (get-one) L)
        (semiring-element (get-one) R)
        (semiring-element (get-one) Core)))

;; Minimal verification: bijectivity over the sample and stability of carriers
(define (verify-evidence-isomorphism iso)
  (define f (evidence-iso-forward iso))
  (define g (evidence-iso-backward iso))
  (and (procedure? f)
       (procedure? g)
       (for/and ([x (in-list (sample-elements))])
         (and (equal? (g (f x)) x)
              (eq? (semiring-element-semiring-type (f x))
                   (semiring-element-semiring-type x))))))
;; (no local braid aliases needed in the minimal checker)
