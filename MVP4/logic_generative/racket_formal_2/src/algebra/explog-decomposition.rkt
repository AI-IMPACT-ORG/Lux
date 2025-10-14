#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Exponential/Logarithmic Decomposition and NF

 (require racket/function
          racket/list
          (file "../foundations/abstract-core.rkt")
          (file "./algebraic-structures.rkt")
          (file "./central-scalars.rkt"))

(provide (all-defined-out))

(define (dec-z-zbar b)
  (define v (semiring-element-value b))
  ;; In the abstract setting, treat all B-elements as having zero headers and
  ;; carry the entire payload into the Core component.
  (list 0 0 0 (semiring-element v Core)))

(define (rec-z-zbar k mz mzb core)
  (define cv (semiring-element-value core))
  (if (and (eq? k 0) (eq? mz 0) (eq? mzb 0))
      (semiring-element cv B)
      (semiring-element
       (abstract-mul (abstract-mul (abstract-expt (get-φ) k)
                                   (abstract-expt (get-z) mz))
                     (abstract-mul (abstract-expt (get-z̄) mzb) cv))
       B)))

(define (collapse k mz mzb core)
  (list k (+ mz mzb) core))

(define (NF-B t)
  (define d (dec-z-zbar t))
  (collapse (first d) (second d) (third d) (fourth d)))

(define (test-exp-log-isomorphism b)
  (define d (dec-z-zbar b))
  (define r (apply rec-z-zbar d))
  (and (semiring-element? r)
       (eq? (semiring-element-semiring-type r) B)
       (abstract-expr-equal? (semiring-element-value b)
                             (semiring-element-value r))))

(define (test-header-factoring b)
  (test-exp-log-isomorphism b))

(define (test-multiplicative-compatibility t u)
  (define tt (semiring-element t B))
  (define uu (semiring-element u B))
  (define tu ((semiring-ops-mul B-ops) tt uu))
  (define dt (dec-z-zbar tt))
  (define du (dec-z-zbar uu))
  (define dtu (dec-z-zbar tu))
  (and (eq? (first dtu) (+ (first dt) (first du)))
       (eq? (second dtu) (+ (second dt) (second du)))
       (eq? (third dtu) (+ (third dt) (third du)))
       (abstract-semiring-equal? (fourth dtu)
                                 ((semiring-ops-mul Core-ops)
                                  (fourth dt) (fourth du)))))
