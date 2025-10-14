#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Feynman Path Integral (QFT)

(require racket/contract
         racket/match
         racket/function
         racket/hash
         rackunit
         (file "../core.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../logic/guarded-negation.rkt")
         (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt"))

(provide (all-defined-out))

(struct history (steps action weight) #:transparent)
(struct micro-step (from-term to-term transformation) #:transparent)

(define (make-micro-step from-term to-term transformation)
  (micro-step from-term to-term transformation))

(define (make-history steps)
  (define action (compute-action steps))
  (define weight (compute-weight action))
  (history steps action weight))

(define (compute-action steps)
  (if (null? steps)
      (get-one)
      (foldl abstract-mul (get-one) (map (λ (step)
                          (define from-val (semiring-element-value (micro-step-from-term step)))
                          (define to-val (semiring-element-value (micro-step-to-term step)))
                          (abstract-abs (abstract-sub to-val from-val)))
                        steps))))

(define (compute-weight action)
  (abstract-complex-exp (abstract-complex action (get-zero))))

(define (schwinger-dyson-derivative partition-fn source-term)
  (define epsilon (get-epsilon-real))
  (define perturbed-source ((semiring-ops-add B-ops) source-term (semiring-element epsilon B)))
  (define z-original (partition-fn source-term))
  (define z-perturbed (partition-fn perturbed-source))
  (define derivative (abstract-div (abstract-sub (semiring-element-value z-perturbed) (semiring-element-value z-original)) epsilon))
  (abstract-complex (get-zero) derivative))

(define (partition-function histories source-term)
  (define weights (map history-weight histories))
  (define total-weight (foldl abstract-complex-add (abstract-complex (get-zero) (get-zero)) weights))
  (semiring-element total-weight B))

(define (generate-histories initial-term max-steps)
  (define (generate-step term step-count)
    (if (abstract-ge? step-count max-steps)
        (list (make-history '()))
        (let* ([transformed-term ((semiring-ops-mul B-ops) term (semiring-element (get-correlation-factor) B))]
               [step (make-micro-step term transformed-term 'multiply)]
               [remaining-histories (generate-step transformed-term (abstract-add step-count (make-abstract-const 1 'integer)))])
          (cons (make-history (list step)) remaining-histories))))
  (generate-step initial-term (make-abstract-const 0 'integer)))

(define (feynman-path-integral initial-term transformations)
  (define histories (generate-histories initial-term (get-feynman-step-limit)))
  (define partition-fn (λ (source) (partition-function histories source)))
  (define z-result (partition-fn (semiring-element (make-abstract-const 1 'integer) B)))
  z-result)

(define (two-point-correlation histories x-term y-term)
  (define weights (map history-weight histories))
  (define correlations (map (λ (weight)
                              (abstract-complex-mul weight (abstract-complex-mul (abstract-complex (semiring-element-value x-term) (get-zero))
                                                                                     (abstract-complex (semiring-element-value y-term) (get-zero)))))
                            weights))
  (define total-correlation (foldl abstract-complex-add (abstract-complex (get-zero) (get-zero)) correlations))
  (semiring-element total-correlation B))
