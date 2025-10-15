#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Symbolic evidence for ANT: Euler product equals Dirichlet sum; log-derivative identity

(require rackunit
         (file "./symbolic-dirichlet.rkt")
         (file "../../foundations/abstract-core.rkt"))

(provide (all-defined-out))

(define (run-ant-symbolic-evidence #:N [N 200])
  (define euler (ds-euler-product N))
  (define sum1 (ds-const1 N))
  (define ok-product-vs-sum (ds-equal? euler sum1))
  (define lam-a (ds-lambda N))
  (define lam-b (ds-lambda-by-primes N))
  (define ok-lambda (ds-equal? lam-a lam-b))
  ;; Derivation proof: -d/ds log ζ = Λ-series
  (define logz (ds-log-zeta N))
  (define dlogz (ds-deriv-log-zeta N))
  (define neg-lambda (ds-scale lam-a (make-abstract-const -1 'integer)))
  (define ok-derivation (ds-equal? dlogz neg-lambda))
  (list ok-product-vs-sum ok-lambda ok-derivation))

(define (run-ant-symbolic-evidence-tests)
  (define results (run-ant-symbolic-evidence))
  (check-true (list-ref results 0) "Euler product equals Dirichlet sum symbolically (truncated)")
  (check-true (list-ref results 1) "Von Mangoldt identity holds symbolically (prime power support)")
  (check-true (list-ref results 2) "-d/ds log ζ equals -Λ as Dirichlet series (truncated)")
  #t)
