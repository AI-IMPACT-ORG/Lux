#lang racket/base

(require rackunit
         racket/list
         "../signature.rkt"
         "../nf.rkt"
         "../observers.rkt"
         "../triality.rkt"
         "../cumulants.rkt")

(module+ test
  (define bulk (make-term 'bulk#:0 #:header '(2 . 1) #:core 'bulk-core))
  (define l (reflect-L bulk))
  (define r (reflect-R bulk))

  (test-equal? "normal-form captures headers" 2
               (nf-phase (normal-form bulk)))
  (test-equal? "normal-form scale" 1
               (nf-scale (normal-form bulk)))

  (test-case "reconstitute equals boundary sum on observers"
    (define rho (reconstitute bulk))
    (check-equal? (term-name (observer-value rho 'L)) (term-name l))
    (check-equal? (term-name (observer-value rho 'R)) (term-name r)))

  (test-case "residual is invisible to observers"
    (define res (residual bulk))
    (check-equal? (term-metadata res) 'residual)
    (check-equal? (term-name (observer-value res 'L)) '0_L)
    (check-equal? (term-name (observer-value res 'R)) '0_R))

  (test-case "triality sum preserves additive headers"
    (define sum (triality-sum l r))
    (check-equal? (nf-phase (normal-form sum))
                  (+ (nf-phase (normal-form l))
                     (nf-phase (normal-form r))))
    (check-equal? (nf-scale (normal-form sum))
                  (+ (nf-scale (normal-form l))
                     (nf-scale (normal-form r)))))

  (test-case "cumulant registry reflects headers"
    (clear-observables!)
    (register-observable 0 bulk)
    (register-observable 1 (make-term 'probe#:1 #:header '(0 . 3) #:core 'probe))
    (check-equal? (value-g 0) 'bulk-core)
    (check-equal? (value-G 0 1) '(cov bulk#:0 probe#:1)))

  (test-case "generating functional accumulates phases/scales"
    (clear-observables!)
    (register-observable 0 (make-term 'x #:header '(1 . 0)))
    (register-observable 1 (make-term 'y #:header '(0 . 2)))
    (define Z (generating-functional (list (cons 0 1) (cons 1 1))))
    (check-equal? (term-name Z) "Z[J]")
    (check-equal? (nf-phase (normal-form Z)) 1)
    (check-equal? (nf-scale (normal-form Z)) 2)))
