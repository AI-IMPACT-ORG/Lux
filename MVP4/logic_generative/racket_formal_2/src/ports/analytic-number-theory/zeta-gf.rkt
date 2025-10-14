#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Zeta as a generating functional with gauges and RC-normalization

(require (file "./rc-scheme.rkt")
         (file "../../foundations/abstract-core.rkt")
         (file "../../foundations/abstract-intervals.rkt"))

(provide (all-defined-out))

(struct zeta-gf (scheme) #:transparent)

(define (make-zeta-gf #:scheme [scheme (make-rc-scheme)])
  (zeta-gf scheme))

(define (zeta-gf-eval gf s #:gauge [g 'dirichlet])
  (match g
    ['dirichlet (zeta-dirichlet/rc (zeta-gf-scheme gf) s)]
    ['euler     (zeta-euler/rc (zeta-gf-scheme gf) s)]
    ['xi        (xi/rc (zeta-gf-scheme gf) s)]
    [_ (zeta-dirichlet/rc (zeta-gf-scheme gf) s)]))

(define (zeta-gf-equal-gauges? gf s)
  (equal-mod-rc? (zeta-gf-scheme gf) s))

(define (zeta-gf-universal? gf s)
  (rc-universal? (zeta-gf-scheme gf) s))

(define (zeta-gf-critical-line-invariants? gf t)
  (and (xi-symmetric? (zeta-gf-scheme gf) t)
       (critical-line-invariants? (zeta-gf-scheme gf) t)))

