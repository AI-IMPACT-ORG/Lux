#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

;; Shim to replicate the Yoneda-style example using plain Racket requires
;; to avoid relying on an installed #lang Lux collection in CI.

(require (file "../src/foundations/abstract-core.rkt")
         (file "../src/algebra/algebraic-structures.rkt")
         (file "../src/algebra/braided-operators.rkt")
         (file "../src/algebra/boundary-decomposition.rkt"))

(provide yoneda-summary-ok?)

(define (yoneda-summary-ok?)
  ;; Test objects (generators) in each semiring
  (define l1 (semiring-element (get-one) L))
  (define r1 (semiring-element (get-one) R))
  (define b1 (semiring-element (get-one) B))

  ;; Naturality against braids/exp-log (mirrors spec-aligned tests)
  (define nat-L (equal? (ν_L (ad₀ b1)) (ν_L b1)))
  (define nat-R (equal? (ν_R (ad₁ b1)) (ν_R b1)))

  ;; Retracts witness “components determine arrows”
  (define retr-L (equal? (ν_L (ι_L l1)) l1))
  (define retr-R (equal? (ν_R (ι_R r1)) r1))

  ;; Bulk = two boundaries yields uniqueness via components (use reconstitution)
  (define reconst (reconstitute b1))
  (define uniq (and (equal? (ν_L b1) (ν_L reconst))
                    (equal? (ν_R b1) (ν_R reconst))))
  (and nat-L nat-R retr-L retr-R uniq))
