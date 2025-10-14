#lang Lux

;; Yoneda-style example (categorical logic appendix flavor)
;; We witness that observers/embeddings determine morphisms via their action on test objects.

(require (file "../../src/main.rkt"))

(provide prove-yoneda-summary)

(define (prove-yoneda-summary)
  ;; Test objects (generators) in each semiring
  (define l1 (semiring-element (get-one) L))
  (define r1 (semiring-element (get-one) R))
  (define b1 (semiring-element (get-one) B))

  ;; Naturalities (mirroring tests/spec-aligned-comprehensive-tests.rkt V10-Class checks)
  (define nat-L (equal? (ν_L (ad₀ b1)) (ν_L b1)))
  (define nat-R (equal? (ν_R (ad₁ b1)) (ν_R b1)))

  ;; Retracts witness “components determine arrows”
  (define retr-L (equal? (ν_L (ι_L l1)) l1))
  (define retr-R (equal? (ν_R (ι_R r1)) r1))

  ;; Bulk = two boundaries yields uniqueness via components
  (define b2 (ι_L (ν_L b1)))
  (define b3 (ι_R (ν_R b1)))
  (define reconst ((semiring-ops-add B-ops) b2 b3))
  (define uniq (and (equal? (ν_L b1) (ν_L reconst))
                    (equal? (ν_R b1) (ν_R reconst))))

  (list (cons 'naturality-L nat-L)
        (cons 'naturality-R nat-R)
        (cons 'retract-L retr-L)
        (cons 'retract-R retr-R)
        (cons 'bulk-equals-two-boundaries uniq)))
