#lang racket
; (c) 2025 AI.IMPACT GmbH

;; Side-car integration tests that realize proofs as L-level derivations.
;; - Validates rules-as-theorems via the sequent checker (self-application)
;; - Checks Gödel 1 & 2 and Rice generalization are internalized to L

(require rackunit
         (file "../src/foundations/abstract-core.rkt")
         (file "../src/algebra/algebraic-structures.rkt")
         (file "../src/logic/guarded-negation.rkt")
         (file "../src/logic/internalize.rkt")
         (file "../src/logic/sequent-checker.rkt")
         (file "../src/logic/rule-catalog.rkt")
         (file "../src/theorems/self-application.rkt")
         (only-in (file "../src/logic/incompleteness.rkt")
                  godel1-proof godel2-proof)
         (only-in (file "../src/logic/rice-generalization.rkt")
                  rice-generalization-proof)
         (file "../src/logic/quantifiers.rkt")
         (only-in (file "../src/logic/kernel-checker.rkt")
                  kernel-check prove-and-intro)
         "yoneda-shim.rkt")

(provide run-proofs-integration)

;; Ensure an L-term helper
(define (is-L? t)
  (and (semiring-element? t)
       (eq? (semiring-element-semiring-type t) L)))

(define (run-proofs-integration)
  (displayln "=== proofs integration: realizing witnesses in L ===")
  ;; 1) Rules as theorems: derive via catalog and check via sequent checker
  (check-true (self-apply-ruleset) "rules self-application (sequent checker) passes")

  ;; 2) Gödel incompleteness schemata: program → internalized L term
  (let ([g1 (godel1-proof)]
        [g2 (godel2-proof)])
    (check-true (is-L? g1) "Gödel 1 internalized to L")
    (check-true (is-L? g2) "Gödel 2 internalized to L"))

  ;; 3) Rice generalization schema: internalized L term
  (let ([rp (rice-generalization-proof 'extensional-nontrivial)])
    (check-true (is-L? rp) "Rice-generalization internalized to L"))

  ;; 4) Quantifiers: ∀-intro with computed freshness on empty ctx
  (let* ([ctx '()]
         [x   (abstract-op 'var (list (make-abstract-const 'x 'symbol)) 'term)]
         [phi (abstract-op 'phi '() 'predicate)])
    (check-true (is-L? (rule-forall-intro ctx x phi)) "forall-intro (freshness computed)"))

  ;; 5) Yoneda-style side-car check (observer/naturality summary)
  (check-true (yoneda-summary-ok?) "yoneda summary side-car ok")

  (displayln "=== proofs integration: all checks passed ===")
  #t)
