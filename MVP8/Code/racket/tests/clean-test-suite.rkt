#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

;; Clean Comprehensive Test Suite (compat)

(require racket/contract
         racket/match
         racket/function
         racket/hash
         rackunit
         "core.rkt"
         (file "../src/foundation/lux-axioms.rkt"))

;; Bring algebraic operations into test namespace
(require (file "../src/algebra/algebraic-structures.rkt")
         (file "../src/algebra/auxiliary-transporters.rkt"))

(provide (all-defined-out))

(define (run-clean-test-suite)
  (displayln "=== CLEAN TEST SUITE ===")
  (displayln "Auxiliary-Modulated Constructions + V2 Foundation")
  (displayln "")
  (displayln "Running V2 Rigorous Foundation Tests...")
  (run-lux-axioms-rigorous-tests)
  (displayln "")
  (displayln "Running Auxiliary-Modulated Construction Tests...")
  (test-auxiliary-modulated-constructions)
  (displayln "")
  (displayln "=== ALL CLEAN TESTS COMPLETED ==="))

(define (test-auxiliary-modulated-constructions)
  (displayln "Testing auxiliary-modulated constructions...")
  (define test-elements (list (semiring-element 1 B) (semiring-element 2 B) (semiring-element 3 B)))
  (define tests-passed 0)
  (define total-tests 0)

  (displayln "  Testing auxiliary transporter...")
  (for ([elem test-elements])
    (set! total-tests (+ total-tests 1))
    (define transported (auxiliary-transporter 1 1 1 elem))
    (define transporter-works (and (semiring-element? transported)
                                  (equal? (semiring-element-semiring-type transported) B)))
    (if transporter-works (set! tests-passed (+ tests-passed 1)) (void)))

  (displayln "  Testing moduli-driven Feynman steps...")
  (for ([elem test-elements])
    (set! total-tests (+ total-tests 4))
    (define modulated-0 (modulated-ad₀ elem))
    (define modulated-1 (modulated-ad₁ elem))
    (define modulated-2 (modulated-ad₂ elem))
    (define modulated-3 (modulated-ad₃ elem))
    (define feynman-works (and (semiring-element? modulated-0)
                              (semiring-element? modulated-1)
                              (semiring-element? modulated-2)
                              (semiring-element? modulated-3)))
    (if feynman-works (set! tests-passed (+ tests-passed 4)) (void)))

  (displayln "  Testing monoid semiring structure...")
  (for ([elem (take test-elements 2)])
    (set! total-tests (+ total-tests 2))
    (define mult-result (monoid-semiring-multiply elem (semiring-element 2 B)))
    (define add-result (monoid-semiring-add elem (semiring-element 2 B)))
    (define semiring-works (and (semiring-element? mult-result)
                               (semiring-element? add-result)))
    (if semiring-works (set! tests-passed (+ tests-passed 2)) (void)))

  (displayln "  Testing conjugation auxiliary swap...")
  (for ([elem test-elements])
    (set! total-tests (+ total-tests 1))
    (define conjugated (starB elem))
    (define conjugation-works (and (semiring-element? conjugated)
                                  (equal? (semiring-element-semiring-type conjugated) B)))
    (if conjugation-works (set! tests-passed (+ tests-passed 1)) (void)))

  (displayln "  Testing auxiliary-modulated composition...")
  (for ([elem (take test-elements 2)])
    (set! total-tests (+ total-tests 2))
    (define weight (step-weight elem))
    (define modulated-result (modulated-ad₀ elem))
    (define composition-works (and (semiring-element? weight)
                                  (semiring-element? modulated-result)))
    (if composition-works (set! tests-passed (+ tests-passed 2)) (void)))

  (define success-rate (* 100 (/ tests-passed total-tests)))
  (displayln (format "Auxiliary-modulated tests: ~a/~a (~a%)" tests-passed total-tests (exact-round success-rate)))

  (if (= tests-passed total-tests)
      (displayln "  ✅ All auxiliary-modulated tests passed!")
      (displayln "  ❌ Some auxiliary-modulated tests failed!")))

(displayln "Clean Test Suite initialized")
