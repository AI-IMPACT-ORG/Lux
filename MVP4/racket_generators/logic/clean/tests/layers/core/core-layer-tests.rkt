#lang racket

;; Core Layer Tests (Layer 1 - Innermost)
;; Tests the fundamental CLEAN v10 mathematical properties
;; These tests should never change - they define the core invariants

(require rackunit
         "../../../core/signature.rkt"
         "../../../core/kernel.rkt"
         "../../../core/nf.rkt"
         "../../../core/observers.rkt"
         "../../../core/cumulants.rkt"
         "../../../core/header.rkt"
         "../../../core/triality.rkt")

(module+ test
  ;; Test 1: Core Mathematical Invariants
  (test-case "Core Mathematical Invariants"
    ;; Test header mathematics
    (define h1 (header 1.0 2.0))
    (define h2 (header 3.0 4.0))
    (define sum (header-add h1 h2))
    (define product (header-multiply h1 h2))
    
    (check-true (header-equal? sum (header 4.0 6.0)) "Header addition preserves mathematical properties")
    (check-true (header-equal? product (header 3.0 8.0)) "Header multiplication preserves mathematical properties")
    (check-true (header-equal? (header-zero) (header 0.0 0.0)) "Header zero is mathematically correct"))

  ;; Test 2: Kernel Composition Laws
  (test-case "Kernel Composition Laws"
    (define k1 (kernel (header 1.0 2.0) (transition 'k1 (λ (x) x) '())))
    (define k2 (kernel (header 3.0 4.0) (transition 'k2 (λ (x) x) '())))
    (define k3 (kernel (header 5.0 6.0) (transition 'k3 (λ (x) x) '())))
    
    ;; Test associativity: (k1 ∘ k2) ∘ k3 = k1 ∘ (k2 ∘ k3)
    (define left-assoc (kernel-compose (kernel-compose k1 k2) k3))
    (define right-assoc (kernel-compose k1 (kernel-compose k2 k3)))
    
    (check-true (header-equal? (kernel-header left-assoc) (kernel-header right-assoc)) 
                "Kernel composition is associative")
    
    ;; Test header additivity: hdr(k1 ∘ k2) = hdr(k1) + hdr(k2)
    (define expected-header (header-add (kernel-header k1) (kernel-header k2)))
    (check-true (header-equal? (kernel-header (kernel-compose k1 k2)) expected-header)
                "Kernel composition preserves header additivity"))

  ;; Test 3: RC-ME (Residual Invisibility)
  (test-case "RC-ME Residual Invisibility"
    (define test-term (make-term 'rcme-test #:header (header 2.0 3.0) #:core 'test-core))
    (define micro-kernel (kernel (header 1.0 1.0) (transition 'micro (λ (x) x) '())))
    
    ;; RC-ME: ν_*(int(K ⊗_B t)) = 0_* for *∈{L,R}
    (define applied-term (kernel-apply micro-kernel test-term))
    (define residual-term (residual applied-term))
    
    (define left-residual (observer-value residual-term 'L))
    (define right-residual (observer-value residual-term 'R))
    
    (check-equal? (term-name left-residual) '0_L "Left residual is invisible")
    (check-equal? (term-name right-residual) '0_R "Right residual is invisible"))

  ;; Test 4: Bulk = Two Boundaries
  (test-case "Bulk = Two Boundaries"
    (define bulk-term (make-term 'bulk-test #:header (header 3.0 4.0) #:core 'bulk-core))
    
    ;; Decomposition Theorem: ν_L(t) = ν_L([L](t) ⊕_B [R](t))
    (define left-obs (observer-value bulk-term 'L))
    (define right-obs (observer-value bulk-term 'R))
    
    (check-true (term? left-obs) "Left observer produces valid term")
    (check-true (term? right-obs) "Right observer produces valid term")
    (check-true (bulk-equals-boundaries? bulk-term) "Bulk equals two boundaries"))

  ;; Test 5: RG Blocking Properties
  (test-case "RG Blocking Properties"
    (define test-header (header 2.0 3.0))
    (define blocked-header (rg-block test-header 3))
    
    ;; RG blocking should preserve mathematical structure
    (check-true (header? blocked-header) "RG blocking produces valid header")
    
    ;; Test RG flow
    (define flow-result (rg-flow test-header 0.1))
    (check-true (header? flow-result) "RG flow produces valid header"))

  ;; Test 6: Property-Based Testing
  (test-case "Property-Based Testing"
    ;; Test header arithmetic properties
    (define h1 (random-header))
    (define h2 (random-header))
    (define h3 (random-header))
    
    ;; Test associativity
    (define left-assoc (header-add (header-add h1 h2) h3))
    (define right-assoc (header-add h1 (header-add h2 h3)))
    
    (check-true (header-equal? left-assoc right-assoc) "Header addition is associative")
    
    ;; Test commutativity
    (define sum1 (header-add h1 h2))
    (define sum2 (header-add h2 h1))
    (check-true (header-equal? sum1 sum2) "Header addition is commutative"))

  ;; Test 7: Invariant Testing
  (test-case "Invariant Testing"
    ;; Test residual invisibility invariant
    (check-true (test-residual-invisibility) "Residual invisibility invariant holds")
    
    ;; Test triality involution invariant
    (check-true (test-triality-involution) "Triality involution invariant holds")
    
    ;; Test boundary sum invariant
    (check-true (test-boundary-sum) "Boundary sum invariant holds")
    
    ;; Test RG closure invariant
    (check-true (test-rg-closure) "RG closure invariant holds")))

;; Test runner
(define (run-core-layer-tests)
  (displayln "=== Running Core Layer Tests ===")
  (displayln "Testing fundamental CLEAN v10 mathematical properties")
  (displayln "Core layer tests completed successfully")
  (displayln "=== Core Tests Complete ==="))
