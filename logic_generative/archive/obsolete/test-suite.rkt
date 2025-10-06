#lang racket

;; @logic/gen Test Suite
;; Comprehensive tests for generator-focused CLEAN language

(require rackunit
         "truth.rkt"
         "core.rkt"
         "rg.rkt"
         "ports/boolean.rkt")

(provide (all-defined-out))

;; ============================================================================
;; CORE GENERATOR TESTS
;; ============================================================================

(define-test-suite core-generator-tests
  "Core generator operations"
  
  (test-case "Generator identity"
    (define id (gen-id))
    (check-true (gen? id))
    (check-equal? (gen-apply id 5) 5)
    (check-equal? (gen-apply id 'test) 'test))
  
  (test-case "Generator composition"
    (define inc (make-gen add1 'increment '(monotonic)))
    (define double (make-gen (λ (x) (* 2 x)) 'double '(linear)))
    (define inc-then-double (gen-compose double inc))
    (check-equal? (gen-apply inc-then-double 5) 12))
  
  (test-case "Generator powers"
    (define inc (make-gen add1 'increment '(monotonic)))
    (define inc3 (gen-power inc 3))
    (check-equal? (gen-apply inc3 5) 8))
  
  (test-case "Green's sum generator"
    (define inc (make-gen add1 'increment '(monotonic)))
    (define G3 (greens-sum-generator inc 3))
    (check-equal? (gen-apply G3 0) 6))  ; 0 + 1 + 2 + 3 = 6
  )

;; ============================================================================
;; RG AND CONVERGENCE TESTS
;; ============================================================================

(define-test-suite rg-convergence-tests
  "RG blocking and convergence tests"
  
  (test-case "RG blocking"
    (define scale (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    (define blocked (rg-block-generator scale 2))
    (check-true (gen? blocked))
    (check-equal? (gen-apply blocked 1) 4))  ; 2^2 = 4
  
  (test-case "Flow convergence"
    (define f (λ (x) (/ (+ x (/ 2 x)) 2)))  ; Newton's method for sqrt(2)
    (check-true (test-flow-convergence f 1.0 0.001 100)))
  
  (test-case "Fixed point"
    (define f (λ (x) (cos x)))
    (define fp-gen (fixed-point-generator f 0.001))
    (define result (gen-apply fp-gen 1.0))
    (check-true (< (abs (- result (cos result))) 0.001)))
  
  (test-case "Moduli flow composition"
    (define flow1 (make-moduli-flow 1 0 0 1))
    (define flow2 (make-moduli-flow 0 1 1 0))
    (check-true (test-moduli-flow-composition flow1 flow2)))
  )

;; ============================================================================
;; DOMAIN PORT TESTS
;; ============================================================================

(define-test-suite domain-port-tests
  "Domain port generator tests"
  
  (test-case "Boolean port creation"
    (define B (make-boolean-port))
    (check-true (domain-port-gen? B))
    (check-equal? (domain-port-gen-carrier B) 'boolean)
    (check-equal? (domain-port-gen-q-vector B) '(1 0 0)))
  
  (test-case "Lambda port creation"
    (define L (make-lambda-port))
    (check-true (domain-port-gen? L))
    (check-equal? (domain-port-gen-carrier L) 'lambda)
    (check-equal? (domain-port-gen-q-vector L) '(0 1 0)))
  
  (test-case "InfoFlow port creation"
    (define I (make-infoflow-port))
    (check-true (domain-port-gen? I))
    (check-equal? (domain-port-gen-carrier I) 'infoflow)
    (check-equal? (domain-port-gen-q-vector I) '(0 0 0)))
  
  (test-case "QFT port creation"
    (define Q (make-qft-port))
    (check-true (domain-port-gen? Q))
    (check-equal? (domain-port-gen-carrier Q) 'euclidean)
    (check-equal? (domain-port-gen-q-vector Q) '(0 0 1)))
  
  (test-case "Domain port evaluation"
    (define B (make-boolean-port))
    (check-true (psdm-defined? B 1))
    (check-true (psdm-defined? B 'test))
    (check-false (psdm-defined? B 'non-halting)))
  
  (test-case "Domain port composition"
    (define B (make-boolean-port))
    (define L (make-lambda-port))
    (define BL (compose-domain-ports B L))
    (check-true (domain-port-gen? BL))
    (check-equal? (domain-port-gen-q-vector BL) '(1 1 0)))
  )

;; ============================================================================
;; GENERATOR ALGEBRA TESTS
;; ============================================================================

(define-test-suite generator-algebra-tests
  "Generator algebra property tests"
  
  (test-case "Composition associativity"
    (define g1 (make-gen add1 'inc '(monotonic)))
    (define g2 (make-gen (λ (x) (* 2 x)) 'double '(linear)))
    (define g3 (make-gen (λ (x) (* 3 x)) 'triple '(linear)))
    (check-true (test-associativity g1 g2 g3)))
  
  (test-case "Identity laws"
    (define g (make-gen add1 'inc '(monotonic)))
    (check-true (test-identity g)))
  
  (test-case "RG closure"
    (define K (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    (check-true (test-rg-closure K)))
  )

;; ============================================================================
;; INTEGRATION TESTS
;; ============================================================================

(define-test-suite integration-tests
  "Integration tests for complete workflows"
  
  (test-case "Complete generator workflow"
    ;; Create kernel
    (define K (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    
    ;; Generate Green's sum
    (define G3 (greens-sum-generator K 3))
    
    ;; Apply RG blocking
    (define K-blocked (rg-block-generator K 2))
    
    ;; Test with domain port
    (define B (make-boolean-port))
    (define test-term 5)
    
    (when (psdm-defined? B test-term)
      (define result (domain-port-eval B test-term))
      (check-equal? result test-term)))
  
  (test-case "Moduli flow workflow"
    ;; Create moduli flows
    (define flow1 (make-moduli-flow 1 0 0 1))
    (define flow2 (make-moduli-flow 0 1 1 0))
    
    ;; Compose flows
    (define composed (compose-moduli-flows flow1 flow2))
    
    ;; Verify composition
    (check-equal? (moduli-flow-μL composed) 1)
    (check-equal? (moduli-flow-θL composed) 1)
    (check-equal? (moduli-flow-μR composed) 1)
    (check-equal? (moduli-flow-θR composed) 1))
  )

;; ============================================================================
;; COMPLETE TEST SUITE
;; ============================================================================

(define-test-suite logic-gen-complete-tests
  "Complete @logic/gen test suite"
  core-generator-tests
  rg-convergence-tests
  domain-port-tests
  generator-algebra-tests
  integration-tests)

;; ============================================================================
;; TEST RUNNER
;; ============================================================================

(define (run-logic-gen-tests)
  "Run complete @logic/gen test suite"
  (run-tests logic-gen-complete-tests))

(define (run-logic-gen-tests-verbose)
  "Run complete @logic/gen test suite with verbose output"
  (run-tests logic-gen-complete-tests #:verbosity 'high))

;; Run tests if this file is executed directly
(when (equal? (current-command-line-arguments) '())
  (run-logic-gen-tests))

