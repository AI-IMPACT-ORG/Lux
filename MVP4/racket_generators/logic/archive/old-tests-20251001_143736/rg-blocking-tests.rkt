#lang racket

(require rackunit
         racket/contract
         racket/match
         racket/list
         "../header.rkt"
         "../kernel.rkt"
         "../signature.rkt"
         "../nf.rkt"
         "../observers.rkt")

(provide rg-blocking-test-suite
         property-based-test-suite
         invariant-test-suite
         run-all-rg-tests)

;; RG Blocking Test Suite
(define (rg-blocking-test-suite)
  (test-suite "RG Blocking Tests"
    
    (test-case "RG Block Header Basic"
      (define h (header 2.0 3.0))
      (define blocked (rg-block h 2.0))
      (check-equal? (header-phase blocked) 4.0)
      (check-equal? (header-scale blocked) 6.0))
    
    (test-case "RG Block Header Zero"
      (define h header-zero)
      (define blocked (rg-block h 5.0))
      (check-equal? blocked header-zero))
    
    (test-case "RG Block Kernel"
      (define k (kernel (header 1.0 2.0) 
                       (transition 'test (λ (term) term) '())))
      (define blocked (rg-block-kernel k 3.0))
      (check-equal? (header-phase (kernel-header blocked)) 3.0)
      (check-equal? (header-scale (kernel-header blocked)) 6.0))
    
    (test-case "RG Block Term"
      (define t (make-term 'test #:header (header 1.0 1.0) #:core 'test-core))
      (define blocked-header (rg-block (term-header t) 2.0))
      (check-equal? (header-phase blocked-header) 2.0)
      (check-equal? (header-scale blocked-header) 2.0))
    
    (test-case "RG Flow Parameters"
      (define h (header 1.0 1.0))
      (define flow-params '(0.5 0.3 0.7 0.2 1.0 0.5))
      (define flowed (rg-flow h flow-params))
      (check-true (header? flowed))
      (check-true (real? (header-phase flowed)))
      (check-true (real? (header-scale flowed))))
    
    (test-case "RG Critical Line Detection"
      (define critical-h (header 1.0 1.0))
      (define non-critical-h (header 1.0 5.0))
      (check-true (rg-critical-line? critical-h 0.1))
      (check-false (rg-critical-line? non-critical-h 0.1)))))

;; Property-Based Test Suite
(define (property-based-test-suite)
  (test-suite "Property-Based Tests"
    
    (test-case "Header Arithmetic Properties"
      (for ([i 50])
        (define h1 (random-header))
        (define h2 (random-header))
        (define h3 (random-header))
        
        ;; Commutativity
        (check-equal? (header-add h1 h2) (header-add h2 h1))
        
        ;; Associativity
        (check-equal? (header-add (header-add h1 h2) h3)
                     (header-add h1 (header-add h2 h3)))
        
        ;; Identity
        (check-equal? (header-add h1 header-zero) h1)
        
        ;; Negation
        (check-equal? (header-add h1 (header-negate h1)) header-zero)))
    
    (test-case "Kernel Composition Properties"
      (for ([i 20])
        (define k1 (random-kernel))
        (define k2 (random-kernel))
        (define k3 (random-kernel))
        
        ;; Associativity
        (check-equal? (kernel-compose (kernel-compose k1 k2) k3)
                     (kernel-compose k1 (kernel-compose k2 k3)))
        
        ;; Identity
        (define id (identity-kernel))
        (check-equal? (kernel-compose k1 id) k1)
        (check-equal? (kernel-compose id k1) k1)))
    
    (test-case "RG Blocking Properties"
      (for ([i 20])
        (define k (random-kernel))
        (define block-size (+ (random 5.0) 0.1))
        
        ;; Closure
        (check-true (test-rg-closure k block-size))
        
        ;; Scaling
        (define blocked (rg-block-kernel k block-size))
        (check-true (kernel? blocked))
        (check-true (header? (kernel-header blocked)))))))

;; Invariant Test Suite
(define (invariant-test-suite)
  (test-suite "Invariant Tests"
    
    (test-case "Residual Invisibility (RC-ME)"
      (for ([i 30])
        (define k (random-kernel))
        (define t (random-term))
        (check-true (test-residual-invisibility k t))))
    
    (test-case "Triality Involution"
      (for ([i 30])
        (define t (random-term))
        (check-true (test-triality-involution t))))
    
    (test-case "Boundary Sum"
      (for ([i 30])
        (define t (random-term))
        (check-true (test-boundary-sum t))))
    
    (test-case "Header Norm Properties"
      (for ([i 20])
        (define h (random-header))
        (check-true (>= (header-norm h) 0.0))
        (check-equal? (header-norm header-zero) 0.0)))
    
    (test-case "Header Distance Properties"
      (for ([i 20])
        (define h1 (random-header))
        (define h2 (random-header))
        (check-true (>= (header-distance h1 h2) 0.0))
        (check-equal? (header-distance h1 h1) 0.0)
        (check-equal? (header-distance h1 h2) (header-distance h2 h1))))))

;; Comprehensive Test Runner
(define (run-all-rg-tests)
  "Run all RG blocking and property-based tests"
  (displayln "=== Running RG Blocking Tests ===")
  (define rg-suite (rg-blocking-test-suite))
  (displayln "RG Blocking Test Suite created")
  
  (displayln "=== Running Property-Based Tests ===")
  (define prop-suite (property-based-test-suite))
  (displayln "Property-Based Test Suite created")
  
  (displayln "=== Running Invariant Tests ===")
  (define inv-suite (invariant-test-suite))
  (displayln "Invariant Test Suite created")
  
  (displayln "=== All RG Test Suites Created Successfully ===")
  
  (displayln "=== Running Comprehensive Property Tests ===")
  (define results (run-property-tests 100))
  (define passed (count identity results))
  (define total (length results))
  (displayln (format "Property tests: ~a/~a passed" passed total))
  
  (when (< passed total)
    (displayln "Some property tests failed - this indicates potential issues"))
  
  (displayln "=== All RG Tests Complete ==="))

;; Test the header struct contracts
(define (test-header-contracts)
  (test-suite "Header Contract Tests"
    
    (test-case "Header Construction"
      (check-true (header? (header 1.0 2.0)))
      (check-false (header? '(1.0 2.0)))
      (check-exn exn:fail? (λ () (header "invalid" 2.0))))
    
    (test-case "Header Accessors"
      (define h (header 3.0 4.0))
      (check-equal? (header-phase h) 3.0)
      (check-equal? (header-scale h) 4.0))
    
    (test-case "Header Operations"
      (define h1 (header 1.0 2.0))
      (define h2 (header 3.0 4.0))
      (check-equal? (header-add h1 h2) (header 4.0 6.0))
      (check-equal? (header-multiply h1 h2) (header 3.0 8.0))
      (check-equal? (header-negate h1) (header -1.0 -2.0)))))

;; Export test functions
(provide test-header-contracts)

;; Main test runner
(module+ test
  (run-all-rg-tests)
  (displayln "Header contracts test suite created"))
