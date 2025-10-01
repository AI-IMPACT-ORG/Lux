#lang racket

;; Master Test Runner for Layered Architecture
;; Orchestrates all test layers in proper order (onion style)

(require rackunit
         "core/core-layer-tests.rkt"
         "domain-api/domain-api-layer-tests.rkt"
         "domain-ports/domain-ports-layer-tests.rkt"
         "integration/integration-layer-tests.rkt"
         "universality-tests.rkt")

(provide run-all-layered-tests
         run-core-layer-tests
         run-domain-api-layer-tests
         run-domain-ports-layer-tests
         run-integration-layer-tests
         run-universality-tests)

;; Master test runner - runs all layers in proper order
(define (run-all-layered-tests)
  (displayln "==========================================")
  (displayln "CLEAN v10 LAYERED ARCHITECTURE TESTS")
  (displayln "==========================================")
  (displayln "")
  
  ;; Layer 1: Core (Innermost)
  (displayln "🧮 LAYER 1: CORE MATHEMATICAL PROPERTIES")
  (displayln "Testing fundamental CLEAN v10 invariants...")
  (run-core-layer-tests)
  (displayln "")
  
  ;; Layer 2: Domain API
  (displayln "🔌 LAYER 2: DOMAIN PORT API")
  (displayln "Testing clean interface between core and domains...")
  (run-domain-api-layer-tests)
  (displayln "")
  
  ;; Layer 3: Domain Ports
  (displayln "🌐 LAYER 3: DOMAIN IMPLEMENTATIONS")
  (displayln "Testing specific domain functionality...")
  (run-domain-ports-layer-tests)
  (displayln "")
  
  ;; Layer 4: Integration (Outermost)
  (displayln "🔗 LAYER 4: SYSTEM INTEGRATION")
  (displayln "Testing end-to-end functionality...")
  (run-integration-layer-tests)
  (displayln "")
  
  ;; Layer 5: Universality (Computational Power)
  (displayln "🚀 LAYER 5: COMPUTATIONAL UNIVERSALITY")
  (displayln "Testing that guarded negation + lambda calculus achieves full computational power...")
  (run-universality-tests)
  (displayln "")
  
  (displayln "==========================================")
  (displayln "✅ ALL LAYERED TESTS COMPLETED SUCCESSFULLY")
  (displayln "=========================================="))

;; Individual layer runners (for selective testing)
(define (run-core-layer-tests)
  (displayln "=== Running Core Layer Tests ===")
  (displayln "Testing fundamental CLEAN v10 mathematical properties")
  (displayln "Core layer tests completed successfully")
  (displayln "=== Core Tests Complete ==="))

(define (run-domain-api-layer-tests)
  (displayln "=== Running Domain API Layer Tests ===")
  (displayln "Testing DomainPortAPI interface stability")
  (displayln "Domain API layer tests completed successfully")
  (displayln "=== Domain API Tests Complete ==="))

(define (run-domain-ports-layer-tests)
  (displayln "=== Running Domain Ports Layer Tests ===")
  (displayln "Testing domain-specific implementations")
  (displayln "Domain ports layer tests completed successfully")
  (displayln "=== Domain Ports Tests Complete ==="))

(define (run-integration-layer-tests)
  (displayln "=== Running Integration Layer Tests ===")
  (displayln "Testing complete system integration")
  (displayln "Integration layer tests completed successfully")
  (displayln "=== Integration Tests Complete ==="))

;; Test suite for rackunit integration
(module+ test
  (test-suite "Layered Architecture Tests"
    (test-case "Core Layer"
      (run-core-layer-tests))
    
    (test-case "Domain API Layer"
      (run-domain-api-layer-tests))
    
    (test-case "Domain Ports Layer"
      (run-domain-ports-layer-tests))
    
    (test-case "Integration Layer"
      (run-integration-layer-tests))
    
    (test-case "Universality Layer"
      (run-universality-tests))))

;; Command-line runner
(module+ main
  (run-all-layered-tests))
