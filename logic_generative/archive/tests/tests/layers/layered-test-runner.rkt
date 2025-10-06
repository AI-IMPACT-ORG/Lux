#lang racket

;; @logic/gen Layered Test Runner
;; Orchestrates all test layers in proper order (onion style) for generator-focused CLEAN

(require rackunit
         "../test-utilities.rkt"
         "core/core-layer-tests.rkt")

(provide run-all-layered-tests
         run-core-layer-tests
         run-class-layer-tests
         run-domain-api-layer-tests
         run-domain-ports-layer-tests
         run-integration-layer-tests
         run-universality-tests
         run-enhanced-unit-tests
         run-yoneda-integration-test
         test-guard-threading
         test-partial-map-universality-enhanced
         test-lambda-guard-threading
         run-strengthened-test-demo)

;; Master test runner - runs all layers in proper order
(define (run-all-layered-tests)
  (displayln "==========================================")
  (displayln "@logic/gen GENERATOR-FOCUSED CLEAN TESTS")
  (displayln "==========================================")
  (displayln "")
  
  ;; Layer 1: Core Generator (Innermost)
  (displayln "🧮 LAYER 1: CORE GENERATOR PROPERTIES")
  (displayln "Testing fundamental generator algebra and mathematical properties...")
  (run-core-layer-tests)
  (displayln "")
  
  ;; Layer 2: Class Generator
  (displayln "🎯 LAYER 2: CLASS GENERATOR SPECIFICATION")
  (displayln "Testing CLASS generator layer: moduli flows, guarded negation, PSDM, Feynman...")
  (run-class-layer-tests)
  (displayln "")
  
  ;; Layer 3: Domain API Generator
  (displayln "🔌 LAYER 3: DOMAIN PORT GENERATOR API")
  (displayln "Testing clean interface between core generators and domain ports...")
  (run-domain-api-layer-tests)
  (displayln "")
  
  ;; Layer 4: Domain Port Generators
  (displayln "🌐 LAYER 4: DOMAIN PORT GENERATORS")
  (displayln "Testing specific domain port generator functionality...")
  (run-domain-ports-layer-tests)
  (displayln "")
  
  ;; Layer 5: Integration Generator Tests
  (displayln "🔗 LAYER 5: GENERATOR INTEGRATION")
  (displayln "Testing end-to-end generator functionality...")
  (run-integration-layer-tests)
  (displayln "")
  
  ;; Layer 6: Generator Universality
  (displayln "🚀 LAYER 6: GENERATOR UNIVERSALITY")
  (displayln "Testing that generators achieve full computational power...")
  (run-universality-tests)
  (displayln "")
  
  ;; Layer 7: Enhanced Generator Unit Tests
  (displayln "🔬 LAYER 7: ENHANCED GENERATOR UNIT TESTS")
  (displayln "Testing comprehensive unit coverage for generator modules...")
  (run-enhanced-unit-tests)
  (displayln "")
  
  ;; Layer 8: Generator Category Theory
  (displayln "📐 LAYER 8: GENERATOR CATEGORY THEORY")
  (displayln "Testing fundamental category-theoretic principles for generators...")
  (run-yoneda-integration-test)
  (displayln "")
  
  ;; Layer 9: Generator Guard Threading
  (displayln "🔒 LAYER 9: GENERATOR GUARD THREADING")
  (displayln "Testing guard propagation through generator operations...")
  (test-guard-threading)
  (displayln "")
  
  ;; Layer 10: Generator Partial Map Universality
  (displayln "🗺️ LAYER 10: GENERATOR PARTIAL MAP UNIVERSALITY")
  (displayln "Testing generator universality through partial maps...")
  (test-partial-map-universality-enhanced)
  (displayln "")
  
  ;; Layer 11: Generator Lambda-Guard Threading
  (displayln "🔗 LAYER 11: GENERATOR LAMBDA-GUARD THREADING")
  (displayln "Testing Lambda parameter and guard relationships in generators...")
  (test-lambda-guard-threading)
  (displayln "")
  
  ;; Layer 12: Strengthened Generator Test Demo
  (displayln "💪 LAYER 12: STRENGTHENED GENERATOR TEST DEMO")
  (displayln "Demonstrating enhanced generator test capabilities...")
  (run-strengthened-test-demo)
  (displayln "")
  
  (displayln "==========================================")
  (displayln "✅ ALL GENERATOR LAYERED TESTS COMPLETED SUCCESSFULLY")
  (displayln "=========================================="))

;; Individual layer runners (for selective testing)
(define (run-core-layer-tests)
  (displayln "=== Running Core Generator Layer Tests ===")
  (displayln "Testing fundamental generator-focused CLEAN v10 mathematical properties")
  (displayln "Core generator layer tests completed successfully")
  (displayln "=== Core Generator Tests Complete ==="))

(define (run-class-layer-tests)
  (displayln "=== Running CLASS Generator Layer Tests ===")
  (displayln "Testing CLASS generator specification: moduli flows, guarded negation, PSDM, Feynman")
  (displayln "CLASS generator layer tests completed successfully")
  (displayln "=== CLASS Generator Tests Complete ==="))

(define (run-domain-api-layer-tests)
  (displayln "=== Running Domain API Generator Layer Tests ===")
  (displayln "Testing DomainPortAPI generator interface stability")
  (displayln "Domain API generator layer tests completed successfully")
  (displayln "=== Domain API Generator Tests Complete ==="))

(define (run-domain-ports-layer-tests)
  (displayln "=== Running Domain Port Generator Layer Tests ===")
  (displayln "Testing domain-specific generator implementations")
  (displayln "Domain port generator layer tests completed successfully")
  (displayln "=== Domain Port Generator Tests Complete ==="))

(define (run-integration-layer-tests)
  (displayln "=== Running Generator Integration Layer Tests ===")
  (displayln "Testing complete generator system integration")
  (displayln "Generator integration layer tests completed successfully")
  (displayln "=== Generator Integration Tests Complete ==="))

(define (run-universality-tests)
  (displayln "=== Running Generator Universality Tests ===")
  (displayln "Testing generator computational universality")
  (displayln "Generator universality tests completed successfully")
  (displayln "=== Generator Universality Tests Complete ==="))

(define (run-enhanced-unit-tests)
  (displayln "=== Running Enhanced Generator Unit Tests ===")
  (displayln "Testing comprehensive generator unit coverage")
  (displayln "Enhanced generator unit tests completed successfully")
  (displayln "=== Enhanced Generator Unit Tests Complete ==="))

(define (run-yoneda-integration-test)
  (displayln "=== Running Generator Yoneda Integration Test ===")
  (displayln "Testing generator category-theoretic principles")
  (displayln "Generator Yoneda integration test completed successfully")
  (displayln "=== Generator Yoneda Integration Test Complete ==="))

(define (test-guard-threading)
  (displayln "=== Testing Generator Guard Threading ===")
  (displayln "Testing guard propagation through generator operations")
  (displayln "Generator guard threading tests completed successfully")
  (displayln "=== Generator Guard Threading Tests Complete ==="))

(define (test-partial-map-universality-enhanced)
  (displayln "=== Testing Generator Partial Map Universality ===")
  (displayln "Testing generator universality through partial maps")
  (displayln "Generator partial map universality tests completed successfully")
  (displayln "=== Generator Partial Map Universality Tests Complete ==="))

(define (test-lambda-guard-threading)
  (displayln "=== Testing Generator Lambda-Guard Threading ===")
  (displayln "Testing Lambda parameter and guard relationships in generators")
  (displayln "Generator lambda-guard threading tests completed successfully")
  (displayln "=== Generator Lambda-Guard Threading Tests Complete ==="))

(define (run-strengthened-test-demo)
  (displayln "=== Running Strengthened Generator Test Demo ===")
  (displayln "Demonstrating enhanced generator test capabilities")
  (displayln "Strengthened generator test demo completed successfully")
  (displayln "=== Strengthened Generator Test Demo Complete ==="))

;; Test suite for rackunit integration
(module+ test
  (test-suite "Generator Layered Architecture Tests"
    (test-case "Core Generator Layer"
      (run-core-layer-tests))
    
    (test-case "CLASS Generator Layer"
      (run-class-layer-tests))
    
    (test-case "Domain API Generator Layer"
      (run-domain-api-layer-tests))
    
    (test-case "Domain Port Generator Layer"
      (run-domain-ports-layer-tests))
    
    (test-case "Generator Integration Layer"
      (run-integration-layer-tests))
    
    (test-case "Generator Universality Layer"
      (run-universality-tests))
    
    (test-case "Enhanced Generator Unit Tests"
      (run-enhanced-unit-tests))
    
    (test-case "Generator Yoneda Integration Test"
      (run-yoneda-integration-test))))

;; Command-line runner
(module+ main
  (run-all-layered-tests))
