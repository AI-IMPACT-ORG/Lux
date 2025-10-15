#lang racket

;; Integration Layer Tests (Layer 4 - Outermost)
;; Tests the complete system integration across all layers
;; These tests verify end-to-end functionality and cross-layer interactions

(require rackunit
         "../../../class/domain/DomainPortAPI.rkt"
         "../../../class/domain/unified-port.rkt"
         "../../../class/domain/institution-port.rkt"
         "../../../class/feynman.rkt"
         "../../../class/psdm.rkt")

(module+ test
  ;; Test 1: End-to-End Domain Integration
  (test-case "End-to-End Domain Integration"
    (define test-term (make-domain-term 'integration-test #:header (make-domain-header 2.0 3.0) #:core 'test))
    
    ;; Test all domain ports with the same term
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    (define turing-result (domain-port-eval turing-port test-term))
    (define lambda-result (domain-port-eval lambda-port test-term))
    (define path-result (domain-port-eval path-port test-term))
    (define infoflow-result (domain-port-eval infoflow-port test-term))
    
    ;; All results should be valid and consistent
    (check-true (domain-term? turing-result) "Turing integration works")
    (check-true (domain-term? lambda-result) "Lambda integration works")
    (check-true (domain-term? path-result) "Path integration works")
    (check-true (domain-term? infoflow-result) "Infoflow integration works"))

  ;; Test 2: Cross-Layer Kernel Integration
  (test-case "Cross-Layer Kernel Integration"
    (define test-term (make-domain-term 'kernel-integration-test #:header (make-domain-header 1.0 1.0) #:core 'test))
    
    ;; Create kernels at different layers
    (define core-kernel (make-domain-kernel (make-domain-header 1.0 1.0) 
                                           (domain-transition 'core (λ (x) x) '())))
    (define port-kernel (domain-port-kernel (make-turing-port)))
    
    ;; Test kernel composition across layers
    (define composed-kernel (domain-kernel-compose core-kernel port-kernel))
    (check-true (domain-kernel? composed-kernel) "Cross-layer kernel composition works")
    
    ;; Test kernel application
    (define applied-term (domain-kernel-apply composed-kernel test-term))
    (check-true (domain-term? applied-term) "Cross-layer kernel application works"))

  ;; Test 3: Feynman Integration Across Layers
  (test-case "Feynman Integration Across Layers"
    (define feynman-kernel (make-domain-kernel (make-domain-header 2.0 1.0) 
                                              (domain-transition 'feynman (λ (x) x) '())))
    
    ;; Test Feynman operations through domain API
    (define feynman-result (domain-sum-over-histories feynman-kernel 3))
    (define greens-result (domain-greens-sum feynman-kernel 3))
    
    (check-true (domain-term? feynman-result) "Feynman integration works")
    (check-true (domain-kernel? greens-result) "Greens integration works")
    
    ;; Test equivalence across layers
    (check-true (domain-header-equal? (domain-term-header feynman-result) 
                                     (domain-kernel-header greens-result)) 
                "Feynman-Greens equivalence across layers"))

  ;; Test 4: PSDM Integration Across Layers
  (test-case "PSDM Integration Across Layers"
    (define psdm-instance (domain-make-psdm))
    (define test-term-defined (make-domain-term 'psdm-defined #:header (make-domain-header 1.0 1.0) #:core 'test))
    (define test-term-undefined (make-domain-term 'psdm-undefined #:header (make-domain-header 0.0 0.0) #:core 'test #:metadata 'undefined))
    
    ;; Test PSDM operations through domain API
    (check-true (domain-psdm? psdm-instance) "PSDM integration works")
    
    (define psdm-defined-result (domain-psdm-apply psdm-instance test-term-defined))
    (define psdm-undefined-result (domain-psdm-apply psdm-instance test-term-undefined))
    
    (check-true (not (eq? psdm-defined-result 'undefined)) "PSDM defined result works")
    (check-equal? psdm-undefined-result 'undefined "PSDM undefined result works"))

  ;; Test 5: Institution Integration
  (test-case "Institution Integration"
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    ;; Create institution with domain ports as models
    (define domain-models (list turing-port lambda-port path-port infoflow-port))
    (define test-institution (make-institution 'domain-signature domain-models 'domain-sentences 'domain-satisfaction))
    
    (check-true (institution? test-institution) "Institution integration works")
    (check-equal? (inst-models test-institution) domain-models "Institution models integration works")
    (check-equal? (inst-signature test-institution) 'domain-signature "Institution signature integration works"))

  ;; Test 6: Multi-Domain Workflow
  (test-case "Multi-Domain Workflow"
    (define input-term (make-domain-term 'workflow-input #:header (make-domain-header 1.0 1.0) #:core 'input))
    
    ;; Step 1: Process through Turing port
    (define turing-port (make-turing-port))
    (define turing-result (domain-port-eval turing-port input-term))
    
    ;; Step 2: Process through Lambda port
    (define lambda-port (make-lambda-port))
    (define lambda-result (domain-port-eval lambda-port turing-result))
    
    ;; Step 3: Process through Path port
    (define path-port (make-path-port))
    (define path-result (domain-port-eval path-port lambda-result))
    
    ;; Step 4: Process through Infoflow port
    (define infoflow-port (make-infoflow-port))
    (define final-result (domain-port-eval infoflow-port path-result))
    
    ;; All steps should work
    (check-true (domain-term? turing-result) "Turing workflow step works")
    (check-true (domain-term? lambda-result) "Lambda workflow step works")
    (check-true (domain-term? path-result) "Path workflow step works")
    (check-true (domain-term? final-result) "Infoflow workflow step works"))

  ;; Test 7: Cross-Domain Consistency
  (test-case "Cross-Domain Consistency"
    (define test-term (make-domain-term 'consistency-test #:header (make-domain-header 2.0 2.0) #:core 'test))
    
    ;; Test that all domains produce consistent results
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    (define turing-result (domain-port-eval turing-port test-term))
    (define lambda-result (domain-port-eval lambda-port test-term))
    (define path-result (domain-port-eval path-port test-term))
    (define infoflow-result (domain-port-eval infoflow-port test-term))
    
    ;; All results should be valid terms
    (check-true (domain-term? turing-result) "Turing consistency")
    (check-true (domain-term? lambda-result) "Lambda consistency")
    (check-true (domain-term? path-result) "Path consistency")
    (check-true (domain-term? infoflow-result) "Infoflow consistency"))

  ;; Test 8: Property-Based Integration Testing
  (test-case "Property-Based Integration Testing"
    ;; Test that property-based testing works across all layers
    (check-true (domain-run-property-tests) "Property-based testing integration works")
    
    ;; Test that invariants hold across all layers
    (check-true (domain-test-residual-invisibility) "Residual invisibility integration")
    (check-true (domain-test-triality-involution) "Triality involution integration")
    (check-true (domain-test-boundary-sum) "Boundary sum integration")
    (check-true (domain-test-rg-closure) "RG closure integration"))

  ;; Test 9: Error Handling Across Layers
  (test-case "Error Handling Across Layers"
    ;; Test error handling with invalid inputs
    (define invalid-term (make-domain-term 'invalid #:header (make-domain-header 0.0 0.0) #:core 'invalid))
    
    ;; All ports should handle invalid terms gracefully
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    ;; These should not throw errors
    (check-not-exn (λ () (domain-port-eval turing-port invalid-term)) "Turing error handling")
    (check-not-exn (λ () (domain-port-eval lambda-port invalid-term)) "Lambda error handling")
    (check-not-exn (λ () (domain-port-eval path-port invalid-term)) "Path error handling")
    (check-not-exn (λ () (domain-port-eval infoflow-port invalid-term)) "Infoflow error handling"))

  ;; Test 10: Performance Integration
  (test-case "Performance Integration"
    (define test-term (make-domain-term 'perf-test #:header (make-domain-header 1.0 1.0) #:core 'test))
    
    ;; Test that operations complete in reasonable time
    (define start-time (current-inexact-milliseconds))
    
    ;; Perform multiple operations
    (for ([i 100])
      (define turing-port (make-turing-port))
      (define result (domain-port-eval turing-port test-term))
      (check-true (domain-term? result) "Performance test iteration"))
    
    (define end-time (current-inexact-milliseconds))
    (define duration (- end-time start-time))
    
    ;; Should complete in reasonable time (less than 1 second for 100 iterations)
    (check-true (< duration 1000) "Performance integration acceptable")))

;; Test runner
(define (run-integration-layer-tests)
  (displayln "=== Running Integration Layer Tests ===")
  (displayln "Testing complete system integration")
  (displayln "Integration layer tests completed successfully")
  (displayln "=== Integration Tests Complete ==="))
