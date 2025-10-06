#lang racket

;; @logic/gen Enhanced Test Suite
;; Comprehensive tests for generator-focused CLEAN language with enhanced coverage

(require rackunit
         "test-utilities.rkt"
         "layers/layered-test-runner.rkt"
         "../core.rkt"
         "../truth.rkt"
         "../rg.rkt"
         "../ports/boolean.rkt")

(provide (all-defined-out))

;; ============================================================================
;; ENHANCED GENERATOR UNIT TESTS
;; ============================================================================

(define-test-suite enhanced-generator-unit-tests
  "Enhanced generator unit tests with comprehensive coverage"
  
  (test-case "Generator Identity Properties"
    (define id (gen-id))
    (check-true (gen? id) "Identity generator exists")
    (check-equal? (gen-apply id 42) 42 "Identity preserves values")
    (check-equal? (gen-apply id 'test) 'test "Identity preserves symbols")
    (check-equal? (gen-apply id '(a b c)) '(a b c) "Identity preserves lists"))
  
  (test-case "Generator Composition Properties"
    (define inc (make-gen add1 'increment '(monotonic)))
    (define double (make-gen (λ (x) (* 2 x)) 'double '(linear)))
    (define triple (make-gen (λ (x) (* 3 x)) 'triple '(linear)))
    
    ;; Test basic composition
    (define inc-then-double (gen-compose double inc))
    (check-equal? (gen-apply inc-then-double 5) 12 "Basic composition works")
    
    ;; Test associativity
    (check-true (test-associativity inc double triple) "Composition associativity")
    
    ;; Test identity laws
    (check-true (test-identity inc) "Left identity law")
    (check-true (test-identity double) "Right identity law"))
  
  (test-case "Generator Powers and Iteration"
    (define inc (make-gen add1 'increment '(monotonic)))
    
    ;; Test powers
    (check-equal? (gen-apply (gen-power inc 0) 5) 5 "Power 0 is identity")
    (check-equal? (gen-apply (gen-power inc 1) 5) 6 "Power 1 is original")
    (check-equal? (gen-apply (gen-power inc 3) 5) 8 "Power 3 works")
    (check-equal? (gen-apply (gen-power inc 10) 0) 10 "Power 10 works"))
  
  (test-case "Green's Sum Generator"
    (define inc (make-gen add1 'increment '(monotonic)))
    
    ;; Test Green's sum with different N
    (check-equal? (gen-apply (greens-sum-generator inc 0) 0) 0 "Green's sum N=0")
    (check-equal? (gen-apply (greens-sum-generator inc 1) 0) 1 "Green's sum N=1")
    (check-equal? (gen-apply (greens-sum-generator inc 3) 0) 6 "Green's sum N=3")
    (check-equal? (gen-apply (greens-sum-generator inc 5) 0) 15 "Green's sum N=5")
    (check-equal? (gen-apply (greens-sum-generator inc 10) 0) 55 "Green's sum N=10"))
  
  (test-case "RG Blocking Generator"
    (define scale (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    
    ;; Test RG blocking with different k
    (check-equal? (gen-apply (rg-block-generator scale 1) 5) 10 "RG blocking k=1")
    (check-equal? (gen-apply (rg-block-generator scale 2) 5) 20 "RG blocking k=2")
    (check-equal? (gen-apply (rg-block-generator scale 3) 5) 40 "RG blocking k=3")
    
    ;; Test RG closure
    (check-true (test-rg-closure scale) "RG closure property"))
  
  (test-case "Flow Convergence Generator"
    (define f (λ (x) (/ (+ x (/ 2 x)) 2)))  ; Newton's method for sqrt(2)
    (define conv-gen (flow-convergence-generator f 0.001 100))
    
    (check-true (gen? conv-gen) "Convergence generator exists")
    (check-true (test-flow-convergence f 1.0 0.001 100) "Flow convergence works")
    (check-true (test-flow-convergence-properties) "Convergence properties"))
  
  (test-case "Fixed Point Generator"
    (define cos-f (λ (x) (cos x)))
    (define fp-gen (fixed-point-generator cos-f 0.001))
    
    (check-true (gen? fp-gen) "Fixed point generator exists")
    (check-true (test-fixed-point-properties) "Fixed point properties"))
  
  (test-case "Moduli Flow Generator"
    (define flow1 (make-moduli-flow 1 2 3 4))
    (define flow2 (make-moduli-flow 5 6 7 8))
    
    ;; Test moduli flow properties
    (check-true (moduli-flow? flow1) "Moduli flow 1 exists")
    (check-true (moduli-flow? flow2) "Moduli flow 2 exists")
    
    ;; Test composition
    (define composed (compose-moduli-flows flow1 flow2))
    (check-equal? (moduli-flow-μL composed) 6 "Moduli flow μL composition")
    (check-equal? (moduli-flow-θL composed) 8 "Moduli flow θL composition")
    (check-equal? (moduli-flow-μR composed) 10 "Moduli flow μR composition")
    (check-equal? (moduli-flow-θR composed) 12 "Moduli flow θR composition"))
  
  (test-case "Domain Port Generator Properties"
    (define B (make-boolean-port))
    (define L (make-lambda-port))
    (define I (make-infoflow-port))
    (define Q (make-qft-port))
    
    ;; Test port creation
    (check-true (domain-port-gen? B) "Boolean port exists")
    (check-true (domain-port-gen? L) "Lambda port exists")
    (check-true (domain-port-gen? I) "InfoFlow port exists")
    (check-true (domain-port-gen? Q) "QFT port exists")
    
    ;; Test port coherence
    (check-true (validate-domain-port-coherence B) "Boolean port coherence")
    (check-true (validate-domain-port-coherence L) "Lambda port coherence")
    (check-true (validate-domain-port-coherence I) "InfoFlow port coherence")
    (check-true (validate-domain-port-coherence Q) "QFT port coherence")
    
    ;; Test q-vectors
    (check-equal? (domain-port-gen-q-vector B) '(1 0 0) "Boolean port q-vector")
    (check-equal? (domain-port-gen-q-vector L) '(0 1 0) "Lambda port q-vector")
    (check-equal? (domain-port-gen-q-vector I) '(0 0 0) "InfoFlow port q-vector")
    (check-equal? (domain-port-gen-q-vector Q) '(0 0 1) "QFT port q-vector"))
  
  (test-case "Domain Port Evaluation"
    (define B (make-boolean-port))
    (define L (make-lambda-port))
    
    ;; Test PSDM definedness
    (check-true (psdm-defined? B 1) "Boolean port defined for 1")
    (check-true (psdm-defined? B 'test) "Boolean port defined for symbol")
    (check-false (psdm-defined? B 'non-halting) "Boolean port undefined for non-halting")
    
    (check-true (psdm-defined? L 'lambda) "Lambda port defined for lambda")
    (check-true (psdm-defined? L 'halt) "Lambda port defined for halt")
    (check-false (psdm-defined? L 'infinite-loop) "Lambda port undefined for infinite-loop")
    
    ;; Test port evaluation
    (when (psdm-defined? B 42)
      (check-equal? (domain-port-eval B 42) 42 "Boolean port evaluation"))
    
    (when (psdm-defined? L 'test)
      (check-equal? (domain-port-eval L 'test) 'test "Lambda port evaluation")))
  
  (test-case "Domain Port Composition"
    (define B (make-boolean-port))
    (define L (make-lambda-port))
    (define BL (compose-domain-ports B L))
    
    (check-true (domain-port-gen? BL) "Composed port exists")
    (check-equal? (domain-port-gen-q-vector BL) '(1 1 0) "Composed port q-vector")
    (check-true (validate-domain-port-coherence BL) "Composed port coherence"))
  
  (test-case "Generator Metadata and Laws"
    (define g (make-gen (λ (x) (* 2 x)) 'double '(linear monotonic)))
    
    ;; Test metadata access
    (check-equal? (gen-tag g) 'double "Generator tag")
    (check-equal? (gen-laws g) '(linear monotonic) "Generator laws")
    
    ;; Test equality
    (define g2 (make-gen (λ (x) (* 2 x)) 'double '(linear monotonic)))
    (check-true (gen-equal? g g2) "Generator equality")
    
    ;; Test string representation
    (check-true (string? (gen->string g)) "Generator string representation"))
  
  (test-case "Property-Based Testing"
    (define test-count 100)
    (for ([i test-count])
      (define g1 (generate-test-generator (string->symbol (format "gen1-~a" i)) '(test)))
      (define g2 (generate-test-generator (string->symbol (format "gen2-~a" i)) '(test)))
      (define g3 (generate-test-generator (string->symbol (format "gen3-~a" i)) '(test)))
      
      ;; Test associativity
      (check-true (test-associativity g1 g2 g3) 
                  (format "Associativity failed for generators ~a, ~a, ~a" g1 g2 g3))
      
      ;; Test identity laws
      (check-true (test-identity g1)
                  (format "Identity law failed for generator ~a" g1))
      
      ;; Test composition
      (check-true (test-generator-composition g1 g2)
                  (format "Composition failed for generators ~a, ~a" g1 g2))
      
      ;; Test powers
      (check-true (test-generator-powers g1 3)
                  (format "Powers failed for generator ~a" g1))
      
      ;; Test Green's sum
      (check-true (test-greens-sum g1 5)
                  (format "Green's sum failed for generator ~a" g1))
      
      ;; Test RG blocking
      (check-true (test-rg-blocking g1 2)
                  (format "RG blocking failed for generator ~a" g1))))
  
  (test-case "Edge Cases and Error Handling"
    ;; Test edge cases for Green's sum
    (define inc (make-gen add1 'increment '(monotonic)))
    (check-equal? (gen-apply (greens-sum-generator inc 0) 5) 5 "Green's sum N=0 edge case")
    
    ;; Test edge cases for RG blocking
    (define scale (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    (check-equal? (gen-apply (rg-block-generator scale 1) 5) 10 "RG blocking k=1 edge case")
    
    ;; Test error handling
    (check-exn exn:fail? (λ () (greens-sum-generator inc -1)) "Negative N error")
    (check-exn exn:fail? (λ () (rg-block-generator scale 0)) "Zero k error")
    (check-exn exn:fail? (λ () (rg-block-generator scale -1)) "Negative k error"))
  
  (test-case "Systematic Validation"
    ;; Test systematic validation
    (check-true (validate-systematic-properties #:iterations 50) 
                "Systematic validation passes")
    
    ;; Test all property functions
    (check-true (test-generator-algebra-properties) "Generator algebra properties")
    (check-true (test-domain-properties) "Domain properties")
    (check-true (test-flow-convergence-properties) "Flow convergence properties")
    (check-true (test-fixed-point-properties) "Fixed point properties")))

;; ============================================================================
;; INTEGRATION TEST SUITE
;; ============================================================================

(define-test-suite integration-tests
  "Integration tests for complete generator workflows"
  
  (test-case "Complete Generator Workflow"
    ;; Create generators
    (define K (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    (define L (make-gen add1 'increment '(monotonic)))
    
    ;; Generate Green's sum
    (define G3 (greens-sum-generator K 3))
    
    ;; Apply RG blocking
    (define K-blocked (rg-block-generator K 2))
    
    ;; Test with domain port
    (define B (make-boolean-port))
    (define test-term 5)
    
    (when (psdm-defined? B test-term)
      (define result (domain-port-eval B test-term))
      (check-equal? result test-term "Complete workflow result"))
    
    ;; Test generator composition
    (define KL (gen-compose K L))
    (check-equal? (gen-apply KL 5) 12 "Generator composition in workflow"))
  
  (test-case "Moduli Flow Workflow"
    ;; Create moduli flows
    (define flow1 (make-moduli-flow 1 2 3 4))
    (define flow2 (make-moduli-flow 5 6 7 8))
    
    ;; Compose flows
    (define composed (compose-moduli-flows flow1 flow2))
    
    ;; Verify composition
    (check-equal? (moduli-flow-μL composed) 6 "Moduli flow μL composition")
    (check-equal? (moduli-flow-θL composed) 8 "Moduli flow θL composition")
    (check-equal? (moduli-flow-μR composed) 10 "Moduli flow μR composition")
    (check-equal? (moduli-flow-θR composed) 12 "Moduli flow θR composition"))
  
  (test-case "Domain Port Workflow"
    ;; Create domain ports
    (define B (make-boolean-port))
    (define L (make-lambda-port))
    (define I (make-infoflow-port))
    (define Q (make-qft-port))
    
    ;; Test port evaluation workflow
    (define test-terms '(1 'test "string" '(a b c)))
    
    (for ([term test-terms])
      (when (psdm-defined? B term)
        (define result (domain-port-eval B term))
        (check-equal? result term "Boolean port workflow"))
      
      (when (psdm-defined? L term)
        (define result (domain-port-eval L term))
        (check-equal? result term "Lambda port workflow")))
    
    ;; Test port composition workflow
    (define BL (compose-domain-ports B L))
    (define BI (compose-domain-ports B I))
    (define LQ (compose-domain-ports L Q))
    
    (check-true (domain-port-gen? BL) "Boolean-Lambda composition")
    (check-true (domain-port-gen? BI) "Boolean-InfoFlow composition")
    (check-true (domain-port-gen? LQ) "Lambda-QFT composition")))

;; ============================================================================
;; COMPLETE TEST SUITE
;; ============================================================================

(define-test-suite logic-gen-enhanced-tests
  "Complete @logic/gen enhanced test suite"
  enhanced-generator-unit-tests
  integration-tests)

;; ============================================================================
;; TEST RUNNER
;; ============================================================================

(define (run-enhanced-unit-tests)
  "Run enhanced generator unit tests"
  (displayln "=== Running Enhanced Generator Unit Tests ===")
  (run-tests enhanced-generator-unit-tests)
  (displayln "=== Enhanced Generator Unit Tests Complete ==="))

(define (run-integration-tests)
  "Run generator integration tests"
  (displayln "=== Running Generator Integration Tests ===")
  (run-tests integration-tests)
  (displayln "=== Generator Integration Tests Complete ==="))

(define (run-all-enhanced-tests)
  "Run all enhanced tests"
  (displayln "=== Running All Enhanced Generator Tests ===")
  (run-tests logic-gen-enhanced-tests)
  (displayln "=== All Enhanced Generator Tests Complete ==="))

;; Run tests if this file is executed directly
(when (equal? (current-command-line-arguments) '())
  (run-all-enhanced-tests))

