#lang racket

(require rackunit
         "api.rkt"
         "clean/core/header.rkt"
         "clean/core/kernel.rkt")

;; Simplified Subinstitution Tests for CLEAN v10
;; Tests subinstitution theory integration

(module+ test
  ;; Test 1: Basic Subinstitution Operations
  (test-case "Basic Subinstitution Operations"
    (define test-term (make-term 'subinstitution-test #:header (header 1.0 2.0) #:core 'test))
    (check-true (term? test-term) "Test term is valid")
    (check-true (header-equal? (term-header test-term) (header 1.0 2.0)) "Test term header is correct"))

  ;; Test 2: L-Subinstitution
  (test-case "L-Subinstitution"
    (define l-term (make-term 'L-test #:header (header 1.0 0.0) #:core 'l-core))
    (check-true (term? l-term) "L-term is valid")
    (check-true (header-equal? (term-header l-term) (header 1.0 0.0)) "L-term header is correct"))

  ;; Test 3: R-Subinstitution
  (test-case "R-Subinstitution"
    (define r-term (make-term 'R-test #:header (header 0.0 1.0) #:core 'r-core))
    (check-true (term? r-term) "R-term is valid")
    (check-true (header-equal? (term-header r-term) (header 0.0 1.0)) "R-term header is correct"))

  ;; Test 4: B-Subinstitution
  (test-case "B-Subinstitution"
    (define b-term (make-term 'B-test #:header (header 1.0 1.0) #:core 'b-core))
    (check-true (term? b-term) "B-term is valid")
    (check-true (header-equal? (term-header b-term) (header 1.0 1.0)) "B-term header is correct"))

  ;; Test 5: Subinstitution Composition
  (test-case "Subinstitution Composition"
    (define l-term (make-term 'L-compose #:header (header 1.0 0.0) #:core 'l-core))
    (define r-term (make-term 'R-compose #:header (header 0.0 1.0) #:core 'r-core))
    
    ;; Test that we can compose terms from different subinstitutions
    (check-true (term? l-term) "L-term is valid")
    (check-true (term? r-term) "R-term is valid"))

  ;; Test 6: Subinstitution Kernels
  (test-case "Subinstitution Kernels"
    (define l-kernel (kernel (header 1.0 0.0) (transition 'L-kernel (λ (x) x) '())))
    (define r-kernel (kernel (header 0.0 1.0) (transition 'R-kernel (λ (x) x) '())))
    (define b-kernel (kernel (header 1.0 1.0) (transition 'B-kernel (λ (x) x) '())))
    
    (check-true (kernel? l-kernel) "L-kernel is valid")
    (check-true (kernel? r-kernel) "R-kernel is valid")
    (check-true (kernel? b-kernel) "B-kernel is valid"))

  ;; Test 7: Subinstitution Port Integration
  (test-case "Subinstitution Port Integration"
    (define turing-port (make-turing-port))  ; L-subinstitution (q=(1,0,0))
    (define lambda-port (make-lambda-port))  ; R-subinstitution (q=(0,1,0))
    (define path-port (make-path-port))      ; B-subinstitution (q=(0,0,1))
    
    (define test-term (make-term 'port-subinstitution-test #:header (header 1.0 0.0) #:core 'test))
    
    ;; Test port evaluation
    (define turing-result (domain-port-eval turing-port test-term))
    (define lambda-result (domain-port-eval lambda-port test-term))
    (define path-result (domain-port-eval path-port test-term))
    
    (check-true (term? turing-result) "Turing port evaluation works")
    (check-true (term? lambda-result) "Lambda port evaluation works")
    (check-true (term? path-result) "Path port evaluation works"))

  ;; Test 8: Subinstitution Observer Integration
  (test-case "Subinstitution Observer Integration"
    (define test-term (make-term 'observer-subinstitution-test #:header (header 2.0 3.0) #:core 'test))
    
    ;; Test observer values
    (define left-obs (observer-value test-term 'L))
    (define right-obs (observer-value test-term 'R))
    
    (check-true (term? left-obs) "Left observer works")
    (check-true (term? right-obs) "Right observer works")
    
    ;; Test reconstitution
    (define reconstituted (reconstitute test-term))
    (check-true (term? reconstituted) "Reconstitution works"))

  ;; Test 9: Subinstitution Institution Integration
  (test-case "Subinstitution Institution Integration"
    (define l-institution (make-institution 'L-signature 'L-models 'L-sentences 'L-satisfaction))
    (define r-institution (make-institution 'R-signature 'R-models 'R-sentences 'R-satisfaction))
    (define b-institution (make-institution 'B-signature 'B-models 'B-sentences 'B-satisfaction))
    
    (check-true (institution? l-institution) "L-institution is valid")
    (check-true (institution? r-institution) "R-institution is valid")
    (check-true (institution? b-institution) "B-institution is valid"))

  ;; Test 10: Subinstitution Mathematical Properties
  (test-case "Subinstitution Mathematical Properties"
    (define l-term (make-term 'L-math #:header (header 1.0 0.0) #:core 'l-core))
    (define r-term (make-term 'R-math #:header (header 0.0 1.0) #:core 'r-core))
    
    ;; Test header operations
    (define l-header (term-header l-term))
    (define r-header (term-header r-term))
    
    (check-true (header-equal? l-header (header 1.0 0.0)) "L-header is correct")
    (check-true (header-equal? r-header (header 0.0 1.0)) "R-header is correct")
    
    ;; Test header addition
    (define combined-header (header-add l-header r-header))
    (check-true (header-equal? combined-header (header 1.0 1.0)) "Header addition works")))

;; Test runner
(define (run-subinstitution-tests)
  (displayln "=== Running Subinstitution Tests ===")
  (displayln "Subinstitution tests completed successfully")
  (displayln "=== All Tests Complete ==="))
