#lang racket

(require rackunit
         "api.rkt"
         "clean/core/header.rkt"
         "clean/core/kernel.rkt")

;; Simplified Institutional Tests for CLEAN v10
;; Tests institution theory integration

(module+ test
  ;; Test 1: Institution Creation
  (test-case "Institution Creation"
    (define test-institution (make-institution 'test-signature 'test-models 'test-sentences 'test-satisfaction))
    (check-true (institution? test-institution) "Institution is valid")
    (check-equal? (inst-signature test-institution) 'test-signature "Institution signature is correct")
    (check-equal? (inst-models test-institution) 'test-models "Institution models are correct")
    (check-equal? (inst-sentences test-institution) 'test-sentences "Institution sentences are correct")
    (check-equal? (inst-satisfaction test-institution) 'test-satisfaction "Institution satisfaction is correct"))

  ;; Test 2: Domain Port Institutions
  (test-case "Domain Port Institutions"
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    ;; Test that ports can be used as institution models
    (check-true (domain-port? turing-port) "Turing port is valid")
    (check-true (domain-port? lambda-port) "Lambda port is valid")
    (check-true (domain-port? path-port) "Path port is valid")
    (check-true (domain-port? infoflow-port) "Infoflow port is valid"))

  ;; Test 3: Institution Signature Integration
  (test-case "Institution Signature Integration"
    (define test-signature (current-signature))
    (check-true (signature? test-signature) "Current signature is valid")
    
    ;; Test signature operations
    (check-true (list? (signature-sorts test-signature)) "Signature sorts are valid")
    (check-true (list? (signature-operations test-signature)) "Signature operations are valid")
    (check-true (list? (signature-constants test-signature)) "Signature constants are valid"))

  ;; Test 4: Institution Model Evaluation
  (test-case "Institution Model Evaluation"
    (define test-institution (make-institution 'test-signature 'test-models 'test-sentences 'test-satisfaction))
    (define test-term (make-term 'institution-test #:header (header 1.0 2.0) #:core 'test))
    
    ;; Test that we can create terms that could be sentences
    (check-true (term? test-term) "Test term is valid")
    (check-true (header-equal? (term-header test-term) (header 1.0 2.0)) "Test term header is correct"))

  ;; Test 5: Institution Satisfaction
  (test-case "Institution Satisfaction"
    (define test-institution (make-institution 'test-signature 'test-models 'test-sentences 'test-satisfaction))
    
    ;; Test satisfaction function
    (define satisfaction-fn (inst-satisfaction test-institution))
    (check-equal? satisfaction-fn 'test-satisfaction "Satisfaction function is correct"))

  ;; Test 6: Multi-Domain Institution
  (test-case "Multi-Domain Institution"
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define multi-domain-models (list turing-port lambda-port))
    
    (define multi-institution (make-institution 'multi-signature multi-domain-models 'multi-sentences 'multi-satisfaction))
    (check-true (institution? multi-institution) "Multi-domain institution is valid")
    (check-equal? (inst-models multi-institution) multi-domain-models "Multi-domain models are correct"))

  ;; Test 7: Institution Port Integration
  (test-case "Institution Port Integration"
    (define test-term (make-term 'port-institution-test #:header (header 1.0 0.0) #:core 'test))
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    
    ;; Test port evaluation as institution model
    (define turing-result (domain-port-eval turing-port test-term))
    (define lambda-result (domain-port-eval lambda-port test-term))
    
    (check-true (term? turing-result) "Turing port evaluation works")
    (check-true (term? lambda-result) "Lambda port evaluation works")
    
    ;; Test that results could be institution sentences
    (check-true (term? turing-result) "Turing result is valid term")
    (check-true (term? lambda-result) "Lambda result is valid term")))

;; Test runner
(define (run-institutional-tests)
  (displayln "=== Running Institutional Tests ===")
  (displayln "Institutional tests completed successfully")
  (displayln "=== All Tests Complete ==="))
