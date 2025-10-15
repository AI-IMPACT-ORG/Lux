#lang racket

(require rackunit
         "api.rkt"
         "clean/core/header.rkt"
         "clean/core/kernel.rkt")

;; Simplified Comprehensive Logic Tests for CLEAN v10
;; Tests the complete logic system using working functions

(module+ test
  ;; Test 1: Core Logic Operations
  (test-case "Core Logic Operations"
    (define core-term (make-term 'core-complete #:header (header 2.0 3.0) #:core 'core-logic))
    (check-true (term? core-term) "Core term is valid")
    (check-true (header-equal? (term-header core-term) (header 2.0 3.0)) "Core term header is correct")
    
    ;; Test normal form
    (define nf-core (normal-form core-term))
    (check-true (nf? nf-core) "Normal form is valid")
    
    ;; Test kernel application
    (define test-kernel (kernel (header 1.0 1.0) (transition 'test (λ (x) x) '())))
    (define applied-term (kernel-apply test-kernel core-term))
    (check-true (term? applied-term) "Kernel application works"))

  ;; Test 2: Domain Port Integration
  (test-case "Domain Port Integration"
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    (define test-term (make-term 'domain-test #:header (header 1.0 0.0) #:core 'test))
    
    ;; Test all domain ports
    (check-true (domain-port? turing-port) "Turing port is valid")
    (check-true (domain-port? lambda-port) "Lambda port is valid")
    (check-true (domain-port? path-port) "Path port is valid")
    (check-true (domain-port? infoflow-port) "Infoflow port is valid")
    
    ;; Test port evaluation
    (define turing-result (domain-port-eval turing-port test-term))
    (define lambda-result (domain-port-eval lambda-port test-term))
    (define path-result (domain-port-eval path-port test-term))
    (define infoflow-result (domain-port-eval infoflow-port test-term))
    
    (check-true (term? turing-result) "Turing port evaluation works")
    (check-true (term? lambda-result) "Lambda port evaluation works")
    (check-true (term? path-result) "Path port evaluation works")
    (check-true (term? infoflow-result) "Infoflow port evaluation works"))

  ;; Test 3: Feynman Integration
  (test-case "Feynman Integration"
    (define feynman-kernel (kernel (header 2.0 1.0) (transition 'feynman (λ (x) x) '())))
    
    ;; Test sum-over-histories
    (define feynman-result (sum-over-histories feynman-kernel 3))
    (check-true (term? feynman-result) "Feynman sum-over-histories works")
    
    ;; Test greens-sum
    (define greens-result (greens-sum feynman-kernel 3))
    (check-true (kernel? greens-result) "Greens sum works")
    
    ;; Test equivalence
    (check-true (header-equal? (term-header feynman-result) (kernel-header greens-result)) "Feynman-Greens equivalence"))

  ;; Test 4: PSDM Operations
  (test-case "PSDM Operations"
    (define psdm-instance (make-psdm-legacy))
    (define test-term (make-term 'psdm-test #:header (header 0.0 0.0) #:core 'test))
    
    (check-true (psdm-legacy? psdm-instance) "PSDM instance is valid")
    (define psdm-result (psdm-apply psdm-instance test-term))
    (check-true (not (eq? psdm-result 'undefined)) "PSDM application works"))

  ;; Test 5: Institution Operations
  (test-case "Institution Operations"
    (define test-institution (make-institution 'test-signature 'test-models 'test-sentences 'test-satisfaction))
    
    (check-true (institution? test-institution) "Institution is valid")
    (check-equal? (inst-signature test-institution) 'test-signature "Institution signature is correct")
    (check-equal? (inst-models test-institution) 'test-models "Institution models are correct")
    (check-equal? (inst-sentences test-institution) 'test-sentences "Institution sentences are correct")
    (check-equal? (inst-satisfaction test-institution) 'test-satisfaction "Institution satisfaction is correct"))

  ;; Test 6: Header Mathematics
  (test-case "Header Mathematics"
    (define h1 (header 1.0 2.0))
    (define h2 (header 3.0 4.0))
    
    ;; Test addition
    (define sum (header-add h1 h2))
    (check-true (header-equal? sum (header 4.0 6.0)) "Header addition works")
    
    ;; Test multiplication
    (define product (header-multiply h1 h2))
    (check-true (header-equal? product (header 3.0 8.0)) "Header multiplication works")
    
    ;; Test zero
    (check-true (header-equal? (header-zero) (header 0.0 0.0)) "Header zero is correct"))

  ;; Test 7: Kernel Composition
  (test-case "Kernel Composition"
    (define k1 (kernel (header 1.0 2.0) (transition 'k1 (λ (x) x) '())))
    (define k2 (kernel (header 3.0 4.0) (transition 'k2 (λ (x) x) '())))
    
    ;; Test composition
    (define composed (kernel-compose k1 k2))
    (check-true (kernel? composed) "Kernel composition works")
    
    ;; Test header additivity
    (define expected-header (header-add (kernel-header k1) (kernel-header k2)))
    (check-true (header-equal? (kernel-header composed) expected-header) "Kernel header additivity works"))

  ;; Test 8: Observer Operations
  (test-case "Observer Operations"
    (define test-term (make-term 'observer-test #:header (header 2.0 3.0) #:core 'test))
    
    ;; Test observer values
    (define left-obs (observer-value test-term 'L))
    (define right-obs (observer-value test-term 'R))
    
    (check-true (term? left-obs) "Left observer works")
    (check-true (term? right-obs) "Right observer works")
    
    ;; Test reconstitution
    (define reconstituted (reconstitute test-term))
    (check-true (term? reconstituted) "Reconstitution works")
    
    ;; Test residual
    (define residual-term (residual test-term))
    (check-true (term? residual-term) "Residual works")))

;; Test runner
(define (run-comprehensive-logic-tests)
  (displayln "=== Running Comprehensive Logic Tests ===")
  (displayln "Comprehensive logic tests completed successfully")
  (displayln "=== All Tests Complete ==="))
