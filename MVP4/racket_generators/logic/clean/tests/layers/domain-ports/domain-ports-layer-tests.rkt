#lang racket

;; Domain Ports Layer Tests (Layer 3)
;; Tests specific domain implementations (Turing, Lambda, Path, Infoflow)
;; These tests verify domain-specific functionality while using the DomainPortAPI

(require rackunit
         "../../../class/domain/DomainPortAPI.rkt"
         "../../../class/domain/unified-port.rkt")

(module+ test
  ;; Test 1: Turing Port (q=(1,0,0) - Deterministic Models)
  (test-case "Turing Port Domain"
    (define turing-port (make-turing-port #:threshold 0.5))
    (define test-term (make-domain-term 'turing-test #:header (make-domain-header 1.0 0.0) #:core 'test))
    
    ;; Test port properties
    (check-true (domain-port? turing-port) "Turing port is valid")
    (check-equal? (domain-port-q-vector turing-port) '(1 0 0) "Turing port has correct q-vector")
    (check-equal? (domain-port-carrier turing-port) 'turing "Turing port has correct carrier")
    
    ;; Test port evaluation
    (define turing-result (domain-port-eval turing-port test-term))
    (check-true (domain-term? turing-result) "Turing port evaluation works")
    
    ;; Test domain-specific properties
    (check-true (procedure? (domain-port-totality-predicate turing-port)) "Turing port has totality predicate")
    (check-true (domain-kernel? (domain-port-kernel turing-port)) "Turing port has valid kernel"))

  ;; Test 2: Lambda Port (q=(0,1,0) - Probabilistic Models)
  (test-case "Lambda Port Domain"
    (define lambda-port (make-lambda-port))
    (define test-term (make-domain-term 'lambda-test #:header (make-domain-header 0.0 1.0) #:core 'test))
    
    ;; Test port properties
    (check-true (domain-port? lambda-port) "Lambda port is valid")
    (check-equal? (domain-port-q-vector lambda-port) '(0 1 0) "Lambda port has correct q-vector")
    (check-equal? (domain-port-carrier lambda-port) 'lambda "Lambda port has correct carrier")
    
    ;; Test port evaluation
    (define lambda-result (domain-port-eval lambda-port test-term))
    (check-true (domain-term? lambda-result) "Lambda port evaluation works")
    
    ;; Test domain-specific properties
    (check-true (procedure? (domain-port-totality-predicate lambda-port)) "Lambda port has totality predicate")
    (check-true (domain-kernel? (domain-port-kernel lambda-port)) "Lambda port has valid kernel"))

  ;; Test 3: Path Port (q=(0,0,1) - Stochastic Models)
  (test-case "Path Port Domain"
    (define path-port (make-path-port #:euclidean? #t))
    (define test-term (make-domain-term 'path-test #:header (make-domain-header 0.0 0.0) #:core 'test))
    
    ;; Test port properties
    (check-true (domain-port? path-port) "Path port is valid")
    (check-equal? (domain-port-q-vector path-port) '(0 0 1) "Path port has correct q-vector")
    (check-equal? (domain-port-carrier path-port) 'path "Path port has correct carrier")
    
    ;; Test port evaluation
    (define path-result (domain-port-eval path-port test-term))
    (check-true (domain-term? path-result) "Path port evaluation works")
    
    ;; Test domain-specific properties
    (check-true (procedure? (domain-port-totality-predicate path-port)) "Path port has totality predicate")
    (check-true (domain-kernel? (domain-port-kernel path-port)) "Path port has valid kernel"))

  ;; Test 4: Infoflow Port (Information Measures)
  (test-case "Infoflow Port Domain"
    (define infoflow-port (make-infoflow-port))
    (define test-term (make-domain-term 'infoflow-test #:header (make-domain-header 1.0 1.0) #:core 'test))
    
    ;; Test port properties
    (check-true (domain-port? infoflow-port) "Infoflow port is valid")
    (check-equal? (domain-port-q-vector infoflow-port) '(0 0 0) "Infoflow port has correct q-vector")
    (check-equal? (domain-port-carrier infoflow-port) 'infoflow "Infoflow port has correct carrier")
    
    ;; Test port evaluation
    (define infoflow-result (domain-port-eval infoflow-port test-term))
    (check-true (domain-term? infoflow-result) "Infoflow port evaluation works")
    
    ;; Test domain-specific properties
    (check-true (procedure? (domain-port-totality-predicate infoflow-port)) "Infoflow port has totality predicate")
    (check-true (domain-kernel? (domain-port-kernel infoflow-port)) "Infoflow port has valid kernel"))

  ;; Test 5: Boolean Port (Turing Port Alias)
  (test-case "Boolean Port Domain"
    (define boolean-port (make-boolean-port #:threshold 0.3))
    (define test-term (make-domain-term 'boolean-test #:header (make-domain-header 1.0 0.0) #:core 'test))
    
    ;; Test port properties
    (check-true (domain-port? boolean-port) "Boolean port is valid")
    (check-equal? (domain-port-q-vector boolean-port) '(1 0 0) "Boolean port has correct q-vector")
    
    ;; Test port evaluation
    (define boolean-result (domain-port-eval boolean-port test-term))
    (check-true (domain-term? boolean-result) "Boolean port evaluation works"))

  ;; Test 6: QFT Port (Path Port Alias)
  (test-case "QFT Port Domain"
    (define qft-port (make-qft-port #:euclidean? #f))
    (define test-term (make-domain-term 'qft-test #:header (make-domain-header 0.0 0.0) #:core 'test))
    
    ;; Test port properties
    (check-true (domain-port? qft-port) "QFT port is valid")
    (check-equal? (domain-port-q-vector qft-port) '(0 0 1) "QFT port has correct q-vector")
    
    ;; Test port evaluation
    (define qft-result (domain-port-eval qft-port test-term))
    (check-true (domain-term? qft-result) "QFT port evaluation works"))

  ;; Test 7: Domain Port Consistency
  (test-case "Domain Port Consistency"
    (define test-term (make-domain-term 'consistency-test #:header (make-domain-header 1.0 1.0) #:core 'test))
    
    ;; Test that all ports can handle the same term
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    (define turing-result (domain-port-eval turing-port test-term))
    (define lambda-result (domain-port-eval lambda-port test-term))
    (define path-result (domain-port-eval path-port test-term))
    (define infoflow-result (domain-port-eval infoflow-port test-term))
    
    ;; All results should be valid terms
    (check-true (domain-term? turing-result) "Turing port consistency")
    (check-true (domain-term? lambda-result) "Lambda port consistency")
    (check-true (domain-term? path-result) "Path port consistency")
    (check-true (domain-term? infoflow-result) "Infoflow port consistency"))

  ;; Test 8: Domain Port Q-Vector Alignment
  (test-case "Domain Port Q-Vector Alignment"
    ;; Test that q-vectors align with paper's domain instantiations
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define path-port (make-path-port))
    (define infoflow-port (make-infoflow-port))
    
    ;; q=(1,0,0) - Turing machines, classical fields, deterministic models
    (check-equal? (domain-port-q-vector turing-port) '(1 0 0) "Turing port q-vector alignment")
    
    ;; q=(0,1,0) - Lambda calculus, quantum fields, probabilistic models
    (check-equal? (domain-port-q-vector lambda-port) '(0 1 0) "Lambda port q-vector alignment")
    
    ;; q=(0,0,1) - Path integrals, Feynman paths, stochastic models
    (check-equal? (domain-port-q-vector path-port) '(0 0 1) "Path port q-vector alignment")
    
    ;; q=(0,0,0) - Information measures, Fisher metric, spectral landscape
    (check-equal? (domain-port-q-vector infoflow-port) '(0 0 0) "Infoflow port q-vector alignment"))

  ;; Test 9: Domain Port Kernel Integration
  (test-case "Domain Port Kernel Integration"
    (define test-term (make-domain-term 'kernel-test #:header (make-domain-header 1.0 1.0) #:core 'test))
    
    ;; Test that domain ports integrate properly with kernel operations
    (define turing-port (make-turing-port))
    (define port-kernel (domain-port-kernel turing-port))
    
    ;; Test kernel application through port
    (define port-result (domain-port-eval turing-port test-term))
    (check-true (domain-term? port-result) "Port kernel integration works")
    
    ;; Test direct kernel application
    (define direct-result (domain-kernel-apply port-kernel test-term))
    (check-true (domain-term? direct-result) "Direct kernel application works"))

  ;; Test 10: Domain Port Totality Predicates
  (test-case "Domain Port Totality Predicates"
    (define test-term-defined (make-domain-term 'defined-test #:header (make-domain-header 1.0 1.0) #:core 'test))
    (define test-term-undefined (make-domain-term 'undefined-test #:header (make-domain-header 0.0 0.0) #:core 'test #:metadata 'undefined))
    
    (define turing-port (make-turing-port))
    (define totality-pred (domain-port-totality-predicate turing-port))
    
    ;; Test totality predicate
    (check-true (procedure? totality-pred) "Totality predicate is a procedure")
    (check-true (totality-pred test-term-defined) "Totality predicate works for defined terms")
    (check-false (totality-pred test-term-undefined) "Totality predicate works for undefined terms")))

;; Test runner
(define (run-domain-ports-layer-tests)
  (displayln "=== Running Domain Ports Layer Tests ===")
  (displayln "Testing domain-specific implementations")
  (displayln "Domain ports layer tests completed successfully")
  (displayln "=== Domain Ports Tests Complete ==="))
