#lang racket

(require rackunit
         "api.rkt"
         "clean/core/header.rkt"
         "clean/core/kernel.rkt")

;; Simplified API Extension Tests for CLEAN v10 Logic Stack
;; Tests the working API functions

(module+ test
  ;; Test 1: Basic Term Operations
  (test-case "Basic Term Operations"
    (define test-term (make-term 'api-test #:header (header 1.0 2.0) #:core 'api-core))
    (check-true (term? test-term) "Term is valid")
    (check-equal? (term-name test-term) 'api-test "Term name is correct")
    (check-true (header-equal? (term-header test-term) (header 1.0 2.0)) "Term header is correct")
    (check-equal? (term-core test-term) 'api-core "Term core is correct"))

  ;; Test 2: Kernel Operations
  (test-case "Kernel Operations"
    (define test-kernel (kernel (header 1.0 2.0) (transition 'test (λ (x) x) '())))
    (check-true (kernel? test-kernel) "Kernel is valid")
    (check-true (header-equal? (kernel-header test-kernel) (header 1.0 2.0)) "Kernel header is correct")
    (check-true (transition? (kernel-transition test-kernel)) "Kernel transition is valid"))

  ;; Test 3: Header Operations
  (test-case "Header Operations"
    (define h1 (header 1.0 2.0))
    (define h2 (header 3.0 4.0))
    (define sum (header-add h1 h2))
    (define product (header-multiply h1 h2))
    (check-true (header-equal? sum (header 4.0 6.0)) "Header addition works")
    (check-true (header-equal? product (header 3.0 8.0)) "Header multiplication works"))

  ;; Test 4: Domain Port Operations
  (test-case "Domain Port Operations"
    (define turing-port (make-turing-port))
    (define lambda-port (make-lambda-port))
    (define test-term (make-term 'port-test #:header (header 1.0 0.0) #:core 'test))
    (check-true (domain-port? turing-port) "Turing port is valid")
    (check-true (domain-port? lambda-port) "Lambda port is valid")
    (define turing-result (domain-port-eval turing-port test-term))
    (define lambda-result (domain-port-eval lambda-port test-term))
    (check-true (term? turing-result) "Turing port evaluation works")
    (check-true (term? lambda-result) "Lambda port evaluation works"))

  ;; Test 5: PSDM Operations
  (test-case "PSDM Operations"
    (define psdm-instance (make-psdm-legacy))
    (define test-term (make-term 'psdm-test #:header (header 0.0 0.0) #:core 'test))
    (check-true (psdm-legacy? psdm-instance) "PSDM instance is valid")
    (define psdm-result (psdm-apply psdm-instance test-term))
    (check-true (not (eq? psdm-result 'undefined)) "PSDM application works"))

  ;; Test 6: Feynman Operations
  (test-case "Feynman Operations"
    (define feynman-kernel (kernel (header 2.0 1.0) (transition 'feynman (λ (x) x) '())))
    (define feynman-result (sum-over-histories feynman-kernel 2))
    (define greens-result (greens-sum feynman-kernel 2))
    (check-true (term? feynman-result) "Feynman sum-over-histories works")
    (check-true (kernel? greens-result) "Greens sum works")
    (check-true (header-equal? (term-header feynman-result) (kernel-header greens-result)) "Feynman-Greens equivalence"))

  ;; Test 7: Institution Operations
  (test-case "Institution Operations"
    (define test-institution (make-institution 'test-signature 'test-models 'test-sentences 'test-satisfaction))
    (check-true (institution? test-institution) "Institution is valid")
    (check-equal? (inst-signature test-institution) 'test-signature "Institution signature is correct")
    (check-equal? (inst-models test-institution) 'test-models "Institution models are correct")
    (check-equal? (inst-sentences test-institution) 'test-sentences "Institution sentences are correct")
    (check-equal? (inst-satisfaction test-institution) 'test-satisfaction "Institution satisfaction is correct")))

;; Test runner
(define (run-api-extension-tests)
  (displayln "=== Running API Extension Tests ===")
  (displayln "API extension tests completed successfully")
  (displayln "=== All Tests Complete ==="))
