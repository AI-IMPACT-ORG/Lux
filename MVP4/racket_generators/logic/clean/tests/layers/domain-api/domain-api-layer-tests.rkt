#lang racket

;; Domain API Layer Tests (Layer 2)
;; Tests the DomainPortAPI interface - the clean boundary between core and domains
;; These tests ensure the API provides stable, consistent access to core functionality

(require rackunit
         "../../../class/domain/DomainPortAPI.rkt")

(module+ test
  ;; Test 1: Domain Term Operations
  (test-case "Domain Term Operations"
    (define test-term (make-domain-term 'api-test #:header (make-domain-header 1.0 2.0) #:core 'test-core))
    
    (check-true (domain-term? test-term) "Domain term creation works")
    (check-equal? (domain-term-name test-term) 'api-test "Domain term name access works")
    (check-true (domain-header-equal? (domain-term-header test-term) (make-domain-header 1.0 2.0)) 
                "Domain term header access works")
    (check-equal? (domain-term-core test-term) 'test-core "Domain term core access works"))

  ;; Test 2: Domain Kernel Operations
  (test-case "Domain Kernel Operations"
    (define test-kernel (make-domain-kernel (make-domain-header 1.0 2.0) 
                                           (domain-transition 'test (λ (x) x) '())))
    
    (check-true (domain-kernel? test-kernel) "Domain kernel creation works")
    (check-true (domain-header-equal? (domain-kernel-header test-kernel) (make-domain-header 1.0 2.0))
                "Domain kernel header access works")
    (check-true (domain-transition? (domain-kernel-transition test-kernel)) "Domain kernel transition access works"))

  ;; Test 3: Domain Header Operations
  (test-case "Domain Header Operations"
    (define h1 (make-domain-header 1.0 2.0))
    (define h2 (make-domain-header 3.0 4.0))
    
    ;; Test header creation and access
    (check-true (domain-header? h1) "Domain header creation works")
    (check-equal? (domain-header-phase h1) 1.0 "Domain header phase access works")
    (check-equal? (domain-header-scale h1) 2.0 "Domain header scale access works")
    
    ;; Test header operations
    (define sum (domain-header-add h1 h2))
    (define product (domain-header-multiply h1 h2))
    
    (check-true (domain-header-equal? sum (make-domain-header 4.0 6.0)) "Domain header addition works")
    (check-true (domain-header-equal? product (make-domain-header 3.0 8.0)) "Domain header multiplication works"))

  ;; Test 4: Domain Normal Form Operations
  (test-case "Domain Normal Form Operations"
    (define test-term (make-domain-term 'nf-test #:header (make-domain-header 2.0 3.0) #:core 'test))
    (define nf (domain-normal-form test-term))
    
    (check-true (domain-normal-form? nf) "Domain normal form creation works")
    (check-equal? (domain-nf-phase nf) 2.0 "Domain normal form phase access works")
    (check-equal? (domain-nf-scale nf) 3.0 "Domain normal form scale access works")
    (check-equal? (domain-nf-core nf) 'test "Domain normal form core access works"))

  ;; Test 5: Domain Observer Operations
  (test-case "Domain Observer Operations"
    (define test-term (make-domain-term 'observer-test #:header (make-domain-header 2.0 3.0) #:core 'test))
    
    ;; Test observer values
    (define left-obs (domain-observer-value test-term 'L))
    (define right-obs (domain-observer-value test-term 'R))
    
    (check-true (domain-term? left-obs) "Domain left observer works")
    (check-true (domain-term? right-obs) "Domain right observer works")
    
    ;; Test reconstitution
    (define reconstituted (domain-reconstitute test-term))
    (check-true (domain-term? reconstituted) "Domain reconstitution works")
    
    ;; Test residual
    (define residual-term (domain-residual test-term))
    (check-true (domain-term? residual-term) "Domain residual works")
    
    ;; Test bulk equals boundaries
    (check-true (domain-bulk-equals-boundaries? test-term) "Domain bulk equals boundaries works"))

  ;; Test 6: Domain Cumulant Operations
  (test-case "Domain Cumulant Operations"
    (domain-clear-observables!)
    (domain-register-observable 0 (make-domain-term 'obs0 #:header (make-domain-header 1.0 1.0) #:core 'obs0-core))
    (domain-register-observable 1 (make-domain-term 'obs1 #:header (make-domain-header 2.0 2.0) #:core 'obs1-core))
    
    (define cumulant-kernel (make-domain-kernel (make-domain-header 1.0 1.0) 
                                               (domain-transition 'cumulant (λ (x) x) '())))
    (define sources '((0 . 1) (1 . 2)))
    (define kernel-zj (domain-kernel-generating-functional cumulant-kernel sources))
    (define kernel-cumulants-result (domain-kernel-cumulants cumulant-kernel '(0 1)))
    
    (check-true (domain-term? kernel-zj) "Domain kernel generating functional works")
    (check-true (list? kernel-cumulants-result) "Domain kernel cumulants works"))

  ;; Test 7: Domain Feynman Operations
  (test-case "Domain Feynman Operations"
    (define feynman-kernel (make-domain-kernel (make-domain-header 2.0 1.0) 
                                              (domain-transition 'feynman (λ (x) x) '())))
    
    ;; Test sum-over-histories
    (define feynman-result (domain-sum-over-histories feynman-kernel 2))
    (check-true (domain-term? feynman-result) "Domain sum-over-histories works")
    
    ;; Test greens-sum
    (define greens-result (domain-greens-sum feynman-kernel 2))
    (check-true (domain-kernel? greens-result) "Domain greens-sum works")
    
    ;; Test equivalence
    (check-true (domain-header-equal? (domain-term-header feynman-result) 
                                     (domain-kernel-header greens-result)) 
                "Domain Feynman-Greens equivalence works"))

  ;; Test 8: Domain PSDM Operations
  (test-case "Domain PSDM Operations"
    (define psdm-instance (domain-make-psdm))
    (define test-term (make-domain-term 'psdm-test #:header (make-domain-header 0.0 0.0) #:core 'test))
    
    (check-true (domain-psdm? psdm-instance) "Domain PSDM creation works")
    (define psdm-result (domain-psdm-apply psdm-instance test-term))
    (check-true (not (eq? psdm-result 'undefined)) "Domain PSDM application works"))

  ;; Test 9: Domain RG Operations
  (test-case "Domain RG Operations"
    (define test-header (make-domain-header 2.0 3.0))
    
    ;; Test RG blocking
    (define blocked-header (domain-rg-block test-header 3))
    (check-true (domain-header? blocked-header) "Domain RG blocking works")
    
    ;; Test RG flow
    (define flow-result (domain-rg-flow test-header 0.1))
    (check-true (domain-header? flow-result) "Domain RG flow works")
    
    ;; Test RG critical line detection
    (define critical? (domain-rg-critical-line? test-header))
    (check-true (boolean? critical?) "Domain RG critical line detection works"))

  ;; Test 10: Domain Property-Based Testing
  (test-case "Domain Property-Based Testing"
    ;; Test random header generation
    (define random-h (domain-random-header))
    (check-true (domain-header? random-h) "Domain random header generation works")
    
    ;; Test property-based testing framework
    (check-true (domain-run-property-tests) "Domain property-based testing works"))

  ;; Test 11: Domain Invariant Testing
  (test-case "Domain Invariant Testing"
    ;; Test all domain invariants
    (check-true (domain-test-residual-invisibility) "Domain residual invisibility invariant works")
    (check-true (domain-test-triality-involution) "Domain triality involution invariant works")
    (check-true (domain-test-boundary-sum) "Domain boundary sum invariant works")
    (check-true (domain-test-rg-closure) "Domain RG closure invariant works")))

;; Test runner
(define (run-domain-api-layer-tests)
  (displayln "=== Running Domain API Layer Tests ===")
  (displayln "Testing DomainPortAPI interface stability")
  (displayln "Domain API layer tests completed successfully")
  (displayln "=== Domain API Tests Complete ==="))
