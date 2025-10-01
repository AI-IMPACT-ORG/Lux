#lang racket

;; Test Utilities - Comprehensive validation and testing infrastructure
;; Provides strengthened test harness capabilities for CLEAN v10

(require rackunit
         "../../core/signature.rkt"
         "../../core/kernel.rkt"
         "../../core/nf.rkt"
         "../../core/observers.rkt"
         "../../core/cumulants.rkt"
         "../../core/header.rkt")

(provide ; Comprehensive validation functions
         validate-header-properties
         validate-kernel-properties
         validate-term-properties
         validate-mathematical-properties
         
         ; Test data generation
         generate-random-header
         generate-random-kernel
         generate-random-term
         generate-test-suite
         
         ; Safe test execution
         safe-test-execution
         test-case-result?
         test-case-result-passed?
         test-case-result-message
         
         ; Comprehensive test runners
         run-comprehensive-tests
         run-property-tests-enhanced
         run-invariant-tests-enhanced)

;; ===== COMPREHENSIVE VALIDATION FUNCTIONS =====

;; Validate header properties comprehensively
(define (validate-header-properties h)
  (and (header? h)
       (real? (header-phase h))
       (real? (header-scale h))
       (not (nan? (header-phase h)))
       (not (nan? (header-scale h)))
       (not (infinite? (header-phase h)))
       (not (infinite? (header-scale h)))))

;; Validate kernel properties comprehensively
(define (validate-kernel-properties k)
  (and (kernel? k)
       (validate-header-properties (kernel-header k))
       (transition? (kernel-transition k))
       (procedure? (transition-step-weight (kernel-transition k)))
       (list? (transition-event-sequence (kernel-transition k)))))

;; Validate term properties comprehensively
(define (validate-term-properties t)
  (and (term? t)
       (symbol? (term-name t))
       (validate-header-properties (term-header t))
       (list? (term-core t))
       (or (not (term-left t)) (term? (term-left t)))
       (or (not (term-right t)) (term? (term-right t)))))

;; Validate mathematical properties across the system
(define (validate-mathematical-properties #:iterations [iterations 10])
  (define all-passed #t)
  
  (for ([i iterations])
    (define h1 (generate-random-header))
    (define h2 (generate-random-header))
    (define k (generate-random-kernel))
    (define t (generate-random-term))
    
    ;; Test header operations
    (define sum (header-add h1 h2))
    (define product (header-multiply h1 h2))
    
    (set! all-passed (and all-passed
                         (validate-header-properties sum)
                         (validate-header-properties product)))
    
    ;; Test kernel operations
    (define applied (kernel-apply k t))
    (set! all-passed (and all-passed (validate-term-properties applied)))
    
    ;; Test RG operations
    (define blocked (rg-block h1 2))
    (define flow (rg-flow h1 '(0.1 0.1 0.1 0.1 0.1 0.1)))
    (set! all-passed (and all-passed
                         (validate-header-properties blocked)
                         (validate-header-properties flow))))
  
  all-passed)

;; ===== TEST DATA GENERATION =====

;; Generate random header with controlled range
(define (generate-random-header #:phase-range [phase-range 10.0] #:scale-range [scale-range 10.0])
  (define phase (- (* (random) (* 2 phase-range)) phase-range))
  (define scale (- (* (random) (* 2 scale-range)) scale-range))
  (header phase scale))

;; Generate random kernel
(define (generate-random-kernel)
  (define h (generate-random-header))
  (define carrier (string->symbol (format "random-~a" (random 1000))))
  (define step-weight (λ (x) x)) ; Identity function for simplicity
  (define event-sequence (list (string->symbol (format "event-~a" (random 100)))))
  (kernel h (transition carrier step-weight event-sequence)))

;; Generate random term
(define (generate-random-term)
  (define name (string->symbol (format "random-term-~a" (random 1000))))
  (define h (generate-random-header))
  (define core (list (string->symbol (format "core-~a" (random 100)))))
  (make-term name #:header h #:core core))

;; Generate comprehensive test suite
(define (generate-test-suite #:size [size 10] #:header-range [header-range 5.0])
  (define terms (for/list ([i size]) (generate-random-term)))
  (define kernels (for/list ([i size]) (generate-random-kernel)))
  (define headers (for/list ([i size]) (generate-random-header #:phase-range header-range #:scale-range header-range)))
  (list terms kernels headers))

;; ===== SAFE TEST EXECUTION =====

;; Test case result structure
(struct test-case-result (passed? message) #:transparent)

;; Execute test safely with error handling
(define (safe-test-execution test-name test-function)
  (with-handlers ([exn:fail? (λ (e) (test-case-result #f (format "~a failed: ~a" test-name (exn-message e))))])
    (define result (test-function))
    (if result
        (test-case-result #t (format "~a passed" test-name))
        (test-case-result #f (format "~a returned false" test-name)))))

;; ===== COMPREHENSIVE TEST RUNNERS =====

;; Run comprehensive test suite
(define (run-comprehensive-tests #:iterations [iterations 25])
  (define results (make-hash))
  
  ;; Test mathematical properties
  (define math-result (safe-test-execution "Mathematical Properties" 
                                          (λ () (validate-mathematical-properties #:iterations iterations))))
  (hash-set! results 'mathematical math-result)
  
  ;; Test property-based testing
  (define property-result (safe-test-execution "Property-Based Testing"
                                               (λ () (run-property-tests-enhanced #:iterations iterations))))
  (hash-set! results 'property-based property-result)
  
  ;; Test invariant testing
  (define invariant-result (safe-test-execution "Invariant Testing"
                                                (λ () (run-invariant-tests-enhanced))))
  (hash-set! results 'invariants invariant-result)
  
  results)

;; Enhanced property-based testing
(define (run-property-tests-enhanced #:iterations [iterations 20])
  (define all-passed #t)
  
  (for ([i iterations])
    (define h1 (generate-random-header))
    (define h2 (generate-random-header))
    (define h3 (generate-random-header))
    
    ;; Test associativity
    (define left-assoc (header-add (header-add h1 h2) h3))
    (define right-assoc (header-add h1 (header-add h2 h3)))
    (set! all-passed (and all-passed (header-equal? left-assoc right-assoc)))
    
    ;; Test commutativity
    (define sum1 (header-add h1 h2))
    (define sum2 (header-add h2 h1))
    (set! all-passed (and all-passed (header-equal? sum1 sum2)))
    
    ;; Test identity
    (define identity-test (header-add h1 header-zero))
    (set! all-passed (and all-passed (header-equal? identity-test h1)))
    
    ;; Test kernel associativity
    (define k1 (generate-random-kernel))
    (define k2 (generate-random-kernel))
    (define k3 (generate-random-kernel))
    (define k-left-assoc (kernel-compose (kernel-compose k1 k2) k3))
    (define k-right-assoc (kernel-compose k1 (kernel-compose k2 k3)))
    (set! all-passed (and all-passed (header-equal? (kernel-header k-left-assoc) (kernel-header k-right-assoc)))))
  
  all-passed)

;; Enhanced invariant testing
(define (run-invariant-tests-enhanced)
  (define all-passed #t)
  
  ;; Generate test data
  (define test-kernel (generate-random-kernel))
  (define test-term (generate-random-term))
  
  ;; Test residual invisibility
  (set! all-passed (and all-passed (test-residual-invisibility test-kernel test-term)))
  
  ;; Test triality involution
  (set! all-passed (and all-passed (test-triality-involution test-term)))
  
  ;; Test boundary sum
  (set! all-passed (and all-passed (test-boundary-sum test-term)))
  
  ;; Test RG closure
  (set! all-passed (and all-passed (test-rg-closure test-kernel test-term)))
  
  all-passed)

;; ===== TEST REPORTING =====

;; Generate test report
(define (generate-test-report results)
  (displayln "=== COMPREHENSIVE TEST REPORT ===")
  (for ([(test-name result) results])
    (displayln (format "~a: ~a" 
                       (string-upcase (symbol->string test-name))
                       (if (test-case-result-passed? result) "PASS" "FAIL")))
    (displayln (format "  Message: ~a" (test-case-result-message result))))
  (displayln "=== END TEST REPORT ==="))

;; Performance testing
(define (run-performance-tests #:iterations [iterations 100])
  (define start-time (current-inexact-milliseconds))
  
  (for ([i iterations])
    (begin
      (define h1 (generate-random-header))
      (define h2 (generate-random-header))
      (define sum (header-add h1 h2))
      (define product (header-multiply h1 h2))
      (define blocked (rg-block h1 2))
      (define flow (rg-flow h1 '(0.1 0.1 0.1 0.1 0.1 0.1)))
      (void)))
  
  (define end-time (current-inexact-milliseconds))
  (define duration (- end-time start-time))
  
  (displayln (format "Performance test completed ~a iterations in ~a ms" iterations duration))
  (displayln (format "Average time per iteration: ~a ms" (/ duration iterations)))
  
  duration)
