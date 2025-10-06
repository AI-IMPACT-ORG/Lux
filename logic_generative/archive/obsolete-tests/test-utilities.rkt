#lang racket

;; @logic/gen Test Utilities
;; Centralized test utilities adapted for generator-focused CLEAN language

(require rackunit
         racket/format
         racket/random
         "../core.rkt"
         "../truth.rkt"
         "../rg.rkt"
         "../ports/boolean.rkt")

(provide ; Test data generation
         generate-test-term
         generate-test-kernel
         generate-test-generator
         generate-test-suite
         
         ; Test validation
         validate-term-properties
         validate-kernel-properties
         validate-generator-properties
         validate-mathematical-properties
         
         ; Test execution
         safe-test-execution
         run-test-suite
         run-test-layer
         
         ; Test reporting
         format-test-results
         generate-test-report
         
         ; Common test patterns
         test-generator-algebra-properties
         test-observer-properties
         test-class-properties
         test-domain-properties
         
         ; Enhanced test functions
         test-moduli-properties
         test-guarded-properties
         test-psdm-properties
         test-feynman-properties
         test-domain-coherence
         test-domain-evaluation
         test-domain-psdm-consistency
         generate-systematic-test-terms
         validate-systematic-properties)

;; ============================================================================
;; TEST DATA GENERATION FOR GENERATORS
;; ============================================================================

;; Generate test term (placeholder - will connect to Core when available)
(define (generate-test-term [name "test-term"] [phase 1.0] [scale 1.0] [core 'test])
  "Generate a test term with specified properties"
  ;; This will be connected to Core signature when implemented
  (error 'generate-test-term "implement using Core signature"))

;; Generate test kernel (placeholder - will connect to Core when available)
(define (generate-test-kernel [phase 0.5] [scale 0.5] [carrier 'test])
  "Generate a test kernel with specified properties"
  ;; This will be connected to Core kernel when implemented
  (error 'generate-test-kernel "implement using Core kernel"))

;; Generate test generator
(define (generate-test-generator [tag 'test] [laws '(basic)])
  "Generate a test generator with specified properties"
  (make-gen (λ (x) x) tag laws))

;; Generate test header (placeholder - will connect to Core when available)
(define (generate-test-header [phase 1.0] [scale 1.0])
  "Generate a test header with specified properties"
  ;; This will be connected to Core header when implemented
  (error 'generate-test-header "implement using Core header"))

;; Generate test suite
(define (generate-test-suite [count 10])
  "Generate a suite of test data"
  (for/list ([i count])
    (hash 'generator (generate-test-generator (string->symbol (format "gen-~a" i)) '(test))
          'term (generate-test-term (format "term-~a" i) i (* i 0.1))
          'kernel (generate-test-kernel (* i 0.1) (* i 0.1) (format "carrier-~a" i)))))

;; ============================================================================
;; TEST VALIDATION FOR GENERATORS
;; ============================================================================

;; Validate generator properties
(define (validate-generator-properties gen)
  "Validate that a generator has correct properties"
  (and (gen? gen)
       (procedure? (gen-apply gen))
       (hash? (gen-meta gen))
       (hash-has-key? (gen-meta gen) 'tag)
       (hash-has-key? (gen-meta gen) 'laws)))

;; Validate term properties (placeholder)
(define (validate-term-properties term)
  "Validate that a term has correct properties"
  ;; This will be connected to Core signature when implemented
  (error 'validate-term-properties "implement using Core signature"))

;; Validate kernel properties (placeholder)
(define (validate-kernel-properties kern)
  "Validate that a kernel has correct properties"
  ;; This will be connected to Core kernel when implemented
  (error 'validate-kernel-properties "implement using Core kernel"))

;; Validate header properties (placeholder)
(define (validate-header-properties hdr)
  "Validate that a header has correct properties"
  ;; This will be connected to Core header when implemented
  (error 'validate-header-properties "implement using Core header"))

;; Validate mathematical properties
(define (validate-mathematical-properties gen)
  "Validate mathematical properties of a generator"
  (and (validate-generator-properties gen)
       ;; Test generator application
       (let ([test-input 42])
         (define result (gen-apply gen test-input))
         (not (void? result)))))

;; ============================================================================
;; TEST EXECUTION
;; ============================================================================

;; Safe test execution with error handling
(define (safe-test-execution test-fn)
  "Execute a test function safely with error handling"
  (with-handlers ([exn:fail? (λ (e) (displayln (format "Test failed: ~a" (exn-message e))) #f)])
    (test-fn)
    #t))

;; Run test suite with proper reporting
(define (run-test-suite suite-name test-cases)
  "Run a test suite with proper reporting"
  (displayln (format "=== Running ~a ===" suite-name))
  (define results '())
  (for ([test-case test-cases])
    (define result (safe-test-execution test-case))
    (set! results (cons result results)))
  (displayln (format "=== ~a Complete ===" suite-name))
  results)

;; Run test layer with proper reporting
(define (run-test-layer layer-name layer-tests)
  "Run a test layer with proper reporting"
  (displayln (format "🧮 Testing ~a..." layer-name))
  (define results (run-test-suite layer-name layer-tests))
  (displayln (format "✅ ~a tests completed" layer-name))
  results)

;; ============================================================================
;; TEST REPORTING
;; ============================================================================

;; Format test results for display
(define (format-test-results results)
  "Format test results for display"
  (define passed (count identity results))
  (define total (length results))
  (format "Passed: ~a/~a (~a%)" passed total (round (* 100 (/ passed total)))))

;; Generate test report for a layer
(define (generate-test-report layer-name results)
  "Generate a test report for a layer"
  (displayln (format "📊 ~a Test Report" layer-name))
  (displayln (format-test-results results))
  (displayln ""))

;; ============================================================================
;; COMMON TEST PATTERNS FOR GENERATORS
;; ============================================================================

;; Test generator algebra properties
(define (test-generator-algebra-properties)
  "Test generator algebra properties"
  (define g1 (generate-test-generator 'inc '(monotonic)))
  (define g2 (generate-test-generator 'double '(linear)))
  (define g3 (generate-test-generator 'triple '(linear)))
  
  (and (validate-generator-properties g1)
       (validate-generator-properties g2)
       (validate-generator-properties g3)
       ;; Test composition
       (let ([composed (gen-compose g1 g2)])
         (validate-generator-properties composed))
       ;; Test associativity
       (test-associativity g1 g2 g3)
       ;; Test identity laws
       (test-identity g1)))

;; Test observer properties (placeholder)
(define (test-observer-properties)
  "Test observer function properties"
  ;; This will be connected to Core observers when implemented
  (error 'test-observer-properties "implement using Core observers"))

;; Test CLASS properties (placeholder)
(define (test-class-properties)
  "Test CLASS specification properties"
  ;; This will be connected to Class when implemented
  (error 'test-class-properties "implement using Class"))

;; Test domain properties
(define (test-domain-properties)
  "Test domain port properties"
  (define B (make-boolean-port))
  (define L (make-lambda-port))
  (define I (make-infoflow-port))
  (define Q (make-qft-port))
  
  (and (validate-domain-port-coherence B)
       (validate-domain-port-coherence L)
       (validate-domain-port-coherence I)
       (validate-domain-port-coherence Q)
       ;; Test port composition
       (let ([BL (compose-domain-ports B L)])
         (validate-domain-port-coherence BL))))

;; ============================================================================
;; ENHANCED TEST FUNCTIONS (PLACEHOLDERS)
;; ============================================================================

;; Test moduli properties (placeholder)
(define (test-moduli-properties term)
  "Test moduli flow properties"
  ;; This will be connected to Class moduli when implemented
  (error 'test-moduli-properties "implement using Class moduli"))

;; Test guarded properties (placeholder)
(define (test-guarded-properties term)
  "Test guarded negation properties"
  ;; This will be connected to Class guarded when implemented
  (error 'test-guarded-properties "implement using Class guarded"))

;; Test PSDM properties (placeholder)
(define (test-psdm-properties term)
  "Test PSDM properties"
  ;; This will be connected to Class PSDM when implemented
  (error 'test-psdm-properties "implement using Class PSDM"))

;; Test Feynman properties (placeholder)
(define (test-feynman-properties term)
  "Test Feynman path integration properties"
  ;; This will be connected to Class Feynman when implemented
  (error 'test-feynman-properties "implement using Class Feynman"))

;; Test domain coherence
(define (test-domain-coherence term)
  "Test domain port coherence"
  (define boolean-port (make-boolean-port))
  (define lambda-port (make-lambda-port))
  
  (and (validate-domain-port-coherence boolean-port)
       (validate-domain-port-coherence lambda-port)))

;; Test domain evaluation
(define (test-domain-evaluation term)
  "Test domain port evaluation"
  (define boolean-port (make-boolean-port))
  (define lambda-port (make-lambda-port))
  
  (and (psdm-defined? boolean-port term)
       (psdm-defined? lambda-port term)))

;; Test domain PSDM consistency
(define (test-domain-psdm-consistency term)
  "Test domain port PSDM consistency"
  (define boolean-port (make-boolean-port))
  
  (and (psdm-defined? boolean-port term)
       (let ([result (domain-port-eval boolean-port term)])
         (or (eq? result 'undefined)
             (not (eq? result 'undefined))))))

;; ============================================================================
;; SYSTEMATIC TEST GENERATION
;; ============================================================================

;; Generate systematic test terms (placeholder)
(define (generate-systematic-test-terms #:count [count 10])
  "Generate systematic test terms for comprehensive testing"
  ;; This will be connected to Core signature when implemented
  (error 'generate-systematic-test-terms "implement using Core signature"))

;; Validate systematic properties
(define (validate-systematic-properties #:iterations [iterations 50])
  "Validate properties systematically across generated test data"
  (define test-generators (for/list ([i iterations])
                           (generate-test-generator (string->symbol (format "sys-gen-~a" i)) '(systematic))))
  (define all-passed #t)
  
  (for ([gen test-generators])
    (set! all-passed (and all-passed
                         (validate-generator-properties gen)
                         (test-generator-algebra-properties)
                         (test-domain-properties))))
  
  all-passed)

;; ============================================================================
;; GENERATOR-SPECIFIC TEST UTILITIES
;; ============================================================================

;; Test generator composition properties
(define (test-generator-composition g1 g2)
  "Test generator composition properties"
  (define composed (gen-compose g1 g2))
  (and (validate-generator-properties composed)
       (let ([test-input 42])
         (define result (gen-apply composed test-input))
         (not (void? result)))))

;; Test generator powers
(define (test-generator-powers g n)
  "Test generator powers"
  (define powered (gen-power g n))
  (and (validate-generator-properties powered)
       (let ([test-input 1])
         (define result (gen-apply powered test-input))
         (not (void? result)))))

;; Test Green's sum generator
(define (test-greens-sum g n)
  "Test Green's sum generator"
  (define greens (greens-sum-generator g n))
  (and (validate-generator-properties greens)
       (let ([test-input 0])
         (define result (gen-apply greens test-input))
         (not (void? result)))))

;; Test RG blocking
(define (test-rg-blocking g k)
  "Test RG blocking"
  (define blocked (rg-block-generator g k))
  (and (validate-generator-properties blocked)
       (test-rg-closure g)))

;; Test flow convergence
(define (test-flow-convergence-properties)
  "Test flow convergence properties"
  (define f (λ (x) (/ (+ x (/ 2 x)) 2)))  ; Newton's method for sqrt(2)
  (define conv-gen (flow-convergence-generator f 0.001 100))
  (and (validate-generator-properties conv-gen)
       (let ([result (gen-apply conv-gen 1.0)])
         (number? result))))

;; Test fixed point generator
(define (test-fixed-point-properties)
  "Test fixed point generator properties"
  (define f (λ (x) (cos x)))
  (define fp-gen (fixed-point-generator f 0.001))
  (and (validate-generator-properties fp-gen)
       (let ([result (gen-apply fp-gen 1.0)])
         (number? result))))

;; Initialize test utilities
(displayln "@logic/gen Test Utilities initialized")

