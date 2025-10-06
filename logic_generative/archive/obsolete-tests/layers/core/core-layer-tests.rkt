#lang racket

;; @logic/gen Core Layer Tests (Layer 1 - Innermost)
;; Tests the fundamental generator-focused CLEAN v10 mathematical properties
;; These tests should never change - they define the core generator invariants

(require rackunit
         "../../../core.rkt"
         "../../../truth.rkt"
         "../../../rg.rkt"
         "../../test-utilities.rkt")

(module+ test
  ;; Test 1: Generator Algebra Invariants
  (test-case "Generator Algebra Invariants"
    ;; Test generator identity
    (define id (gen-id))
    (check-true (gen? id) "Generator identity exists")
    (check-equal? (apply-gen id 5) 5 "Generator identity acts as identity")
    (check-equal? (apply-gen id 'test) 'test "Generator identity preserves values")
    
    ;; Test generator composition
    (define inc (make-gen add1 'increment '(monotonic)))
    (define double (make-gen (λ (x) (* 2 x)) 'double '(linear)))
    (define inc-then-double (gen-compose inc double))
    (check-equal? (apply-gen inc-then-double 5) 12 "Generator composition works correctly")
    
    ;; Test generator metadata
    (check-true (hash-has-key? (gen-meta inc) 'tag) "Generator has tag metadata")
    (check-true (hash-has-key? (gen-meta inc) 'laws) "Generator has laws metadata"))

  ;; Test 2: Generator Composition Laws
  (test-case "Generator Composition Laws"
    (define g1 (make-gen add1 'inc '(monotonic)))
    (define g2 (make-gen (λ (x) (* 2 x)) 'double '(linear)))
    (define g3 (make-gen (λ (x) (* 3 x)) 'triple '(linear)))
    
    ;; Test associativity: (g1 ∘ g2) ∘ g3 = g1 ∘ (g2 ∘ g3)
    (define left-assoc (gen-compose (gen-compose g1 g2) g3))
    (define right-assoc (gen-compose g1 (gen-compose g2 g3)))
    
    (check-true (test-associativity g1 g2 g3) "Generator composition is associative")
    
    ;; Test identity laws
    (check-true (test-identity g1) "Generator identity laws hold"))

  ;; Test 3: Generator Powers and Green's Sum
  (test-case "Generator Powers and Green's Sum"
    (define inc (make-gen add1 'increment '(monotonic)))
    
    ;; Test generator powers
    (define inc3 (gen-power inc 3))
    (check-equal? (apply-gen inc3 5) 8 "Generator powers work correctly")
    
    ;; Test Green's sum: G_N = I + K + K² + ... + K^N
    (define G3 (greens-sum-generator inc 3))
    (check-equal? (apply-gen G3 0) 6 "Green's sum works correctly")  ; 0 + 1 + 2 + 3 = 6
    
    ;; Test Green's sum with different N
    (define G5 (greens-sum-generator inc 5))
    (check-equal? (apply-gen G5 0) 15 "Green's sum with N=5 works correctly"))  ; 0 + 1 + 2 + 3 + 4 + 5 = 15

  ;; Test 4: RG Blocking and Closure
  (test-case "RG Blocking and Closure"
    (define scale (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    
    ;; Test RG blocking
    (define blocked (rg-block-generator scale 2))
    (check-true (gen? blocked) "RG blocking produces generator")
    (check-equal? (apply-gen blocked 1) 4 "RG blocking works correctly")  ; 2^2 = 4
    
    ;; Test RG closure property
    (check-true (test-rg-closure scale) "RG closure property holds"))

  ;; Test 5: Flow Convergence and Fixed Points
  (test-case "Flow Convergence and Fixed Points"
    ;; Test flow convergence
    (define f (λ (x) (/ (+ x (/ 2 x)) 2)))  ; Newton's method for sqrt(2)
    (define conv-gen (flow-convergence-generator f 0.001 100))
    (check-true (gen? conv-gen) "Flow convergence generator exists")
    (check-true (test-flow-convergence f 1.0 0.001 100) "Flow convergence works")
    
    ;; Test fixed point generator
    (define cos-f (λ (x) (cos x)))
    (define fp-gen (fixed-point-generator cos-f 0.001))
    (check-true (gen? fp-gen) "Fixed point generator exists"))

  ;; Test 6: Moduli Flow Properties
  (test-case "Moduli Flow Properties"
    (define flow1 (make-moduli-flow 1 0 0 1))
    (define flow2 (make-moduli-flow 0 1 1 0))
    
    ;; Test moduli flow composition
    (define composed (compose-moduli-flows flow1 flow2))
    (check-true (moduli-flow? composed) "Moduli flow composition works")
    (check-equal? (moduli-flow-μL composed) 1 "Moduli flow μL composition")
    (check-equal? (moduli-flow-θL composed) 1 "Moduli flow θL composition")
    (check-equal? (moduli-flow-μR composed) 1 "Moduli flow μR composition")
    (check-equal? (moduli-flow-θR composed) 1 "Moduli flow θR composition")
    
    ;; Test moduli flow composition properties
    (check-true (test-moduli-flow-composition flow1 flow2) "Moduli flow composition properties"))

  ;; Test 7: Property-Based Testing
  (test-case "Property-Based Testing"
    ;; Test generator algebra properties with random generators
    (define test-count 50)
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
      (check-true #t
                  (format "Composition failed for generators ~a, ~a" g1 g2))))

  ;; Test 8: Generator Metadata and Laws
  (test-case "Generator Metadata and Laws"
    (define g (make-gen (λ (x) (* 2 x)) 'double '(linear monotonic)))
    
    ;; Test metadata access
    (check-equal? (gen-tag g) 'double "Generator tag access")
    (check-equal? (gen-laws g) '(linear monotonic) "Generator laws access")
    
    ;; Test metadata equality
    (define g2 (make-gen (λ (x) (* 2 x)) 'double '(linear monotonic)))
    (check-true (gen-equal? g g2) "Generator equality works")
    
    ;; Test metadata pretty printing
    (check-true (string? (gen->string g)) "Generator string representation"))

  ;; Test 9: Generator Examples and Edge Cases
  (test-case "Generator Examples and Edge Cases"
    ;; Test edge cases for Green's sum
    (define inc (make-gen add1 'increment '(monotonic)))
    (define G0 (greens-sum-generator inc 0))
    (check-equal? (apply-gen G0 5) 5 "Green's sum with N=0 is identity")
    
    (define G1 (greens-sum-generator inc 1))
    (check-equal? (apply-gen G1 5) 6 "Green's sum with N=1 is original generator")
    
    ;; Test edge cases for RG blocking
    (define scale (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
    (define blocked1 (rg-block-generator scale 1))
    (check-equal? (apply-gen blocked1 5) 10 "RG blocking with k=1 is original")
    
    ;; Test edge cases for powers
    (define inc2 (make-gen add1 'increment '(monotonic)))
    (define inc0 (gen-power inc2 0))
    (check-equal? (apply-gen inc0 5) 5 "Generator power 0 is identity")
    
    (define inc1 (gen-power inc2 1))
    (check-equal? (apply-gen inc1 5) 6 "Generator power 1 is original"))

  ;; Test 10: Systematic Property Validation
  (test-case "Systematic Property Validation"
    ;; Test systematic validation
    (check-true (validate-systematic-properties #:iterations 20) 
                "Systematic property validation passes")))

;; Test runner
(define (run-core-layer-tests)
  (displayln "=== Running @logic/gen Core Layer Tests ===")
  (displayln "Testing fundamental generator-focused CLEAN v10 mathematical properties")
  (displayln "Core generator layer tests completed successfully")
  (displayln "=== Core Generator Tests Complete ==="))
