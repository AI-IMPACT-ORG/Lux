#lang racket

(require "../header.rkt"
         "../kernel.rkt"
         "../signature.rkt"
         "../observers.rkt")

(provide debug-property-tests
         debug-header-arithmetic
         debug-invariant-tests)

;; Debug property-based tests with detailed output
(define (debug-property-tests [num-tests 5])
  "Debug property-based tests with detailed output"
  (displayln "=== Debugging Property-Based Tests ===")
  
  (for ([i num-tests])
    (displayln (format "--- Test ~a ---" i))
    (define h1 (random-header))
    (define h2 (random-header))
    (define h3 (random-header))
    
    (displayln (format "h1: ~a" h1))
    (displayln (format "h2: ~a" h2))
    (displayln (format "h3: ~a" h3))
    
    ;; Test commutativity
    (define add-commutative (equal? (header-add h1 h2) (header-add h2 h1)))
    (displayln (format "Add commutative: ~a" add-commutative))
    (when (not add-commutative)
      (displayln (format "  h1 + h2: ~a" (header-add h1 h2)))
      (displayln (format "  h2 + h1: ~a" (header-add h2 h1))))
    
    ;; Test associativity
    (define add-associative (equal? (header-add (header-add h1 h2) h3)
                                   (header-add h1 (header-add h2 h3))))
    (displayln (format "Add associative: ~a" add-associative))
    (when (not add-associative)
      (displayln (format "  (h1 + h2) + h3: ~a" (header-add (header-add h1 h2) h3)))
      (displayln (format "  h1 + (h2 + h3): ~a" (header-add h1 (header-add h2 h3)))))
    
    ;; Test identity
    (define add-identity (equal? (header-add h1 header-zero) h1))
    (displayln (format "Add identity: ~a" add-identity))
    (when (not add-identity)
      (displayln (format "  h1 + zero: ~a" (header-add h1 header-zero)))
      (displayln (format "  h1: ~a" h1)))
    
    ;; Test norm properties
    (define norm-positive (>= (header-norm h1) 0.0))
    (displayln (format "Norm positive: ~a" norm-positive))
    (when (not norm-positive)
      (displayln (format "  norm(h1): ~a" (header-norm h1))))
    
    ;; Test distance properties
    (define distance-positive (>= (header-distance h1 h2) 0.0))
    (define distance-symmetric (equal? (header-distance h1 h2) (header-distance h2 h1)))
    (displayln (format "Distance positive: ~a" distance-positive))
    (displayln (format "Distance symmetric: ~a" distance-symmetric))
    (when (not distance-positive)
      (displayln (format "  distance(h1, h2): ~a" (header-distance h1 h2))))
    (when (not distance-symmetric)
      (displayln (format "  distance(h1, h2): ~a" (header-distance h1 h2)))
      (displayln (format "  distance(h2, h1): ~a" (header-distance h2 h1))))
    
    (define all-passed (and add-commutative add-associative add-identity
                           norm-positive distance-positive distance-symmetric))
    (displayln (format "All passed: ~a" all-passed))
    (displayln "")))

;; Debug header arithmetic specifically
(define (debug-header-arithmetic)
  "Debug header arithmetic operations"
  (displayln "=== Debugging Header Arithmetic ===")
  
  (define h1 (header 1.0 2.0))
  (define h2 (header 3.0 4.0))
  
  (displayln (format "h1: ~a" h1))
  (displayln (format "h2: ~a" h2))
  
  (displayln (format "h1 + h2: ~a" (header-add h1 h2)))
  (displayln (format "h2 + h1: ~a" (header-add h2 h1)))
  (displayln (format "Commutative: ~a" (equal? (header-add h1 h2) (header-add h2 h1))))
  
  (displayln (format "h1 * h2: ~a" (header-multiply h1 h2)))
  (displayln (format "h2 * h1: ~a" (header-multiply h2 h1)))
  (displayln (format "Multiply commutative: ~a" (equal? (header-multiply h1 h2) (header-multiply h2 h1))))
  
  (displayln (format "h1 + zero: ~a" (header-add h1 header-zero)))
  (displayln (format "Identity: ~a" (equal? (header-add h1 header-zero) h1)))
  
  (displayln (format "norm(h1): ~a" (header-norm h1)))
  (displayln (format "norm(h2): ~a" (header-norm h2)))
  (displayln (format "distance(h1, h2): ~a" (header-distance h1 h2)))
  (displayln (format "distance(h2, h1): ~a" (header-distance h2 h1))))

;; Debug invariant tests
(define (debug-invariant-tests)
  "Debug invariant tests with detailed output"
  (displayln "=== Debugging Invariant Tests ===")
  
  (define k (random-kernel))
  (define t (random-term))
  
  (displayln (format "Random kernel: ~a" k))
  (displayln (format "Random term: ~a" t))
  
  ;; Test residual invisibility
  (displayln "--- Testing Residual Invisibility ---")
  (define residual-invisible (test-residual-invisibility k t))
  (displayln (format "Residual invisible: ~a" residual-invisible))
  
  ;; Test triality involution
  (displayln "--- Testing Triality Involution ---")
  (define triality-involution (test-triality-involution t))
  (displayln (format "Triality involution: ~a" triality-involution))
  
  ;; Test boundary sum
  (displayln "--- Testing Boundary Sum ---")
  (define boundary-sum (test-boundary-sum t))
  (displayln (format "Boundary sum: ~a" boundary-sum))
  
  ;; Test RG closure
  (displayln "--- Testing RG Closure ---")
  (define rg-closure (test-rg-closure k 2.0))
  (displayln (format "RG closure: ~a" rg-closure)))

;; Main debug runner
(module+ main
  (debug-header-arithmetic)
  (debug-property-tests 3)
  (debug-invariant-tests))
