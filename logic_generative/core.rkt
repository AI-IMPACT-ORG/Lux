#lang racket

;; @logic/gen Core Generator Operations
;; 
;; PURPOSE: Implements the core generator data model and operations for CLEAN V10 CLASS
;; STATUS: Active - Core foundation for all generator-based operations
;; DEPENDENCIES: None (foundational module)
;; TESTS: Tested via spec-aligned-comprehensive-tests.rkt
;;
;; This module provides:
;; - Generator struct and metadata management
;; - Generator composition and application operations
;; - RG blocking and flow convergence generators
;; - Fixed point and moduli flow generators
;; - Domain port generator framework
;;
;; ARCHITECTURE: Core layer of CLEAN V10 CLASS onion architecture

(require racket/contract
         racket/match
         racket/function
         racket/hash)

(provide (all-defined-out))

;; ============================================================================
;; GENERATOR DATA MODEL
;; ============================================================================

;; Generator struct: function with metadata
(struct gen (apply meta) #:transparent)

;; Generator metadata constructor
(define (make-gen-meta tag laws . rest)
  (apply hash 'tag tag 'laws laws rest))

;; ============================================================================
;; CORE GENERATOR OPERATIONS
;; ============================================================================

;; Identity generator
(define (gen-id)
  (gen identity (make-gen-meta 'identity '(associativity identity))))

;; Generator composition (Kleisli composition)
(define (gen-compose g1 g2)
  (gen (compose (gen-apply g2) (gen-apply g1))
       (hash-set (gen-meta g1) 'composed-with (gen-tag g2))))

;; Generator application
(define (apply-gen g x)
  ((gen-apply g) x))

;; Generator iteration (powers)
(define (gen-power g n)
  (cond
    [(= n 0) (gen-id)]
    [(= n 1) g]
    [else (gen-compose g (gen-power g (- n 1)))]))

;; Generator sum (Green's function)
(define (greens-sum-generator K N)
  "Generate Green's sum G_N = I + K + K² + ... + K^N"
  (unless (and (integer? N) (>= N 0))
    (error 'greens-sum-generator "N must be non-negative integer, got ~a" N))
  
  (cond
    [(= N 0) (gen-id)]
    [(= N 1) K]
    [else
     ;; G_N = I + K + K² + ... + K^N
     (let-values ([(result current)
                   (for/fold ([result (gen-id)]
                              [current K])
                             ([i (in-range N)])
                     (values (gen-compose result current)
                             (gen-compose current K)))])
       result)]))

;; ============================================================================
;; GENERATOR LAWS AND VALIDATION
;; ============================================================================

;; Test associativity of generator composition
(define (test-associativity g1 g2 g3)
  "Test that generator composition is associative"
  (define left-assoc (gen-compose (gen-compose g1 g2) g3))
  (define right-assoc (gen-compose g1 (gen-compose g2 g3)))
  
  ;; Test on numeric inputs only
  (define test-inputs '(0 1 2 3 4 5))
  (for/and ([x test-inputs])
    (equal? (apply-gen left-assoc x) (apply-gen right-assoc x))))

;; Test identity laws
(define (test-identity g)
  "Test that identity generator acts as identity"
  (define test-inputs '(0 1 2 3 4 5))
  (for/and ([x test-inputs])
    (and (equal? (apply-gen (gen-compose (gen-id) g) x) (apply-gen g x))
         (equal? (apply-gen (gen-compose g (gen-id)) x) (apply-gen g x)))))

;; ============================================================================
;; GENERATOR UTILITIES
;; ============================================================================

;; Create generator from function
(define (make-gen f tag . laws)
  (gen f (make-gen-meta tag (if (null? laws) '() (car laws)))))

;; Generator metadata accessors
(define (gen-tag g)
  (hash-ref (gen-meta g) 'tag))

(define (gen-laws g)
  (hash-ref (gen-meta g) 'laws))

;; Generator equality (structural)
(define (gen-equal? g1 g2)
  (and (equal? (gen-tag g1) (gen-tag g2))
       (equal? (gen-laws g1) (gen-laws g2))))

;; Generator pretty printing
(define (gen->string g)
  (format "#<gen:~a:~a>" (gen-tag g) (gen-laws g)))

;; ============================================================================
;; GENERATOR EXAMPLES
;; ============================================================================

;; Simple increment generator
(define (inc-gen)
  (make-gen add1 'increment '(monotonic)))

;; Simple double generator  
(define (double-gen)
  (make-gen (λ (x) (* 2 x)) 'double '(linear)))

;; Composition example
(define (inc-then-double-gen)
  (gen-compose (double-gen) (inc-gen)))

;; Power example
(define (inc-power-3-gen)
  (gen-power (inc-gen) 3))

;; Green's sum example
(define (inc-greens-5-gen)
  (greens-sum-generator (inc-gen) 5))
