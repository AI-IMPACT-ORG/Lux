#lang racket

(require racket/contract
         racket/match)

(provide ; Header struct with contracts
         (struct-out header)
         header-zero
         header-add
         header-multiply
         header-negate
         header-inverse
         header-norm
         header-distance
         header-equal?
         ; RG blocking operations
         rg-block
         rg-flow
         rg-critical-line?
         ; Header contracts
         header/c
         phase/c
         scale/c
         ; Property-based testing
         random-header
         ; Test runner
         run-property-tests)

;; Header struct with mathematical contracts
(struct header (phase scale)
  #:transparent
  #:guard (λ (phase scale name)
            (unless (real? phase)
              (error 'header "phase must be real, got ~a" phase))
            (unless (real? scale)
              (error 'header "scale must be real, got ~a" scale))
            (values phase scale)))

;; Contracts for type safety
(define header/c (struct/c header real? real?))
(define phase/c real?)
(define scale/c real?)

;; Zero header (additive identity)
(define header-zero (header 0.0 0.0))

;; Header arithmetic operations with contracts
(define/contract (header-add h1 h2)
  (-> header/c header/c header/c)
  "Add two headers component-wise"
  (header (+ (header-phase h1) (header-phase h2))
          (+ (header-scale h1) (header-scale h2))))

(define/contract (header-multiply h1 h2)
  (-> header/c header/c header/c)
  "Multiply two headers component-wise"
  (header (* (header-phase h1) (header-phase h2))
          (* (header-scale h1) (header-scale h2))))

(define/contract (header-negate h)
  (-> header/c header/c)
  "Negate a header"
  (header (- (header-phase h))
          (- (header-scale h))))

(define/contract (header-inverse h)
  (-> header/c header/c)
  "Multiplicative inverse of a header (with zero check)"
  (when (or (zero? (header-phase h)) (zero? (header-scale h)))
    (error 'header-inverse "cannot invert header with zero components: ~a" h))
  (header (/ 1.0 (header-phase h))
          (/ 1.0 (header-scale h))))

(define/contract (header-norm h)
  (-> header/c real?)
  "Euclidean norm of a header"
  (sqrt (+ (sqr (header-phase h)) (sqr (header-scale h)))))

(define/contract (header-distance h1 h2)
  (-> header/c header/c real?)
  "Distance between two headers"
  (header-norm (header-add h1 (header-negate h2))))

;; Header equality with epsilon tolerance for floating-point precision
(define/contract (header-equal? h1 h2 [epsilon 1e-10])
  (->* (header/c header/c) (real?) boolean?)
  "Check if two headers are equal within epsilon tolerance"
  (and (< (abs (- (header-phase h1) (header-phase h2))) epsilon)
       (< (abs (- (header-scale h1) (header-scale h2))) epsilon)))

;; RG (Renormalization Group) Blocking Operations

(define/contract (rg-block h block-size)
  (-> header/c (and/c real? positive?) header/c)
  "Apply RG blocking to a header with block size k"
  (unless (> block-size 0)
    (error 'rg-block "block size must be positive, got ~a" block-size))
  (header (* (header-phase h) block-size)
          (* (header-scale h) block-size)))

(define/contract (rg-block-term term block-size)
  (-> any/c (and/c real? positive?) any/c)
  "Apply RG blocking to a term with block size k"
  (error 'rg-block-term "use rg-block-term from signature.rkt instead"))

;; RG Flow Operations
(define/contract (rg-flow h flow-params)
  (-> header/c (listof real?) header/c)
  "Apply RG flow to a header with flow parameters [μ_L, θ_L, μ_R, θ_R, z, bar_z]"
  (match flow-params
    [(list μL θL μR θR z barz)
     (define phase-flow (+ (header-phase h) (* μL z) (* θL barz)))
     (define scale-flow (+ (header-scale h) (* μR z) (* θR barz)))
     (header phase-flow scale-flow)]
    [_ (error 'rg-flow "expected 6 flow parameters, got ~a" flow-params)]))

;; Critical Line Detection
(define/contract (rg-critical-line? h tolerance)
  (-> header/c real? boolean?)
  "Check if header is on the RG critical line (Fisher self-adjoint condition)"
  (define phase (header-phase h))
  (define scale (header-scale h))
  ;; Critical line condition: |phase - scale| < tolerance
  (< (abs (- phase scale)) tolerance))

;; Property-Based Testing Infrastructure

(define/contract (random-header [phase-range 10.0] [scale-range 10.0])
  (->* () (real? real?) header/c)
  "Generate a random header for property-based testing"
  (header (- (* (random) (* 2 phase-range)) phase-range)
          (- (* (random) (* 2 scale-range)) scale-range)))

(define/contract (random-kernel [header-range 5.0])
  (->* () (real?) any/c)
  "Generate a random kernel for property-based testing"
  (error 'random-kernel "use random-kernel from kernel.rkt instead"))

(define/contract (random-term [header-range 5.0])
  (->* () (real?) any/c)
  "Generate a random term for property-based testing"
  (error 'random-term "use random-term from signature.rkt instead"))

;; Invariant Testing Functions (header-only)

(define/contract (test-boundary-sum term)
  (-> any/c boolean?)
  "Test that bulk equals sum of boundaries"
  (error 'test-boundary-sum "use test-boundary-sum from observers.rkt instead"))

;; Comprehensive Property-Based Test Suite (header-only)
(define/contract (run-property-tests [num-tests 100])
  (->* () (natural-number/c) (listof boolean?))
  "Run comprehensive property-based tests for headers"
  (define results '())
  
  (for ([i num-tests])
    (define h1 (random-header))
    (define h2 (random-header))
    (define h3 (random-header))
    
    ;; Test header arithmetic properties
    (define add-commutative (header-equal? (header-add h1 h2) (header-add h2 h1)))
    (define add-associative (header-equal? (header-add (header-add h1 h2) h3)
                                          (header-add h1 (header-add h2 h3))))
    (define add-identity (header-equal? (header-add h1 header-zero) h1))
    
    ;; Test header norm properties
    (define norm-positive (>= (header-norm h1) 0.0))
    (define distance-positive (>= (header-distance h1 h2) 0.0))
    (define distance-symmetric (equal? (header-distance h1 h2) (header-distance h2 h1)))
    
    (set! results (cons (and add-commutative add-associative add-identity
                            norm-positive distance-positive distance-symmetric)
                       results)))
  
  results)

;; Export the test runner
(provide run-property-tests)
