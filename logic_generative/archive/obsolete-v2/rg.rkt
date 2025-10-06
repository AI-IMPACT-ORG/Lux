#lang racket

;; @logic/gen RG and Convergence Meta-Generators
;; Implements RG blocking and convergence utilities for generator flows

(require racket/contract
         racket/math
         racket/hash
         "core.rkt")

(provide (all-defined-out))

;; ============================================================================
;; RG BLOCKING META-GENERATORS
;; ============================================================================

;; RG blocking with header-only reparametrization
(define (rg-block-generator K k)
  "Apply RG blocking to generator K with block size k"
  (unless (and (integer? k) (> k 0))
    (error 'rg-block-generator "k must be positive integer, got ~a" k))
  
  ;; RG blocking: K^(k) = K^k with header-only reparametrization
  (define blocked-kernel (gen-power K k))
  (define blocked-meta (hash-set (hash-set (gen-meta blocked-kernel) 
                                          'rg-blocked #t)
                                'closure #t))
  
  (gen (gen-apply blocked-kernel) blocked-meta))

;; RG flow generator
(define (rg-flow-generator K flow-fn)
  "Create RG flow generator from kernel K and flow function"
  (define flow-kernel
    (make-gen (λ (term) (flow-fn (apply-gen K term))) 'rg-flow '(flow)))
  flow-kernel)

;; RG scaling generator
(define (rg-scale-generator K scale-factor)
  "Create RG scaling generator"
  (define scale-kernel
    (make-gen (λ (term) (* scale-factor (apply-gen K term))) 'rg-scale '(scaling)))
  scale-kernel)

;; ============================================================================
;; CONVERGENCE META-GENERATORS
;; ============================================================================

;; Flow convergence detector
(define (flow-convergence-generator f tolerance max-iterations)
  "Create flow convergence generator with tolerance and max iterations"
  (define convergence-kernel
    (make-gen (λ (x) (converge-flow f x tolerance max-iterations)) 
              'convergence '(heuristic)))
  convergence-kernel)

;; Helper: Converge flow function
(define (converge-flow f x tolerance max-iter)
  "Converge flow function f starting from x"
  (let loop ([current x] [iter 0])
    (cond
      [(>= iter max-iter) current]  ; Max iterations reached
      [else
       (define next (f current))
       (define diff (abs (- next current)))
       (if (< diff tolerance)
           next  ; Converged
           (loop next (+ iter 1)))])))

;; Fixed point generator
(define (fixed-point-generator f tolerance)
  "Create fixed point generator"
  (define fp-kernel
    (make-gen (λ (x) (find-fixed-point f x tolerance)) 'fixed-point '(convergence)))
  fp-kernel)

;; Helper: Find fixed point
(define (find-fixed-point f x tolerance)
  "Find fixed point of function f starting from x"
  (let loop ([current x])
    (define next (f current))
    (define diff (abs (- next current)))
    (if (< diff tolerance)
        next
        (loop next))))

;; ============================================================================
;; MODULI FLOW GENERATORS
;; ============================================================================

;; Moduli flow generator
(struct moduli-flow (μL θL μR θR) #:transparent)

;; Create moduli flow generator
(define (make-moduli-flow μL θL μR θR)
  "Create moduli flow generator with four parameters"
  (moduli-flow μL θL μR θR))

;; Apply moduli flow to term
(define (apply-moduli-flow flow term)
  "Apply moduli flow to term"
  (unless (moduli-flow? flow)
    (error 'apply-moduli-flow "expected moduli flow, got ~a" flow))
  
  ;; This will be connected to Class moduli when implemented
  (error 'apply-moduli-flow "implement using Class moduli flows"))

;; Moduli flow composition
(define (compose-moduli-flows flow1 flow2)
  "Compose two moduli flows"
  (unless (and (moduli-flow? flow1) (moduli-flow? flow2))
    (error 'compose-moduli-flows "expected moduli flows"))
  
  (moduli-flow (+ (moduli-flow-μL flow1) (moduli-flow-μL flow2))
               (+ (moduli-flow-θL flow1) (moduli-flow-θL flow2))
               (+ (moduli-flow-μR flow1) (moduli-flow-μR flow2))
               (+ (moduli-flow-θR flow1) (moduli-flow-θR flow2))))

;; ============================================================================
;; FEYNMAN PATH GENERATORS
;; ============================================================================

;; Feynman path generator
(define (feynman-path-generator J)
  "Create Feynman path generator for action J"
  (define path-kernel
    (make-gen (λ (path) (evaluate-path J path)) 'feynman-path '(quantum)))
  path-kernel)

;; Helper: Evaluate path (placeholder)
(define (evaluate-path J path)
  "Evaluate path with action J"
  ;; This will be connected to Class Feynman when implemented
  (error 'evaluate-path "implement using Class Feynman"))

;; Sum over histories generator
(define (sum-over-histories-generator J paths)
  "Create sum over histories generator"
  (define sum-kernel
    (make-gen (λ (x) (sum-paths J paths x)) 'sum-histories '(quantum)))
  sum-kernel)

;; Helper: Sum paths (placeholder)
(define (sum-paths J paths x)
  "Sum over all paths"
  ;; This will be connected to Class Feynman when implemented
  (error 'sum-paths "implement using Class Feynman"))

;; ============================================================================
;; CONVERGENCE TESTING UTILITIES
;; ============================================================================

;; Test RG closure property
(define (test-rg-closure K)
  "Test that RG blocking preserves generator structure"
  (define blocked (rg-block-generator K 2))
  (and (gen? blocked)
       (hash-has-key? (gen-meta blocked) 'tag)
       (hash-has-key? (gen-meta blocked) 'laws)))

;; Test flow convergence
(define (test-flow-convergence f x tolerance max-iter)
  "Test if flow function f converges"
  (define result (converge-flow f x tolerance max-iter))
  (define final-value (f result))
  (< (abs (- final-value result)) tolerance))

;; Test moduli flow composition
(define (test-moduli-flow-composition flow1 flow2)
  "Test moduli flow composition"
  (define composed (compose-moduli-flows flow1 flow2))
  (and (moduli-flow? composed)
       (= (moduli-flow-μL composed) (+ (moduli-flow-μL flow1) (moduli-flow-μL flow2)))
       (= (moduli-flow-θL composed) (+ (moduli-flow-θL flow1) (moduli-flow-θL flow2)))
       (= (moduli-flow-μR composed) (+ (moduli-flow-μR flow1) (moduli-flow-μR flow2)))
       (= (moduli-flow-θR composed) (+ (moduli-flow-θR flow1) (moduli-flow-θR flow2)))))

;; ============================================================================
;; RG AND CONVERGENCE EXAMPLES
;; ============================================================================

;; Example: RG blocking
(define (example-rg-blocking)
  "Example usage of RG blocking"
  (define K (make-gen (λ (x) (* 2 x)) 'scale '(linear)))
  (define K-blocked (rg-block-generator K 3))
  (printf "Original: ~a~n" (apply-gen K 5))
  (printf "Blocked: ~a~n" (apply-gen K-blocked 5)))

;; Example: Flow convergence
(define (example-flow-convergence)
  "Example usage of flow convergence"
  (define f (λ (x) (/ (+ x (/ 2 x)) 2)))  ; Newton's method for sqrt(2)
  (define conv-gen (flow-convergence-generator f 0.001 100))
  (define result (apply-gen conv-gen 1.0))
  (printf "Converged to: ~a~n" result))

;; Example: Fixed point
(define (example-fixed-point)
  "Example usage of fixed point generator"
  (define f (λ (x) (cos x)))  ; Fixed point around 0.739
  (define fp-gen (fixed-point-generator f 0.001))
  (define result (apply-gen fp-gen 1.0))
  (printf "Fixed point: ~a~n" result))

;; Example: Moduli flow
(define (example-moduli-flow)
  "Example usage of moduli flow"
  (define flow1 (make-moduli-flow 1 0 0 1))
  (define flow2 (make-moduli-flow 0 1 1 0))
  (define composed (compose-moduli-flows flow1 flow2))
  (printf "Composed moduli flow: μL=~a, θL=~a, μR=~a, θR=~a~n"
          (moduli-flow-μL composed)
          (moduli-flow-θL composed)
          (moduli-flow-μR composed)
          (moduli-flow-θR composed)))
