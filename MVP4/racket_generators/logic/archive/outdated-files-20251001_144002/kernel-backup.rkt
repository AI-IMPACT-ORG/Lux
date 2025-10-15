#lang racket

(require racket/match
         racket/list
         racket/format
         "signature.rkt")

(provide (struct-out kernel)
         (struct-out transition)
         kernel-compose
         transition-compose
         identity-kernel
         kernel-header-add
         kernel-header-product
         kernel-header-zero
         kernel-header
         greens-sum
         kernel-residual-invisible?
         kernel-rg-block)

;; Kernel: bulk term with header and internal transition
;; K ≡ (Δφ,ΔΛ; op) with internal transition ⟦K⟧
(struct kernel (header transition) #:transparent)

;; Transition: carrier-specific step semantics
;; transition: Σ_B × Ops → Bag(Σ_B × Weight × Event*)
(struct transition (carrier step-weight event-sequence) #:transparent)

;; Identity kernel: zero header, delta transition
(define (identity-kernel)
  (kernel kernel-header-zero 
          (transition 'identity 
                     (λ (term) term)  ; identity function
                     '())))

;; Zero header constant
(define kernel-header-zero '(0 . 0))

;; Header operations (additive for phase/scale)
(define (kernel-header-add h1 h2)
  (match* (h1 h2)
    [((cons p1 s1) (cons p2 s2)) (cons (+ p1 p2) (+ s1 s2))]
    [(_ _) (error 'kernel-header-add "invalid headers ~a ~a" h1 h2)]))

(define (kernel-header-product h1 h2)
  (match* (h1 h2)
    [((cons p1 s1) (cons p2 s2)) (cons (* p1 p2) (* s1 s2))]
    [(_ _) (error 'kernel-header-product "invalid headers ~a ~a" h1 h2)]))

;; Sequential composition (Kleisli composition on bags)
(define (kernel-compose k1 k2)
  (kernel (kernel-header-add (kernel-header k1) (kernel-header k2))
          (transition-compose (kernel-transition k1) (kernel-transition k2))))

;; Transition composition (Kleisli composition)
(define (transition-compose t1 t2)
  (transition (transition-carrier t2)  ; Use carrier from second transition
              (λ (term)
                (define result1 ((transition-step-weight t1) term))
                (define result2 ((transition-step-weight t2) result1))
                result2)
              (append (transition-event-sequence t1) 
                      (transition-event-sequence t2))))

;; Kernel application: K ⊗_B t
;; Note: This requires normal-form from nf.rkt - moved to avoid circular dependency
(define (kernel-apply kernel term)
  (error 'kernel-apply "use kernel-apply from nf.rkt instead"))

;; Create kernel from normal form (moved to nf.rkt to avoid circular dependency)
;; This is now a placeholder - actual implementation in nf.rkt
(define (kernel-from-nf nf)
  (error 'kernel-from-nf "use kernel-normal-form from nf.rkt instead"))

;; Optimized Green's sum: G_N = I_B ⊕_B K ⊕_B K² ⊕_B ... ⊕_B K^N
(define (greens-sum kernel N)
  (unless (and (integer? N) (>= N 0))
    (error 'greens-sum "N must be non-negative integer, got ~a" N))
  (cond
    [(= N 0) (identity-kernel)]
    [(= N 1) kernel]
    [else
     ;; G_N = I + K + K² + ... + K^N (CORRECTED)
     ;; Compute sum by accumulating powers correctly
     (let-values ([(result current)
                   (for/fold ([result (identity-kernel)]
                              [current kernel])
                             ([i (in-range N)])
                     (values (kernel-compose result current)
                             (kernel-compose current kernel)))])
       result)]))

;; RC-ME: residual invisibility under micro-evolution
;; ν_*(int(K ⊗_B t)) = 0_* for *∈{L,R}
(define (kernel-residual-invisible? kernel term)
  (define applied (kernel-apply kernel term))
  ;; Simplified check: residual should have zero observer values
  (define residual-header (term-header applied))
  (equal? residual-header kernel-header-zero))

;; RG blocking: K^(k) = K^k with header-only reparametrization
(define (kernel-rg-block kernel k)
  (unless (and (integer? k) (> k 0))
    (error 'kernel-rg-block "k must be positive integer, got ~a" k))
  (for/fold ([result kernel])
            ([i (in-range (- k 1))])
    (kernel-compose result kernel)))
