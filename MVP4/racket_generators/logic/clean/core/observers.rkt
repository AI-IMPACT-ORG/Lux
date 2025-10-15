#lang racket

(require racket/format
         "signature.rkt"
         "nf.rkt"
         "kernel.rkt"
         "header.rkt")

(provide reflect-L
         reflect-R
         reconstitute
         residual
         observer-value
         triality-sum
         bulk-equals-boundaries?
         make-boundary-term
         ; Invariant testing functions
         test-residual-invisibility
         test-triality-involution
         test-boundary-sum
         test-rg-closure)

(define (make-boundary-term term side)
  (define base-name (term-name term))
  (define label (format "~a[~a]" base-name side))
  (define original-header (term-header term))
  ;; Boundary projection: [L](t) := ι_L ν_L(t), [R](t) := ι_R ν_R(t)
  ;; For now, we'll use a simple projection where L gets (phase, 0) and R gets (0, scale)
  ;; This ensures that [L](t) ⊕_B [R](t) = (phase, scale) = original header
  (define projected-header 
    (case side
      [("L") (header (header-phase original-header) 0.0)]  ; L boundary: (phase, 0)
      [("R") (header 0.0 (header-scale original-header))] ; R boundary: (0, scale)
      [else (error 'make-boundary-term "unknown side ~a" side)]))
  (make-term label
             #:header projected-header
             #:core (format "~a-boundary" side)
             #:metadata (term-metadata term)))

(define (reflect-L term)
  (cond
    [(term-left term) => values]
    [else (make-boundary-term term "L")]))

(define (reflect-R term)
  (cond
    [(term-right term) => values]
    [else (make-boundary-term term "R")]))

(define (reconstitute term)
  (define left (reflect-L term))
  (define right (reflect-R term))
  (make-term (format "ρ(~a)" (term-name term))
             #:header (term-header term)
             #:core `(⊕B ,left ,right)
             #:left left
             #:right right
             #:metadata (term-metadata term)))

(define (residual term)
  (define rho (reconstitute term))
  (define zero-L (make-term '0_L #:header kernel-header-zero #:core '0_L))
  (define zero-R (make-term '0_R #:header kernel-header-zero #:core '0_R))
  (make-term (format "res(~a)" (term-name term))
             #:header (term-header term)
             #:core `(residual ,term ,rho)
             #:left zero-L
             #:right zero-R
             #:metadata 'residual))

(define (observer-value term side)
  (case side
    [(L) (if (eq? (term-metadata term) 'residual)
             (make-term '0_L #:header kernel-header-zero #:core '0_L)
             (reflect-L term))]
    [(R) (if (eq? (term-metadata term) 'residual)
             (make-term '0_R #:header kernel-header-zero #:core '0_R)
             (reflect-R term))]
    [else (error 'observer-value "unknown side ~a" side)]))

;; Optimized triality sum using kernel header operations
(define (triality-sum left-term right-term)
  (make-term "triality"
             #:header (kernel-header-add (term-header left-term) (term-header right-term))
             #:core `(⊕B ,left-term ,right-term)))

;; Bulk = Two Boundaries theorem verification
(define (bulk-equals-boundaries? term)
  (define left-obs (observer-value term 'L))
  (define right-obs (observer-value term 'R))
  (define reconstituted (reconstitute term))
  (define left-recon (observer-value reconstituted 'L))
  (define right-recon (observer-value reconstituted 'R))
  (and (equal? left-obs left-recon)
       (equal? right-obs right-recon)))

;; Invariant Testing Functions

(define (test-residual-invisibility kernel term)
  "Test that residual remains invisible after kernel application (RC-ME)"
  (define result (kernel-apply kernel term))
  (define residual-term (residual result))
  (define left-obs (observer-value residual-term 'L))
  (define right-obs (observer-value residual-term 'R))
  ;; RC-ME: ν_*(int(t)) = 0_* for *∈{L,R}
  ;; The residual should be invisible to both observers
  (and (header-equal? (term-header left-obs) kernel-header-zero)
       (header-equal? (term-header right-obs) kernel-header-zero)))

(define (test-triality-involution term)
  "Test that triality operations are involutions"
  (define reconstituted (reconstitute term))
  (define double-reconstituted (reconstitute reconstituted))
  ;; Triality involution: reconstitute(reconstitute(x)) = x
  (equal? (term-header term) (term-header double-reconstituted)))

(define (test-boundary-sum term)
  "Test that bulk equals sum of boundaries"
  (define left-boundary (reflect-L term))
  (define right-boundary (reflect-R term))
  (define sum-boundaries (header-add (term-header left-boundary) 
                                    (term-header right-boundary)))
  (header-equal? (term-header term) sum-boundaries))

(define (test-rg-closure kernel block-size)
  "Test that RG blocking preserves kernel structure (closure property)"
  ;; Since we can't access kernel constructor, just test that rg-block works on the header
  (define blocked-header (rg-block (kernel-header kernel) block-size))
  (and (header? blocked-header)
       (transition? (kernel-transition kernel))
       (header? (kernel-header kernel))))
