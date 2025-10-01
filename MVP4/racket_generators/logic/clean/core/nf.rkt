#lang racket

(require racket/match
         "signature.rkt"
         "kernel.rkt"
         "header.rkt")

(provide (struct-out nf)
         normal-form
         normal-form-parametric
         normal-form-with-flow
         normal-form-to-kernel
         kernel-normal-form
         normal-form-rg-block
         kernel-apply
         kernel-from-nf)

(struct nf (phase scale core residual)
  #:transparent)

(define (normal-form term)
  (unless (term? term)
    (error 'normal-form "expected term, got ~a" term))
  (match (term-header term)
    [(? header? h)
     (nf (header-phase h) (header-scale h) (term-core term) #f)]
    [(cons phase scale)
     (nf phase scale (term-core term) #f)]
    [_ (error 'normal-form "header must be header struct or cons pair, got ~a" (term-header term))]))

(define (normal-form-parametric term phase-flow scale-flow)
  (define base (normal-form term))
  (define new-phase (phase-flow (nf-phase base)))
  (define new-scale (scale-flow (nf-scale base)))
  (nf new-phase new-scale (nf-core base) (nf-residual base)))

(define (normal-form-with-flow term #:phase [phase-flow identity] #:scale [scale-flow identity])
  (normal-form-parametric term phase-flow scale-flow))

;; Convert normal form to kernel
(define (normal-form-to-kernel nf)
  (kernel (cons (nf-phase nf) (nf-scale nf))
          (transition 'nf-derived
                     (λ (term) (nf-core nf))
                     '())))

;; Create kernel from term via normal form
(define (kernel-normal-form term)
  (normal-form-to-kernel (normal-form term)))

;; Kernel application: K ⊗_B t
(define (kernel-apply kernel term)
  (unless (term? term)
    (error 'kernel-apply "expected term, got ~a" term))
  (define nf (normal-form term))
  (define transition (kernel-transition kernel))
  (define new-core ((transition-step-weight transition) term))  ; Pass the full term, not just core
  (define term-header-struct (header (nf-phase nf) (nf-scale nf)))
  (define new-header (kernel-header-add (kernel-header kernel) term-header-struct))
  (make-term (format "K(~a)" (term-name term))
             #:header new-header
             #:core new-core
             #:metadata 'kernel-applied))

;; Create kernel from normal form
(define (kernel-from-nf nf)
  (normal-form-to-kernel nf))

;; Optimized RG blocking: direct header computation without kernel creation
(define (normal-form-rg-block term k #:phase [phase-flow identity] #:scale [scale-flow identity])
  (define base-nf (normal-form term))
  (define base-header (cons (nf-phase base-nf) (nf-scale base-nf)))
  ;; RG blocking: multiply header by k
  (define blocked-header (cons (* (car base-header) k) (* (cdr base-header) k)))
  (nf (phase-flow (car blocked-header))
      (scale-flow (cdr blocked-header))
      (nf-core base-nf)  ; Core unchanged
      #f))
