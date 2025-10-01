#lang racket

(require "../core/signature.rkt"
         "../core/nf.rkt")

(provide moduli?
         moduli-μL
         moduli-θL
         moduli-μR
         moduli-θR
         moduli-z
         moduli-barz
         current-moduli
         set-moduli!
         with-moduli
         apply-header-flow
         ; spec façade name
         normal-form-4mod)

(struct moduli (μL θL μR θR z barz)
  #:transparent)

(define current-moduli
  (make-parameter (moduli 0 0 0 0 1 1)))

(define (set-moduli! #:μL [μL 0]
                     #:θL [θL 0]
                     #:μR [μR 0]
                     #:θR [θR 0]
                     #:z [z 1]
                     #:barz [barz 1])
  (current-moduli (moduli μL θL μR θR z barz)))

(define (with-moduli new-moduli thunk)
  (parameterize ([current-moduli (if (moduli? new-moduli)
                                    new-moduli
                                    (error 'with-moduli "expected moduli, got ~a" new-moduli))])
    (thunk)))

(define (apply-header-flow term)
  (define base (normal-form term))
  (define m (current-moduli))
  ;; Boundary-aware: apply flows to left and right separately, then recombine
  (define left-phase (moduli-θL m))
  (define right-phase (moduli-θR m))
  (define left-scale (moduli-μL m))
  (define right-scale (moduli-μR m))
  (define new-phase (+ (nf-phase base) left-phase right-phase))
  (define new-scale (+ (nf-scale base) left-scale right-scale))
  (nf new-phase new-scale (nf-core base) (nf-residual base)))

(define (normal-form-4mod term)
  (apply-header-flow term))
