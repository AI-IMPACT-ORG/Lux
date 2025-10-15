#lang racket

(require "../../core/signature.rkt"
         "../../core/kernel.rkt"
         "../../core/nf.rkt")

(provide make-domain-port
         domain-port-eval
         domain-port-kernel
         domain-port-carrier
         domain-port-totality-predicate
         domain-port-q-vector
         domain-port?
         ; specific port constructors aligned with paper's domain instantiations
         make-turing-port      ; q=(1,0,0) - Turing machines, classical fields, deterministic models
         make-lambda-port      ; q=(0,1,0) - Lambda calculus, quantum fields, probabilistic models  
         make-path-port        ; q=(0,0,1) - Path integrals, Feynman paths, stochastic models
         make-infoflow-port    ; Information measures, Fisher metric, spectral landscape
         ; legacy aliases for backward compatibility
         make-boolean-port
         make-qft-port)

;; Unified domain port interface - aligned with paper's L/B/R structure
;; Ports implement the universal domain translation map from Table 1
(struct domain-port (kernel carrier totality-predicate q-vector)
  #:transparent)

;; Simplified constructor with q-vector for domain instantiation
(define (make-domain-port kernel carrier totality-predicate q-vector)
  (domain-port kernel carrier totality-predicate q-vector))

(define (domain-port-eval port term)
  (unless (domain-port? port)
    (error 'domain-port-eval "expected domain port, got ~a" port))
  (if ((domain-port-totality-predicate port) term)
      (kernel-apply (domain-port-kernel port) term)
      'undefined))

;; Domain-specific port constructors aligned with paper's universal translation map

;; Turing machines port: q=(1,0,0) - classical fields, deterministic models
(define (make-turing-port #:threshold [threshold 0.5])
  (define turing-kernel (kernel kernel-header-zero 
                        (transition 'turing 
                                   (λ (term) term)  ; Pure renaming - L/B/R structure preserved
                                   '())))
  (make-domain-port turing-kernel 'turing 
                   (λ (term) #t)  ; Always defined for deterministic computation
                   '(1 0 0)))     ; q-vector for Turing machines

;; Lambda calculus port: q=(0,1,0) - quantum fields, probabilistic models
(define (make-lambda-port)
  (define lambda-kernel (kernel kernel-header-zero
                        (transition 'lambda
                                   (λ (term) term)  ; Pure renaming - quantum field structure
                                   '())))
  (make-domain-port lambda-kernel 'lambda
                   (λ (term) (halts-within-regulator? term))
                   '(0 1 0)))     ; q-vector for lambda calculus

;; Path integrals port: q=(0,0,1) - Feynman paths, stochastic models
(define (make-path-port #:euclidean? [euclidean? #t])
  (define carrier (if euclidean? 'euclidean 'minkowski))
  (define path-kernel (kernel kernel-header-zero
                        (transition carrier
                                   (λ (term) term)  ; Pure renaming - Feynman path structure
                                   '())))
  (make-domain-port path-kernel carrier
                   (λ (term) (converges-within-regulator? term))
                   '(0 0 1)))     ; q-vector for path integrals

;; Information flow port: Fisher metric, spectral landscape
(define (make-infoflow-port)
  (define infoflow-kernel (kernel kernel-header-zero
                        (transition 'infoflow
                                   (λ (term) term)  ; Pure renaming - information geometry
                                   '())))
  (make-domain-port infoflow-kernel 'infoflow
                   (λ (term) (flows-within-regulator? term))
                   '(0 0 0)))     ; Information measures (no specific q-vector)

;; Legacy aliases for backward compatibility
(define (make-boolean-port #:threshold [threshold 0.5])
  (make-turing-port #:threshold threshold))

(define (make-qft-port #:euclidean? [euclidean? #t])
  (make-path-port #:euclidean? euclidean?))

;; Helper predicates - these are pure metadata checks, not domain logic
(define (halts-within-regulator? term)
  (and (term? term)
       (not (eq? (term-metadata term) 'non-halting))
       (not (eq? (term-metadata term) 'infinite-loop))))

(define (converges-within-regulator? term)
  (and (term? term)
       (not (eq? (term-metadata term) 'non-converging))
       (not (eq? (term-metadata term) 'divergent))))

(define (flows-within-regulator? term)
  (and (term? term)
       (not (eq? (term-metadata term) 'non-flowing))
       (not (eq? (term-metadata term) 'blocked))))
