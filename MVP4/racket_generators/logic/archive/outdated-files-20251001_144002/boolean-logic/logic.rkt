#lang racket

(require "../../../core/signature.rkt"
         "../../../core/nf.rkt")

(provide boolean-threshold
         boolean-eval
         boolean-port-apply
         ; paper-aligned functions
         turing-eval
         classical-field-eval
         deterministic-model-eval)

;; Boolean/Turing domain-specific logic layer
;; Aligned with paper's universal domain translation map:
;; - Computation: Turing machines (q=(1,0,0))
;; - Physics: Classical fields  
;; - Learning: Deterministic models
;; - Number Theory: Classical spectral

(define (boolean-threshold term threshold)
  "Apply boolean threshold logic to a term - implements deterministic computation"
  (unless (term? term)
    (error 'boolean-threshold "expected term, got ~a" term))
  (define nf (normal-form term))
  (if (> (nf-phase nf) threshold) 1 0))

(define (boolean-eval term #:threshold [threshold 0.5])
  "Evaluate a term as a boolean value - Turing machine semantics"
  (boolean-threshold term threshold))

(define (boolean-port-apply port term)
  "Apply boolean port logic to a term"
  (unless (term? term)
    (error 'boolean-port-apply "expected term, got ~a" term))
  (define threshold (if (and (hash? port) (hash-has-key? port 'threshold))
                        (hash-ref port 'threshold)
                        0.5))
  (boolean-eval term #:threshold threshold))

;; Paper-aligned domain-specific evaluations

(define (turing-eval term)
  "Turing machine evaluation - q=(1,0,0) instantiation"
  (boolean-eval term #:threshold 0.5))

(define (classical-field-eval term)
  "Classical field evaluation - deterministic physics"
  (boolean-eval term #:threshold 0.5))

(define (deterministic-model-eval term)
  "Deterministic model evaluation - learning domain"
  (boolean-eval term #:threshold 0.5))
