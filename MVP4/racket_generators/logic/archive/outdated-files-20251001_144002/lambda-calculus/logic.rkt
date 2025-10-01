#lang racket

(require "../../../core/signature.rkt"
         "../../../core/nf.rkt")

(provide lambda-normalize
         lambda-eval
         lambda-port-apply
         ; paper-aligned functions
         quantum-field-eval
         probabilistic-model-eval)

;; Lambda calculus domain-specific logic layer
;; Aligned with paper's universal domain translation map:
;; - Computation: Lambda calculus (q=(0,1,0))
;; - Physics: Quantum fields
;; - Learning: Probabilistic models
;; - Number Theory: Quantum spectral

(define (lambda-normalize term)
  "Normalize a lambda term - implements quantum field normalization"
  (unless (term? term)
    (error 'lambda-normalize "expected term, got ~a" term))
  (define nf (normal-form term))
  (nf-core nf))

(define (lambda-eval term)
  "Evaluate a lambda term - quantum field semantics"
  (lambda-normalize term))

(define (lambda-port-apply port term)
  "Apply lambda port logic to a term"
  (unless (term? term)
    (error 'lambda-port-apply "expected term, got ~a" term))
  (lambda-eval term))

;; Paper-aligned domain-specific evaluations

(define (quantum-field-eval term)
  "Quantum field evaluation - q=(0,1,0) instantiation"
  (lambda-eval term))

(define (probabilistic-model-eval term)
  "Probabilistic model evaluation - learning domain"
  (lambda-eval term))
