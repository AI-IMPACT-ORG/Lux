#lang racket

(require "../../../core/signature.rkt"
         "../../../core/nf.rkt")

(provide qft-euclidean-convert
         qft-minkowski-convert
         qft-eval
         qft-port-apply
         ; paper-aligned functions
         feynman-path-eval
         stochastic-model-eval)

;; QFT/Path integrals domain-specific logic layer
;; Aligned with paper's universal domain translation map:
;; - Computation: Path integrals (q=(0,0,1))
;; - Physics: Feynman paths
;; - Learning: Stochastic models
;; - Number Theory: Path spectral

(define (qft-euclidean-convert term)
  "Convert term to Euclidean QFT representation (real) - Feynman path integral"
  (unless (term? term)
    (error 'qft-euclidean-convert "expected term, got ~a" term))
  (define nf (normal-form term))
  (nf-phase nf))  ; Euclidean: real part only

(define (qft-minkowski-convert term)
  "Convert term to Minkowski QFT representation (complex) - stochastic path"
  (unless (term? term)
    (error 'qft-minkowski-convert "expected term, got ~a" term))
  (define nf (normal-form term))
  (make-rectangular (nf-phase nf) (nf-scale nf)))  ; Minkowski: complex

(define (qft-eval term #:euclidean? [euclidean? #t])
  "Evaluate a term as QFT representation - path integral semantics"
  (if euclidean?
      (qft-euclidean-convert term)
      (qft-minkowski-convert term)))

(define (qft-port-apply port term)
  "Apply QFT port logic to a term"
  (unless (term? term)
    (error 'qft-port-apply "expected term, got ~a" term))
  (define euclidean? (if (and (hash? port) (hash-has-key? port 'euclidean?))
                         (hash-ref port 'euclidean?)
                         #t))
  (qft-eval term #:euclidean? euclidean?))

;; Paper-aligned domain-specific evaluations

(define (feynman-path-eval term)
  "Feynman path evaluation - q=(0,0,1) instantiation"
  (qft-eval term #:euclidean? #t))

(define (stochastic-model-eval term)
  "Stochastic model evaluation - learning domain"
  (qft-eval term #:euclidean? #f))
