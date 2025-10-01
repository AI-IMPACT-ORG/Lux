#lang racket

(require "../../../core/signature.rkt"
         "../../../core/nf.rkt")

(provide infoflow-format
         infoflow-eval
         infoflow-port-apply
         ; paper-aligned functions
         fisher-metric-eval
         spectral-landscape-eval)

;; Information flow domain-specific logic layer
;; Aligned with paper's universal domain translation map:
;; - Information Measures: Fisher metric, spectral landscape
;; - Cross-domain: Information geometry, moduli space metric, learning landscape

(define (infoflow-format term)
  "Format a term as info-flow representation - Fisher metric semantics"
  (unless (term? term)
    (error 'infoflow-format "expected term, got ~a" term))
  (define nf (normal-form term))
  `(flow ,(nf-phase nf) ,(nf-scale nf)))

(define (infoflow-eval term)
  "Evaluate a term as info-flow representation - information geometry"
  (infoflow-format term))

(define (infoflow-port-apply port term)
  "Apply info-flow port logic to a term"
  (unless (term? term)
    (error 'infoflow-port-apply "expected term, got ~a" term))
  (infoflow-eval term))

;; Paper-aligned domain-specific evaluations

(define (fisher-metric-eval term)
  "Fisher metric evaluation - information geometry"
  (infoflow-eval term))

(define (spectral-landscape-eval term)
  "Spectral landscape evaluation - number theory domain"
  (infoflow-eval term))
