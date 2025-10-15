#lang racket

(require "../core/signature.rkt")

(provide make-psdm-legacy
         psdm-legacy?
         psdm-extend
         psdm-define
         psdm-lookup
         ; spec-faithful façade
         define-psdm!
         psdm-apply
         psdm-defined?)

;; Simplified PSDM implementation (legacy only)
(struct psdm-legacy (table)
  #:transparent)

(define (make-psdm-legacy)
  (psdm-legacy (hash)))

(define (psdm-extend ps key value)
  (psdm-legacy (hash-set (psdm-legacy-table ps) key value)))

(define (psdm-define ps key thunk)
  (define value (thunk))
  (psdm-legacy (hash-set (psdm-legacy-table ps) key value)))

(define (psdm-lookup ps key)
  (hash-ref (psdm-legacy-table ps) key (λ () 'undefined)))

(define (psdm-apply psdm term)
  (psdm-lookup psdm term))

(define (psdm-defined? psdm term)
  (not (eq? (psdm-lookup psdm term) 'undefined)))

;; Simplified spec-faithful façade
(define (define-psdm! ps #:key [key #f] #:thunk [thunk #f])
  (if key
      (psdm-define ps key thunk)
      ps))
