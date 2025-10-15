#lang racket

(require racket/format
         "signature.rkt"
         "nf.rkt")

(provide delta
         umbral-commutes-with-nf?)

(define (delta term)
  (make-term (format "Δ(~a)" (term-name term))
             #:header (term-header term)
             #:core `(Δ ,(term-core term))
             #:metadata 'delta))

(define (umbral-commutes-with-nf? term)
  (define delta-term (delta term))
  (define nf-term (normal-form term))
  (define delta-nf (normal-form delta-term))
  (define nf-delta-term (delta (make-term (format "NF(~a)" (term-name term))
                                         #:header (term-header term)
                                         #:core (nf-core nf-term))))
  (define nf-delta-nf (normal-form nf-delta-term))
  (and (= (nf-phase delta-nf) (nf-phase nf-delta-nf))
       (= (nf-scale delta-nf) (nf-scale nf-delta-nf))))

