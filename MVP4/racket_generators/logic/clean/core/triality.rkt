#lang racket

(require racket/format
         "signature.rkt"
         "observers.rkt")

(provide starB
         starL
         starR
         triality->bulk)

(define (next-name name suffix)
  (format "~a^~a" name suffix))

(define (conjugate-term term suffix)
  (make-term (next-name (term-name term) suffix)
             #:header (term-header term)
             #:core `(conj ,suffix ,(term-core term))
             #:metadata 'conjugated))

(define (starB term)
  (conjugate-term term 'B))

(define (starL term)
  (conjugate-term term 'L))

(define (starR term)
  (conjugate-term term 'R))

(define (triality->bulk left-term right-term)
  (make-term "triality"
             #:header (cons (+ (car (term-header left-term))
                               (car (term-header right-term)))
                             (+ (cdr (term-header left-term))
                               (cdr (term-header right-term))))
             #:core `(⊕B ,left-term ,right-term)))
