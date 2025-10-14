#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Internal Coding and Reflection

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt"))

(provide (all-defined-out))

(define (encode-term t)
  (abstract-op 'encode (list t) 'code))

(define (decode-code c)
  (abstract-op 'decode (list c) 'term))

(define (coded? x)
  (and (abstract-op? x) (eq? (abstract-op-operator x) 'encode)))

(define (as-code-element t)
  (semiring-element (encode-term t) Core))

(define (from-code-element e)
  (decode-code (semiring-element-value e)))

(define (test-coding-roundtrip t)
  (define c (encode-term t))
  (define back (decode-code c))
  (abstract-op? back))

