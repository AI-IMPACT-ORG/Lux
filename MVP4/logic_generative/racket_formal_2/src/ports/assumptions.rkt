#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Port model assumptions registry: declare concrete model features per port

(require (file "../foundations/abstract-core.rkt")
         (file "../logic/internalize.rkt"))

(provide (all-defined-out))

;; Registry: symbol → hash of assumption → value
(define port-model-registry (make-hash))

(define (register-port-model! port-symbol kv-pairs)
  (define h (make-hash))
  (for ([kv kv-pairs]) (hash-set! h (car kv) (cdr kv)))
  (hash-set! port-model-registry port-symbol h)
  #t)

(define (port-model port-symbol)
  (hash-ref port-model-registry port-symbol (make-hash)))

(define (port-assumption? port-symbol key)
  (define h (port-model port-symbol))
  (hash-ref h key #f))

;; Boolean/meta constructors for documentation and optional L-lifting
(define (b-model-assumption port key)
  (abstract-op 'ModelAssumption (list (make-abstract-const port 'symbol)
                                      (make-abstract-const key 'symbol)) 'meta))
(define (L-model-assumption port key)
  (embed-proposition (b-model-assumption port key)))
