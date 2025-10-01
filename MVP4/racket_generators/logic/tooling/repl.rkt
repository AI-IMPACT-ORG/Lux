#lang racket

(require "../api.rkt")

(provide demo)

(define (demo)
  (set-quotient-mask! '(phase))
  (set-moduli! #:μL 1 #:θR 2)
  (define term (make-term 'demo#:bulk #:header '(1 . 0)))
  (register-observable 0 term)
  (values 'ready (normal-form term)))
