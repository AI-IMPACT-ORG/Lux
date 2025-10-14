#lang Lux
; (c) 2025 AI.IMPACT GmbH

(require (file "../../src/main.rkt"))

(provide prove-godel-1 prove-godel-2 prove-godel-1-internal prove-godel-2-internal)

(define (prove-godel-1)
  (godel1-witness))

(define (prove-godel-2)
  (godel2-witness))

(define (prove-godel-1-internal)
  (godel1-proof))

(define (prove-godel-2-internal)
  (godel2-proof))
