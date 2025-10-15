#lang Lux
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

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
