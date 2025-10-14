#lang racket

;; Reader for #lang Lux. Wraps the source as a Racket module that
;; requires the Lux unified API and then runs the user program.

(require syntax/strip-context)

(provide read-syntax get-info)

(define (read-syntax path in)
  (define src (read-syntax path in))
  (datum->syntax
   #f
   `(module Lux-module racket
      (require (file "../../src/main.rkt"))
      ,(syntax->datum src))))

(define (get-info key default)
  (case key
    [(color-lexer) (λ () #f)]
    [else default]))

