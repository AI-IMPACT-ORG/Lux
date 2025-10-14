#lang racket

;; #lang lux — language reader
;; Injects the unified CLEAN API from racket_formal_2/src/main.rkt

(require syntax/strip-context)

(provide read-syntax get-info)

(define (read-syntax path in)
  (define src (read-syntax path in))
  (datum->syntax
   #f
   `(module lux-program racket
      (require (file "../../racket_formal_2/src/main.rkt"))
      ,(syntax->datum src))))

(define (get-info key default)
  (case key
    [(color-lexer) (λ () #f)]
    [else default]))

