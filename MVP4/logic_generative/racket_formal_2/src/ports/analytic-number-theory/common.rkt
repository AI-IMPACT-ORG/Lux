#lang racket
;; Common symbolic helpers for ANT (no numerics)

(provide (all-defined-out))

;; Regulator for RG control (finite N, K)
(struct ant-regulator (N K) #:transparent)

;; Exact integer primality (discrete, non-analytic)
(define (prime? n)
  (cond [(<= n 1) #f]
        [(= n 2) #t]
        [else (let loop ([d 2])
                (cond [(> (* d d) n) #t]
                      [(zero? (modulo n d)) #f]
                      [else (loop (add1 d))]))]))

(define (primes-up-to n)
  (for/list ([k (in-range 2 (add1 n))] #:when (prime? k)) k))

