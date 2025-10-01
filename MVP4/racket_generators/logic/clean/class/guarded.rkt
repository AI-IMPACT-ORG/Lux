#lang racket

(require "../core/signature.rkt"
         "../class/moduli.rkt")

(provide guarded-negation
         nand^
         ; spec-faithful façade
         set-guard!
         gn-not
         gn-nand
         current-guard
         ; partial map utilities
         undefined?
         in-domain?
         choose-guard
         ; Boolean operations with guard threading
         boolean-and
         boolean-or
         boolean-xor
         boolean-not
         ; Lambda-aware guard utilities
         lambda-to-guard
         guard-from-lambda
         set-guard-from-lambda!)

(define current-guard (make-parameter 1))

(define (set-guard! g)
  (current-guard g))

(define (guarded-negation guard x)
  (cond
    [(not guard) 0]
    [(<= x guard) (- guard x)]
    [else 'undefined]))  ; Partial map: undefined for x > guard

(define (nand^ guard x y)
  (let ([product (* x y)])
    (if (<= product guard)
        (guarded-negation guard product)
        'undefined)))  ; Undefined if product > guard

(define (gn-not x)
  (guarded-negation (current-guard) x))

(define (gn-nand x y)
  (nand^ (current-guard) x y))

;; Partial map utilities
(define (undefined? x)
  "Check if a value represents undefined in partial maps"
  (eq? x 'undefined))

(define (in-domain? guard x)
  "Check if x is in the domain ↓g of guarded negation"
  (and guard (<= x guard)))

(define (choose-guard values)
  "Choose an appropriate guard to cover all values"
  (if (empty? values)
      1
      (apply max values)))

;; Boolean operations with proper guard threading
(define (boolean-and x y)
  "AND operation using guarded negation with proper guard threading"
  (let ([guard (current-guard)])
    (gn-nand (gn-nand x guard) (gn-nand y guard))))

(define (boolean-or x y)
  "OR operation using guarded negation with proper guard threading"
  (let ([guard (current-guard)])
    (gn-nand (gn-nand x guard) (gn-nand y guard))))

(define (boolean-xor x y)
  "XOR operation using guarded negation with proper guard threading"
  (let ([guard (current-guard)])
    (gn-nand (gn-nand x (gn-nand x y)) 
             (gn-nand y (gn-nand x y)))))

(define (boolean-not x)
  "NOT operation using guarded negation with proper guard threading"
  (gn-not x))

;; Lambda-aware guard utilities
(define (lambda-to-guard lambda-scale)
  "Convert Lambda scale parameter to appropriate guard value"
  ;; Use framework's own operations instead of floor
  ;; Find the largest natural number n such that n² ≤ Λ
  ;; This is equivalent to floor(sqrt(Λ)) but uses framework operations
  (if (and (number? lambda-scale) (> lambda-scale 0))
      (let loop ([n 1])
        (if (<= (* n n) lambda-scale)
            (loop (+ n 1))
            (- n 1)))
      1))

(define (guard-from-lambda)
  "Get guard value from current Lambda scale"
  (define moduli (current-moduli))
  (define z (moduli-z moduli))
  (define barz (moduli-barz moduli))
  (define lambda-scale (* z barz))  ; Λ = z ⊗_B barz
  (lambda-to-guard lambda-scale))

(define (set-guard-from-lambda!)
  "Set guard based on current Lambda scale"
  (define guard (guard-from-lambda))
  (set-guard! guard)
  guard)
