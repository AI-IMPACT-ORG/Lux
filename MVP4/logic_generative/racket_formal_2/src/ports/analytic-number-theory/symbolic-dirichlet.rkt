#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Symbolic Dirichlet series and Euler products (finite truncations)

(require racket/hash
         racket/function
         (file "../../foundations/abstract-core.rkt")
         (file "./common.rkt"))

(provide (all-defined-out))

;; A Dirichlet series is represented by coefficients a(n) for 1 <= n <= N
(struct ds (coeff bound) #:transparent)

(define (make-ds bound)
  (ds (make-hash) bound))

(define (ds-set! S n a)
  (hash-set! (ds-coeff S) n a))

(define (ds-ref S n)
  (hash-ref (ds-coeff S) n (make-abstract-const 0 'integer)))

;; use struct accessor ds-bound directly

(define (ds-copy S)
  (define T (make-ds (ds-bound S)))
  (for ([(k v) (in-hash (ds-coeff S))]) (ds-set! T k v))
  T)

(define (ds-delta bound)
  (define S (make-ds bound))
  (ds-set! S 1 (make-abstract-const 1 'integer))
  S)

(define (ds-const1 bound)
  (define S (make-ds bound))
  (for ([n (in-range 1 (add1 bound))])
    (ds-set! S n (make-abstract-const 1 'integer)))
  S)

;; Pointwise addition
(define (ds-add A B)
  (define bound (min (ds-bound A) (ds-bound B)))
  (define S (make-ds bound))
  (for ([n (in-range 1 (add1 bound))])
    (ds-set! S n (abstract-add (ds-ref A n) (ds-ref B n))))
  S)

;; Dirichlet convolution: (A * B)(n) = sum_{ab=n} A(a) B(b)
(define (ds-conv A B)
  (define bound (min (ds-bound A) (ds-bound B)))
  (define S (make-ds bound))
  (for ([n (in-range 1 (add1 bound))])
    (define acc (for/fold ([acc (make-abstract-const 0 'integer)]) ([a (in-range 1 (add1 n))] #:when (zero? (modulo n a)))
                  (define b (quotient n a))
                  (abstract-add acc (abstract-mul (ds-ref A a) (ds-ref B b)))))
    (ds-set! S n acc))
  S)

(define (ds-equal? A B)
  (define bound (min (ds-bound A) (ds-bound B)))
  (for/and ([n (in-range 1 (add1 bound))])
    (abstract-expr-equal? (ds-ref A n) (ds-ref B n))))

;; Scalar multiplication of a DS by c
(define (ds-scale S c)
  (define bound (ds-bound S))
  (define T (make-ds bound))
  (for ([n (in-range 1 (add1 bound))])
    (ds-set! T n (abstract-mul c (ds-ref S n))))
  T)

;; Elementary series: monomial at n with coefficient c
(define (ds-monomial bound n c)
  (define S (make-ds bound))
  (when (<= n bound) (ds-set! S n c))
  S)

;; Euler factor for a prime p: sum_{k=0..K} (p^k)^{-s} ⇒ monomials at p^k with coeff 1
(define (ds-euler-factor bound p)
  (define S (make-ds bound))
  (define c1 (make-abstract-const 1 'integer))
  (define n 1)
  (let loop ([pk 1])
    (when (<= pk bound)
      (ds-set! S pk c1)
      (loop (* pk p))))
  S)

;; Build the truncated Euler product across primes up to bound
;; Fast RC-respecting Euler product construction:
;; In the truncated, symbolic setting used here, the Euler product with unit
;; coefficients equals the Dirichlet sum with unit coefficients on 1..N. Building
;; it directly avoids expensive repeated convolutions and prevents regulator-
;; ignoring blowups (cycles/long runtimes for large N).
(define (ds-euler-product bound)
  (ds-const1 bound))

;; Von Mangoldt series: coefficients Λ(n)
(define (von-mangoldt n)
  (define base
    (for/first ([p (in-list (primes-up-to n))]
                #:when (let loop ([m n])
                         (cond
                           [(= m 1) #t]
                           [(zero? (modulo m p)) (loop (quotient m p))]
                           [else #f])))
      p))
  (if base
      (abstract-op 'log (list (make-abstract-const base 'integer)) 'real)
      (make-abstract-const 0 'integer)))

(define (ds-lambda bound)
  (define S (make-ds bound))
  (for ([n (in-range 1 (add1 bound))])
    (ds-set! S n (von-mangoldt n)))
  S)

;; Euler series (log zeta): coefficients 1/k at n = p^k, else 0
(define (ds-log-zeta bound)
  (define S (make-ds bound))
  (for ([p (in-list (primes-up-to bound))])
    (let loop ([pk p] [k 1])
      (when (<= pk bound)
        (define ck (abstract-div (make-abstract-const 1 'integer)
                                 (make-abstract-const k 'integer)))
        (ds-set! S pk ck)
        (loop (* pk p) (add1 k)))))
  S)

;; Formal derivation D_s: D[∑ a_n n^{-s}] = -∑ a_n log(n) n^{-s}
(define (ds-deriv S)
  (define bound (ds-bound S))
  (define T (make-ds bound))
  (for ([n (in-range 1 (add1 bound))])
    (define an (ds-ref S n))
    (define lnn (abstract-op 'log (list (make-abstract-const n 'integer)) 'real))
    (ds-set! T n (abstract-mul (make-abstract-const -1 'integer) (abstract-mul an lnn))))
  T)

;; Specialized derivation for log ζ: D(log ζ) = - Σ_{p,k} log p · p^{-ks}
(define (ds-deriv-log-zeta bound)
  (define T (make-ds bound))
  (for ([p (in-list (primes-up-to bound))])
    (define lp (abstract-op 'log (list (make-abstract-const p 'integer)) 'real))
    (let loop ([pk p])
      (when (<= pk bound)
        (ds-set! T pk (abstract-mul (make-abstract-const -1 'integer) lp))
        (loop (* pk p)))))
  T)

;; Series built from primes: Λ-series via Euler product derivative semantics (prime powers)
(define (ds-lambda-by-primes bound)
  (define S (make-ds bound))
  (for ([p (in-list (primes-up-to bound))])
    (define lp (abstract-op 'log (list (make-abstract-const p 'integer)) 'real))
    (let loop ([x p])
      (when (<= x bound)
        (ds-set! S x lp)
        (loop (* x p)))))
  S)
