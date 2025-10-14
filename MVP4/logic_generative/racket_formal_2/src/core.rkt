#lang racket
; (c) 2025 AI.IMPACT GmbH

;; Core constructs backed by Lux abstract framework

(require racket/contract
         racket/match
         racket/function
         racket/hash
         "abstract-framework.rkt")

(provide (all-defined-out))

(struct gen (apply meta) #:transparent)
(define (make-gen-meta tag laws . rest) (apply hash 'tag tag 'laws laws rest))

(define (gen-id) (gen identity (make-gen-meta 'identity '(associativity identity))))
(define (gen-compose g1 g2) (gen (compose (gen-apply g2) (gen-apply g1)) (hash-set (gen-meta g1) 'composed-with (gen-tag g2))))
(define (apply-gen g x) ((gen-apply g) x))
(define (gen-power g n)
  (cond [(abstract-eq? n (get-zero)) (gen-id)]
        [(abstract-eq? n (get-one)) g]
        [else (gen-compose g (gen-power g (abstract-sub n (get-one))))]))
(define (greens-sum-generator K N)
  (define zero-const (get-zero)) (define one-const (get-one))
  (cond [(abstract-eq? N zero-const) (gen-id)]
        [(abstract-eq? N one-const) K]
        [else (let loop ([result (gen-id)] [current K] [remaining N])
                (if (abstract-le? remaining zero-const)
                    result
                    (loop (gen-compose result current)
                          (gen-compose current K)
                          (abstract-sub remaining one-const))))]))

(define (test-associativity g1 g2 g3)
  (define left-assoc (gen-compose (gen-compose g1 g2) g3))
  (define right-assoc (gen-compose g1 (gen-compose g2 g3)))
  (define test-inputs (list (get-zero) (get-one) (get-two) (get-three) (get-four) (get-five)))
  (for/and ([x test-inputs]) (equal? (apply-gen left-assoc x) (apply-gen right-assoc x))))

(define (test-identity g)
  (define test-inputs (list (get-zero) (get-one) (get-two) (get-three) (get-four) (get-five)))
  (for/and ([x test-inputs])
    (and (equal? (apply-gen (gen-compose (gen-id) g) x) (apply-gen g x))
         (equal? (apply-gen (gen-compose g (gen-id)) x) (apply-gen g x)))))

(define (make-gen f tag . laws) (gen f (make-gen-meta tag (if (null? laws) '() (car laws)))))
(define (gen-tag g) (hash-ref (gen-meta g) 'tag))
(define (gen-laws g) (hash-ref (gen-meta g) 'laws))
(define (gen-equal? g1 g2) (and (equal? (gen-tag g1) (gen-tag g2)) (equal? (gen-laws g1) (gen-laws g2))))
(define (gen->string g) (format "#<gen:~a:~a>" (gen-tag g) (gen-laws g)))

(define (inc-gen) (make-gen (λ (x) (abstract-add x (get-one))) 'increment '(monotonic)))
(define (double-gen) (make-gen (λ (x) (abstract-mul x (get-two))) 'double '(linear)))
(define (inc-then-double-gen) (gen-compose (double-gen) (inc-gen)))
(define (inc-power-3-gen) (gen-power (inc-gen) (get-three)))
(define (inc-greens-5-gen) (greens-sum-generator (inc-gen) (get-five)))
