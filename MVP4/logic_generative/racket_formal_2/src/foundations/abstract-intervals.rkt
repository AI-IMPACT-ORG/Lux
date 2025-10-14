#lang racket
;; Abstract interval arithmetic for symbolic inequalities and approximations

(require (file "./abstract-core.rkt"))

(provide (all-defined-out))

;; Intervals are abstract; endpoints may be abstract expressions.
(struct abstract-interval (lo hi type) #:transparent)

(define (make-interval lo hi #:type [type 'real])
  (abstract-interval lo hi type))

(define (interval? x) (abstract-interval? x))

(define (interval-lo I) (abstract-interval-lo I))
(define (interval-hi I) (abstract-interval-hi I))
(define (interval-type I) (abstract-interval-type I))

;; Helpers to compute if constants; otherwise create abstract ops to remain symbolic
(define (const-real? x)
  (and (abstract-const? x)
       (or (eq? (abstract-const-type x) 'integer)
           (eq? (abstract-const-type x) 'real))))

(define (num-val x)
  (abstract-const-value x))

(define (interval-add A B)
  (define lo-a (interval-lo A)) (define hi-a (interval-hi A))
  (define lo-b (interval-lo B)) (define hi-b (interval-hi B))
  (cond
    [(and (const-real? lo-a) (const-real? hi-a)
          (const-real? lo-b) (const-real? hi-b))
     (make-interval (make-abstract-const (+ (num-val lo-a) (num-val lo-b)) 'real)
                    (make-abstract-const (+ (num-val hi-a) (num-val hi-b)) 'real)
                    'real)]
    [else
     (make-interval (abstract-add lo-a lo-b)
                    (abstract-add hi-a hi-b)
                    'abstract)]))

(define (interval-mul A B)
  (define lo-a (interval-lo A)) (define hi-a (interval-hi A))
  (define lo-b (interval-lo B)) (define hi-b (interval-hi B))
  (cond
    [(and (const-real? lo-a) (const-real? hi-a)
          (const-real? lo-b) (const-real? hi-b))
     (define candidates (list (* (num-val lo-a) (num-val lo-b))
                              (* (num-val lo-a) (num-val hi-b))
                              (* (num-val hi-a) (num-val lo-b))
                              (* (num-val hi-a) (num-val hi-b))))
     (make-interval (make-abstract-const (apply min candidates) 'real)
                    (make-abstract-const (apply max candidates) 'real)
                    'real)]
    [else
     (make-interval (abstract-op 'interval-mul-lo (list lo-a lo-b hi-a hi-b) 'abstract)
                    (abstract-op 'interval-mul-hi (list lo-a lo-b hi-a hi-b) 'abstract)
                    'abstract)]))

(define (interval-contains? I x)
  (define lo (interval-lo I)) (define hi (interval-hi I))
  (cond
    [(and (const-real? lo) (const-real? hi) (const-real? x))
     (and (<= (num-val lo) (num-val x)) (<= (num-val x) (num-val hi)))]
    [else #t]))

(define (approx-equal? x y eps)
  (cond
    [(and (const-real? x) (const-real? y) (const-real? eps))
     (<= (abs (- (num-val x) (num-val y))) (num-val eps))]
    [else #t]))

