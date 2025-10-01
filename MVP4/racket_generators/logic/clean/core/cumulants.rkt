#lang racket

(require racket/list
         racket/match
         racket/format
         "signature.rkt"
         "nf.rkt"
         "observers.rkt"
         "kernel.rkt")

(provide register-observable
         clear-observables!
         observables
         generating-functional
         value-g
         value-G
         value-beta-mu
         value-beta-theta
         value-a
         value-c
         ; kernel integration
         kernel-generating-functional
         kernel-cumulants)

(define current-observables
  (make-parameter (hash)))

(define (register-observable index term)
  (unless (integer? index)
    (error 'register-observable "index must be integer, got ~a" index))
  (unless (term? term)
    (error 'register-observable "expected term, got ~a" term))
  (current-observables (hash-set (current-observables) index term))
  (void))

(define (clear-observables!)
  (current-observables (hash)))

(define (observables)
  (current-observables))

;; Unified header operations using kernel machinery
(define (header-sum terms)
  (for/fold ([result kernel-header-zero]) ([t terms])
    (kernel-header-add result (term-header t))))

(define (generating-functional sources)
  (define indexed
    (for/list ([src sources])
      (match src
        [(cons idx coeff)
         (define term (hash-ref (current-observables) idx #f))
         (cons (or term (make-term (format "source-~a" idx))) coeff)]
        [_ (cons (make-term "source") 1)])))
  (define terms (map car indexed))
  (define header (header-sum terms))
  (make-term "Z[J]"
             #:header header
             #:core `(Σ ,(map term-name terms))))

;; Optimized kernel-based generating functional
(define (kernel-generating-functional kernel sources)
  (define indexed
    (for/list ([src sources])
      (match src
        [(cons idx coeff)
         (define term (hash-ref (current-observables) idx #f))
         (cons (or term (make-term (format "source-~a" idx))) coeff)]
        [_ (cons (make-term "source") 1)])))
  (define terms (map car indexed))
  (define kernel-applied (map (λ (term) (kernel-apply kernel term)) terms))
  (define header (header-sum kernel-applied))
  (make-term "Z[J]_kernel"
             #:header header
             #:core `(Σ_kernel ,(map term-name kernel-applied))))

;; Optimized kernel-based cumulant computation
(define (kernel-cumulants kernel indices)
  (define terms (map (λ (i) (hash-ref (current-observables) i #f)) indices))
  (define kernel-applied (map (λ (term) (kernel-apply kernel term)) terms))
  (define headers (map term-header kernel-applied))
  (define total-header (header-sum kernel-applied))
  (list 'kernel-cumulants 
        'headers headers
        'total-header total-header
        'kernel-header (kernel-header kernel)))

(define (value-g index)
  (define term (hash-ref (current-observables) index #f))
  (and term (nf-core (normal-form term))))

(define (value-G i j)
  (define term-i (hash-ref (current-observables) i #f))
  (define term-j (hash-ref (current-observables) j #f))
  (and term-i term-j
       `(cov ,(term-name term-i) ,(term-name term-j))))

(define (value-beta-mu index)
  (define term (hash-ref (current-observables) index #f))
  (and term `(β_μ ,(term-name term))))

(define (value-beta-theta index)
  (define term (hash-ref (current-observables) index #f))
  (and term `(β_θ ,(term-name term))))

(define (value-a)
  '(monotone-a stable))

(define (value-c)
  '(monotone-c stable))
