#lang racket

(require racket/list
         "../core/signature.rkt"
         "../core/nf.rkt"
         "../core/kernel.rkt")

(provide clear-histories!
         push-history!
         histories
         history-weight
         sum-over-histories
         schwinger-dyson)

(define current-histories (make-parameter '()))

(define (clear-histories!)
  (current-histories '()))

(define (push-history! steps)
  (current-histories (cons steps (current-histories))))

(define (histories)
  (reverse (current-histories)))

;; Simplified history weight
(define (history-weight history)
  (for/fold ([result kernel-header-zero]) ([term history])
    (kernel-header-add result (term-header term))))

;; Simplified sum-over-histories
(define (sum-over-histories kernel N)
  (unless (and (integer? N) (>= N 0))
    (error 'sum-over-histories "N must be non-negative integer, got ~a" N))
  (define greens (greens-sum kernel N))
  (define header (kernel-header greens))
  (make-term 'Σ#:histories 
             #:header header 
             #:core `(greens-sum ,N)))

;; Simplified Schwinger-Dyson
(define (schwinger-dyson kernel i F)
  (define delta-kernel (kernel kernel-header-zero
                              (transition 'delta
                                         (λ (term) `(Δ_~a ,term))
                                         `(delta-~a))))
  (define composed (kernel-compose delta-kernel kernel))
  (list '⟨Δ_iF⟩=0 i (term-name (if (term? F) F (make-term 'F)))
        (kernel-header composed)))
