#lang racket

(require "header.rkt")

(provide signature?
         signature-sorts
         signature-operations
         signature-constants
         current-signature
         set-current-signature!
         default-signature
         term?
         term-name
         term-header
         term-core
         term-left
         term-right
         term-metadata
         make-term
         random-term
         set-quotient-mask!
         current-quotient-mask
         set-r-matrix!
         current-r-matrix)

(struct signature (sorts operations constants)
  #:transparent)

(define default-signature
  (signature
   '(L B R I)
   '((⊕B . (B B -> B))
     (⊗B . (B B -> B))
     (⊕_L . (L L -> L))
     (⊕_R . (R R -> R))
     (ι_L . (L -> B))
     (ι_R . (R -> B))
     (ν_L . (B -> L))
     (ν_R . (B -> R))
     (ad_0 . (B -> B))
     (ad_1 . (B -> B))
     (ad_2 . (B -> B))
     (ad_3 . (B -> B))
     (starB . (B -> B))
     (starL . (L -> L))
     (starR . (R -> R)))
   '((0_B . B)
     (1_B . B)
     (0_L . L)
     (1_L . L)
     (0_R . R)
     (1_R . R)
     (φ . B)
     (barφ . B)
     (z . B)
     (barz . B)
     (Λ . B)
     (Gen4 . (B B B B -> B)))))

(define current-signature
  (make-parameter default-signature))

(define (set-current-signature! sig)
  (unless (signature? sig)
    (error 'set-current-signature! "expected signature, got ~a" sig))
  (current-signature sig))

(struct term (name header core left right metadata)
  #:transparent)

(define (make-term name
                   #:header [header header-zero]
                   #:core [core '•]
                   #:left [left #f]
                   #:right [right #f]
                   #:metadata [metadata #f])
  (term name header core left right metadata))

;; Random term generation for property-based testing
(define (random-term [header-range 5.0])
  "Generate a random term for property-based testing"
  (define h (random-header header-range header-range))
  (define name (string->symbol (format "random-term-~a" (random 1000))))
  (make-term name #:header h #:core (format "core-~a" (random 1000))))

(define current-quotient-mask (make-parameter '(phase)))
(define (set-quotient-mask! mask)
  (unless (and (list? mask)
               (andmap (λ (m) (member m '(phase scale triality))) mask))
    (error 'set-quotient-mask! "expected list of mask atoms, got ~a" mask))
  (current-quotient-mask mask))

(define current-r-matrix (make-parameter 'identity))
(define (set-r-matrix! rdata)
  (current-r-matrix rdata))
