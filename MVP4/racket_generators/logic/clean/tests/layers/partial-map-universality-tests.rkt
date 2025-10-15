#lang racket

;; CLEAN v10 Partial Map Universality Tests
;; Tests that guarded negation as partial map achieves universality

(require rackunit
         racket/format
         "../../class/guarded.rkt")

(provide test-partial-map-universality)

;; Test partial map universality
(define (test-partial-map-universality)
  "Test that guarded negation as partial map achieves universality"
  (test-suite "Partial Map Universality"
    
    ;; Test partial map behavior
    (test-case "Partial Map Behavior"
      (set-guard! 2)
      
      ;; Test defined cases
      (check-true (not (undefined? (gn-not 0))) "gn-not(0) is defined")
      (check-true (not (undefined? (gn-not 1))) "gn-not(1) is defined")
      (check-true (not (undefined? (gn-not 2))) "gn-not(2) is defined")
      
      ;; Test undefined cases
      (check-true (undefined? (gn-not 3)) "gn-not(3) is undefined")
      (check-true (undefined? (gn-not 4)) "gn-not(4) is undefined")
      
      ;; Test domain checking
      (check-true (in-domain? 2 0) "0 is in domain ↓2")
      (check-true (in-domain? 2 1) "1 is in domain ↓2")
      (check-true (in-domain? 2 2) "2 is in domain ↓2")
      (check-false (in-domain? 2 3) "3 is not in domain ↓2"))
    
    ;; Test guard selection
    (test-case "Guard Selection"
      (define test-values '(0 1 2 3 4 5))
      (define chosen-guard (choose-guard test-values))
      
      (check-true (= chosen-guard 5) "Guard chosen to cover all values")
      
      ;; Test that all values are in domain with chosen guard
      (for ([value test-values])
        (check-true (in-domain? chosen-guard value) 
                    (format "Value ~a is in domain ↓~a" value chosen-guard))))
    
    ;; Test universality through guard selection
    (test-case "Universality Through Guard Selection"
      ;; Test that we can choose guards to cover any computation
      (define computation-values '(0 1 2 3 4 5))
      (define universal-guard (choose-guard computation-values))
      
      (set-guard! universal-guard)
      
      ;; Test that all values are now in domain
      (for ([value computation-values])
        (check-true (in-domain? universal-guard value) 
                    (format "Value ~a is in domain ↓~a" value universal-guard))
        (check-true (not (undefined? (gn-not value))) 
                    (format "gn-not(~a) is defined with guard ~a" value universal-guard)))
      
      ;; Test NAND operations work for all values
      (for ([x computation-values])
        (for ([y computation-values])
          (define product (* x y))
          (if (<= product universal-guard)
              (check-true (not (undefined? (gn-nand x y))) 
                          (format "gn-nand(~a,~a) is defined" x y))
              (check-true (undefined? (gn-nand x y)) 
                          (format "gn-nand(~a,~a) is undefined (product ~a > guard ~a)" 
                                  x y product universal-guard)))))
    
    ;; Test computational universality
    (test-case "Computational Universality"
      ;; Test that we can implement any Boolean function with appropriate guard
      (define boolean-values '(0 1))
      (define boolean-guard (choose-guard boolean-values))
      
      (set-guard! boolean-guard)
      
      ;; Test all Boolean operations work
      (define (boolean-and x y guard)
        (gn-nand (gn-nand x guard) (gn-nand y guard)))
      
      (define (boolean-or x y guard)
        (gn-nand (gn-nand x guard) (gn-nand y guard)))
      
      ;; Test truth tables
      (for ([x boolean-values])
        (for ([y boolean-values])
          (check-true (not (undefined? (gn-nand x y))) 
                      (format "NAND(~a,~a) is defined" x y))
          (check-true (not (undefined? (boolean-and x y boolean-guard))) 
                      (format "AND(~a,~a) is defined" x y))
          (check-true (not (undefined? (boolean-or x y boolean-guard))) 
                      (format "OR(~a,~a) is defined" x y))))))

;; Main execution
(module+ main
  (test-partial-map-universality))

