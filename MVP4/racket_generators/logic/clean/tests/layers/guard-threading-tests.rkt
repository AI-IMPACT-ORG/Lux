#lang racket

;; CLEAN v10 Guard Threading Verification
;; Tests that guards properly thread through all operations

(require rackunit
         racket/format
         "../../class/guarded.rkt")

(provide test-guard-threading)

;; Test guard threading
(define (test-guard-threading)
  "Test that guards properly thread through all operations"
  (test-suite "Guard Threading"
    
    ;; Test basic guard threading
    (test-case "Basic Guard Threading"
      (set-guard! 2)
      (check-true (= (current-guard) 2) "Guard is set correctly")
      
      ;; Test guarded negation
      (check-true (not (undefined? (gn-not 0))) "gn-not(0) is defined")
      (check-true (not (undefined? (gn-not 1))) "gn-not(1) is defined")
      (check-true (not (undefined? (gn-not 2))) "gn-not(2) is defined")
      (check-true (undefined? (gn-not 3)) "gn-not(3) is undefined")
      
      ;; Test NAND operations
      (check-true (not (undefined? (gn-nand 0 0))) "gn-nand(0,0) is defined")
      (check-true (not (undefined? (gn-nand 1 1))) "gn-nand(1,1) is defined")
      (check-true (undefined? (gn-nand 2 2)) "gn-nand(2,2) is undefined (product > guard)"))
    
    ;; Test Boolean operations with guard threading
    (test-case "Boolean Operations with Guard Threading"
      (set-guard! 1)
      
      ;; Test AND operation
      (check-true (not (undefined? (boolean-and 0 0))) "AND(0,0) is defined")
      (check-true (not (undefined? (boolean-and 0 1))) "AND(0,1) is defined")
      (check-true (not (undefined? (boolean-and 1 0))) "AND(1,0) is defined")
      (check-true (not (undefined? (boolean-and 1 1))) "AND(1,1) is defined")
      
      ;; Test OR operation
      (check-true (not (undefined? (boolean-or 0 0))) "OR(0,0) is defined")
      (check-true (not (undefined? (boolean-or 0 1))) "OR(0,1) is defined")
      (check-true (not (undefined? (boolean-or 1 0))) "OR(1,0) is defined")
      (check-true (not (undefined? (boolean-or 1 1))) "OR(1,1) is defined")
      
      ;; Test XOR operation
      (check-true (not (undefined? (boolean-xor 0 0))) "XOR(0,0) is defined")
      (check-true (not (undefined? (boolean-xor 0 1))) "XOR(0,1) is defined")
      (check-true (not (undefined? (boolean-xor 1 0))) "XOR(1,0) is defined")
      (check-true (not (undefined? (boolean-xor 1 1))) "XOR(1,1) is defined")
      
      ;; Test NOT operation
      (check-true (not (undefined? (boolean-not 0))) "NOT(0) is defined")
      (check-true (not (undefined? (boolean-not 1))) "NOT(1) is defined"))
    
    ;; Test guard selection and universality
    (test-case "Guard Selection and Universality"
      (define test-values '(0 1 2 3 4 5))
      (define chosen-guard (choose-guard test-values))
      
      (check-true (= chosen-guard 5) "Guard chosen to cover all values")
      
      (set-guard! chosen-guard)
      
      ;; Test that all values are in domain
      (for ([value test-values])
        (check-true (in-domain? chosen-guard value) 
                    (format "Value ~a is in domain ↓~a" value chosen-guard))
        (check-true (not (undefined? (gn-not value))) 
                    (format "gn-not(~a) is defined with guard ~a" value chosen-guard)))
      
      ;; Test NAND operations work for all values
      (for ([x test-values])
        (for ([y test-values])
          (define product (* x y))
          (if (<= product chosen-guard)
              (check-true (not (undefined? (gn-nand x y))) 
                          (format "gn-nand(~a,~a) is defined" x y))
              (check-true (undefined? (gn-nand x y)) 
                          (format "gn-nand(~a,~a) is undefined (product ~a > guard ~a)" 
                                  x y product chosen-guard)))))
    
    ;; Test computational universality
    (test-case "Computational Universality"
      ;; Test that we can implement any Boolean function with appropriate guard
      (define boolean-values '(0 1))
      (define boolean-guard (choose-guard boolean-values))
      
      (set-guard! boolean-guard)
      
      ;; Test truth tables
      (for ([x boolean-values])
        (for ([y boolean-values])
          (check-true (not (undefined? (gn-nand x y))) 
                      (format "NAND(~a,~a) is defined" x y))
          (check-true (not (undefined? (boolean-and x y))) 
                      (format "AND(~a,~a) is defined" x y))
          (check-true (not (undefined? (boolean-or x y))) 
                      (format "OR(~a,~a) is defined" x y))
          (check-true (not (undefined? (boolean-xor x y))) 
                      (format "XOR(~a,~a) is defined" x y)))))))

;; Main execution
(module+ main
  (test-guard-threading))
