#lang racket

;; CLEAN v10 Lambda-Guard Threading Tests
;; Tests the intimate relationship between Lambda parameters and guarded negation

(require rackunit
         racket/format
         "../../class/guarded.rkt"
         "../../class/moduli.rkt")

(provide test-lambda-guard-threading)

;; Test Lambda-guard threading
(define (test-lambda-guard-threading)
  "Test the intimate relationship between Lambda parameters and guarded negation"
  (test-suite "Lambda-Guard Threading"
    
    ;; Test Lambda-to-guard conversion
    (test-case "Lambda-to-Guard Conversion"
      (check-true (= (lambda-to-guard 1) 1) "Λ=1 → g=1")
      (check-true (= (lambda-to-guard 4) 2) "Λ=4 → g=2")
      (check-true (= (lambda-to-guard 9) 3) "Λ=9 → g=3")
      (check-true (= (lambda-to-guard 16) 4) "Λ=16 → g=4")
      (check-true (= (lambda-to-guard 25) 5) "Λ=25 → g=5"))
    
    ;; Test guard-from-lambda
    (test-case "Guard-from-Lambda"
      (set-moduli! #:z 2 #:barz 2)  ; Λ = 4
      (check-true (= (guard-from-lambda) 2) "Guard from Λ=4 is 2")
      
      (set-moduli! #:z 3 #:barz 3)  ; Λ = 9
      (check-true (= (guard-from-lambda) 3) "Guard from Λ=9 is 3"))
    
    ;; Test automatic guard setting
    (test-case "Automatic Guard Setting"
      (set-moduli! #:z 4 #:barz 4)  ; Λ = 16
      (define auto-guard (set-guard-from-lambda!))
      (check-true (= auto-guard 4) "Auto-set guard is 4")
      (check-true (= (current-guard) 4) "Current guard is 4"))
    
    ;; Test guarded operations with Lambda-derived guard
    (test-case "Guarded Operations with Lambda-Derived Guard"
      (set-moduli! #:z 2 #:barz 2)  ; Λ = 4, g = 2
      (set-guard-from-lambda!)
      
      ;; Test defined cases
      (check-true (not (undefined? (gn-not 0))) "gn-not(0) is defined")
      (check-true (not (undefined? (gn-not 1))) "gn-not(1) is defined")
      (check-true (not (undefined? (gn-not 2))) "gn-not(2) is defined")
      
      ;; Test undefined cases
      (check-true (undefined? (gn-not 3)) "gn-not(3) is undefined")
      (check-true (undefined? (gn-not 4)) "gn-not(4) is undefined"))
    
    ;; Test counting function relationship
    (test-case "Counting Function Relationship"
      (define test-cases '((1 0) (0 1) (1 1) (2 0) (0 2) (2 1) (1 2) (2 2)))
      (for ([case test-cases])
        (define n (first case))
        (define m (second case))
        (define total-steps (+ n m))
        ;; Set Lambda to ensure guard covers the computation
        (define lambda-scale (* total-steps total-steps))  ; Λ = (n+m)²
        (define z (sqrt lambda-scale))
        (define barz (sqrt lambda-scale))
        (set-moduli! #:z z #:barz barz)
        (define guard (set-guard-from-lambda!))
        
        (check-true (>= guard total-steps) 
                    (format "For n=~a, m=~a, n+m=~a, Λ=~a, g=~a: g≥n+m" 
                            n m total-steps lambda-scale guard)))
    
    ;; Test universality through Lambda-guard threading
    (test-case "Universality Through Lambda-Guard Threading"
      (define computation-values '(0 1 2 3 4 5))
      (define max-steps (apply max computation-values))
      (define lambda-scale (* max-steps max-steps))  ; Λ = max²
      (define z (sqrt lambda-scale))
      (define barz (sqrt lambda-scale))
      (set-moduli! #:z z #:barz barz)
      (define guard (set-guard-from-lambda!))
      
      ;; Test that all values are in domain
      (for ([value computation-values])
        (check-true (in-domain? guard value) 
                    (format "Value ~a is in domain ↓~a" value guard))
        (check-true (not (undefined? (gn-not value))) 
                    (format "gn-not(~a) is defined with guard ~a" value guard)))
    
    ;; Test Boolean operations with Lambda-derived guard
    (test-case "Boolean Operations with Lambda-Derived Guard"
      (set-moduli! #:z 1 #:barz 1)  ; Λ = 1, g = 1
      (set-guard-from-lambda!)
      
      ;; Test Boolean operations work
      (check-true (not (undefined? (boolean-and 0 0))) "AND(0,0) is defined")
      (check-true (not (undefined? (boolean-and 0 1))) "AND(0,1) is defined")
      (check-true (not (undefined? (boolean-and 1 0))) "AND(1,0) is defined")
      (check-true (not (undefined? (boolean-and 1 1))) "AND(1,1) is defined")
      
      (check-true (not (undefined? (boolean-or 0 0))) "OR(0,0) is defined")
      (check-true (not (undefined? (boolean-or 0 1))) "OR(0,1) is defined")
      (check-true (not (undefined? (boolean-or 1 0))) "OR(1,0) is defined")
      (check-true (not (undefined? (boolean-or 1 1))) "OR(1,1) is defined"))))

;; Main execution
(module+ main
  (test-lambda-guard-threading))
