#lang racket/base

(require rackunit
         racket/match
         "../truth-system.rkt"
         "../domain/unified-port.rkt"
         "../../../api.rkt")

(module+ test
  ;; Use unified test framework
  (with-truth-validation
    (define term (make-term 'bulk#:1 #:header '(1 . 1) #:core 'λ-term))
    
    (test-case "Truth System Integration"
      (define system (make-truth-system))
      (define results (truth-system-results system))
      (check-true (hash-ref results 'all-passed #f)))
    
    (test-case "Domain Port Validation"
      (define turing-port (port-boolean-logic #:validate? #t))
      (define lambda-port (port-lambda-calculus #:validate? #t))
      (define path-port (port-quantum-field-theory #:validate? #t))
      (define infoflow-port (port-information-theory #:validate? #t))
      
      (check-true (domain-port? turing-port))
      (check-true (domain-port? lambda-port))
      (check-true (domain-port? path-port))
      (check-true (domain-port? infoflow-port)))
    
    (test-case "Truth Theorems"
      (assert-truth-theorem 'umbral-renormalisation)
      (assert-truth-theorem 'church-turing)
      (assert-truth-theorem 'eor-health)
      (assert-truth-theorem 'logic-grh-gate))
    
    (test-case "Feynman Integration"
      (define result (sum-over-histories))
      (check-true (term? result))
      
      (define schwinger-result (schwinger-dyson 1 'test))
      (check-true (term? schwinger-result)))))
