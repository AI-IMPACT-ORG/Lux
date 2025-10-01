#lang racket

(require rackunit
         "../../core/header.rkt"
         "../../core/kernel.rkt"
         "../../core/signature.rkt"
         "../../core/nf.rkt"
         "../../core/observers.rkt"
         "../../core/cumulants.rkt"
         "../feynman.rkt"
         "../psdm.rkt"
         "unified-port.rkt")

(module+ test
  (test-case "Unified Domain Ports Test"
    (set-quotient-mask! '(phase))
    (set-r-matrix! 'identity)

    (define test-term (make-term 'test #:header '(1 . 0) #:core 'test-core))

    ;; Test Turing Port
    (define turing-port (make-turing-port #:threshold 0.5))
    (check-true (domain-port? turing-port))
    (check-equal? (domain-port-q-vector turing-port) '(1 0 0))
    
    (define turing-result (domain-port-eval turing-port test-term))
    (check-true (term? turing-result))

    ;; Test Lambda Port
    (define lambda-port (make-lambda-port))
    (check-true (domain-port? lambda-port))
    (check-equal? (domain-port-q-vector lambda-port) '(0 1 0))
    
    (define lambda-result (domain-port-eval lambda-port test-term))
    (check-true (term? lambda-result))

    ;; Test Path Port
    (define path-port (make-path-port #:euclidean? #t))
    (check-true (domain-port? path-port))
    (check-equal? (domain-port-q-vector path-port) '(0 0 1))
    
    (define path-result (domain-port-eval path-port test-term))
    (check-true (term? path-result))

    ;; Test Infoflow Port
    (define infoflow-port (make-infoflow-port))
    (check-true (domain-port? infoflow-port))
    (check-equal? (domain-port-q-vector infoflow-port) '(0 0 0))
    
    (define infoflow-result (domain-port-eval infoflow-port test-term))
    (check-true (term? infoflow-result))))
