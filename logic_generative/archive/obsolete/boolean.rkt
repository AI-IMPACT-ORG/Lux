#lang racket

;; @logic/gen Domain Port Generators
;; Implements domain-specific port generators for Boolean, Lambda, InfoFlow, and QFT

(require racket/contract
         "../core.rkt")

(provide (all-defined-out))

;; ============================================================================
;; DOMAIN PORT GENERATOR INTERFACE
;; ============================================================================

;; Domain port generator struct
(struct domain-port-gen (kernel carrier totality-predicate q-vector)
  #:transparent)

;; Domain port evaluation
(define (domain-port-eval port term)
  "Evaluate term using domain port generator"
  (unless (domain-port-gen? port)
    (error 'domain-port-eval "expected domain port generator, got ~a" port))
  (if ((domain-port-gen-totality-predicate port) term)
      (gen-apply (domain-port-gen-kernel port) term)
      'undefined))

;; Domain port totality check
(define (psdm-defined? port term)
  "Check if term is defined for domain port"
  (unless (domain-port-gen? port)
    (error 'psdm-defined? "expected domain port generator, got ~a" port))
  ((domain-port-gen-totality-predicate port) term))

;; ============================================================================
;; BOOLEAN PORT GENERATOR (q=(1,0,0))
;; ============================================================================

;; Boolean port generator for deterministic models
(define (make-boolean-port #:threshold [threshold 0.5])
  "Create Boolean domain port generator"
  (define boolean-kernel 
    (make-gen (λ (term) term) 'boolean '(deterministic)))
  (define boolean-carrier 'boolean)
  (define boolean-predicate 
    (λ (term) (deterministic-computation-defined? term)))
  (define boolean-q-vector '(1 0 0))
  
  (domain-port-gen boolean-kernel boolean-carrier boolean-predicate boolean-q-vector))

;; Helper: Check if deterministic computation is defined
(define (deterministic-computation-defined? term)
  "Check if term is suitable for deterministic computation"
  ;; Mathematical criterion: term should be well-formed and computable
  (and (not (eq? term 'non-halting))
       (not (eq? term 'infinite-loop))
       (not (eq? term 'divergent))
       (or (symbol? term)
           (number? term)
           (string? term)
           (and (list? term) (not (empty? term))))))

;; ============================================================================
;; LAMBDA PORT GENERATOR (q=(0,1,0))
;; ============================================================================

;; Lambda calculus port generator for probabilistic models
(define (make-lambda-port)
  "Create Lambda domain port generator"
  (define lambda-kernel
    (make-gen (λ (term) term) 'lambda '(probabilistic)))
  (define lambda-carrier 'lambda)
  (define lambda-predicate
    (λ (term) (halts-within-regulator? term)))
  (define lambda-q-vector '(0 1 0))
  
  (domain-port-gen lambda-kernel lambda-carrier lambda-predicate lambda-q-vector))

;; Helper: Check if term halts within regulator
(define (halts-within-regulator? term)
  "Check if term halts within regulator bounds"
  (and (not (eq? term 'non-halting))
       (not (eq? term 'infinite-loop))
       (not (eq? term 'non-converging))))

;; ============================================================================
;; INFOFLOW PORT GENERATOR (q=(0,0,0))
;; ============================================================================

;; Information flow port generator for information measures
(define (make-infoflow-port)
  "Create InfoFlow domain port generator"
  (define infoflow-kernel
    (make-gen (λ (term) term) 'infoflow '(information)))
  (define infoflow-carrier 'infoflow)
  (define infoflow-predicate
    (λ (term) (flows-within-regulator? term)))
  (define infoflow-q-vector '(0 0 0))
  
  (domain-port-gen infoflow-kernel infoflow-carrier infoflow-predicate infoflow-q-vector))

;; Helper: Check if information flows within regulator
(define (flows-within-regulator? term)
  "Check if information flows within regulator bounds"
  (and (not (eq? term 'non-flowing))
       (not (eq? term 'blocked))
       (not (eq? term 'divergent))))

;; ============================================================================
;; QFT PORT GENERATOR (q=(0,0,1))
;; ============================================================================

;; QFT port generator for stochastic models (alias for path port)
(define (make-qft-port #:euclidean? [euclidean? #t])
  "Create QFT domain port generator"
  (define carrier (if euclidean? 'euclidean 'minkowski))
  (define qft-kernel
    (make-gen (λ (term) term) 'qft '(stochastic)))
  (define qft-carrier carrier)
  (define qft-predicate
    (λ (term) (converges-within-regulator? term)))
  (define qft-q-vector '(0 0 1))
  
  (domain-port-gen qft-kernel qft-carrier qft-predicate qft-q-vector))

;; Helper: Check if term converges within regulator
(define (converges-within-regulator? term)
  "Check if term converges within regulator bounds"
  (and (not (eq? term 'non-converging))
       (not (eq? term 'divergent))
       (not (eq? term 'infinite-loop))))

;; ============================================================================
;; DOMAIN PORT COMPOSITION
;; ============================================================================

;; Compose domain ports
(define (compose-domain-ports port1 port2)
  "Compose two domain port generators"
  (unless (and (domain-port-gen? port1) (domain-port-gen? port2))
    (error 'compose-domain-ports "expected domain port generators"))
  
  (define composed-kernel 
    (gen-compose (domain-port-gen-kernel port1) (domain-port-gen-kernel port2)))
  (define composed-carrier 
    (string->symbol (format "~a-~a" (domain-port-gen-carrier port1) (domain-port-gen-carrier port2))))
  (define composed-predicate
    (λ (term) (and ((domain-port-gen-totality-predicate port1) term)
                   ((domain-port-gen-totality-predicate port2) term))))
  (define composed-q-vector
    (map + (domain-port-gen-q-vector port1) (domain-port-gen-q-vector port2)))
  
  (domain-port-gen composed-kernel composed-carrier composed-predicate composed-q-vector))

;; ============================================================================
;; DOMAIN PORT VALIDATION
;; ============================================================================

;; Validate domain port coherence
(define (validate-domain-port-coherence port)
  "Validate domain port generator coherence"
  (and (domain-port-gen? port)
       (gen? (domain-port-gen-kernel port))
       (symbol? (domain-port-gen-carrier port))
       (procedure? (domain-port-gen-totality-predicate port))
       (list? (domain-port-gen-q-vector port))
       (= (length (domain-port-gen-q-vector port)) 3)))

;; Test domain port functionality
(define (test-domain-port port test-terms)
  "Test domain port generator with test terms"
  (unless (validate-domain-port-coherence port)
    (error 'test-domain-port "invalid domain port generator"))
  
  (for ([term test-terms])
    (define defined? (psdm-defined? port term))
    (when defined?
      (define result (domain-port-eval port term))
      (unless (equal? result 'undefined)
        (printf "Port ~a: ~a -> ~a~n" 
                (domain-port-gen-carrier port) term result)))))

;; ============================================================================
;; DOMAIN PORT EXAMPLES
;; ============================================================================

;; Example: Create and test Boolean port
(define (example-boolean-port)
  "Example usage of Boolean domain port"
  (define B (make-boolean-port))
  (define test-terms '(1 0 'true 'false '(a b c)))
  (test-domain-port B test-terms))

;; Example: Create and test Lambda port
(define (example-lambda-port)
  "Example usage of Lambda domain port"
  (define L (make-lambda-port))
  (define test-terms '(λx.x 'lambda '(a b) 'halt))
  (test-domain-port L test-terms))

;; Example: Compose domain ports
(define (example-port-composition)
  "Example usage of domain port composition"
  (define B (make-boolean-port))
  (define L (make-lambda-port))
  (define BL (compose-domain-ports B L))
  (printf "Composed port: ~a~n" (domain-port-gen-carrier BL))
  (printf "Q-vector: ~a~n" (domain-port-gen-q-vector BL)))
