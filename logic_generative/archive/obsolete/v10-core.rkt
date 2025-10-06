#lang racket

;; @logic/gen V10 Core Extensions
;; Extends V2-aligned generators with V10 Core features: triality, PSDM, domain ports

(require racket/contract
         racket/match
         racket/function
         racket/hash
         rackunit
         "core.rkt"
         "v2-aligned.rkt")

(provide (all-defined-out))

;; ============================================================================
;; V10 TRIALITY FUNCTORS (Natural from Generator Structure)
;; ============================================================================

;; Triality functors: T_L, T_R, T_B : B → B
;; These are natural transformations in the generator category

(define (T_L gen-elem)
  "Left triality functor: T_L : B → B"
  (gen (λ (x) (apply-gen gen-elem (* x 2)))  ; Scale by 2
       (hash-set (gen-meta gen-elem) 'triality 'left)))

(define (T_R gen-elem)
  "Right triality functor: T_R : B → B"
  (gen (λ (x) (apply-gen gen-elem (* x 3)))  ; Scale by 3
       (hash-set (gen-meta gen-elem) 'triality 'right)))

(define (T_B gen-elem)
  "Bulk triality functor: T_B : B → B"
  (gen (λ (x) (apply-gen gen-elem (* x 5)))  ; Scale by 5
       (hash-set (gen-meta gen-elem) 'triality 'bulk)))

;; ============================================================================
;; V10 PSDM (Partial Stable Domain Map) GENERATORS
;; ============================================================================

;; PSDM represents partial maps with stability properties
(struct psdm (domain codomain map stability) #:transparent)

;; PSDM generator: creates partial stable maps
(define (make-psdm-generator domain codomain map-fn stability-fn)
  "Create PSDM generator with domain, codomain, map function, and stability function"
  (gen (λ (x) 
         (if (stability-fn x)
             (map-fn x)
             (error "PSDM: input not in stable domain")))
       (make-gen-meta 'psdm (list 'partial 'stable 'domain-map))))

;; PSDM composition: compose two PSDMs
(define (psdm-compose psdm1 psdm2)
  "Compose two PSDMs: psdm1 ∘ psdm2"
  (define composed-map (compose (psdm-map psdm1) (psdm-map psdm2)))
  (define composed-stability (λ (x) 
                               (and ((psdm-stability psdm2) x)
                                    ((psdm-stability psdm1) ((psdm-map psdm2) x)))))
  (psdm (psdm-domain psdm2) 
        (psdm-codomain psdm1) 
        composed-map 
        composed-stability))

;; PSDM application
(define (apply-psdm psdm-gen x)
  "Apply PSDM generator to input"
  (apply-gen psdm-gen x))

;; ============================================================================
;; V10 DOMAIN PORTS (Natural Generator Extensions)
;; ============================================================================

;; Domain port structure: kernel + carrier + totality predicate + q-vector
(struct domain-port (kernel carrier totality-predicate q-vector) #:transparent)

;; Turing domain port
(define (make-turing-port #:threshold [threshold 0.5])
  "Create Turing domain port with halting threshold"
  (define turing-kernel 
    (gen (λ (x) (if (> x threshold) 'halt 'continue))
         (make-gen-meta 'turing-kernel (list 'halting))))
  
  (define turing-carrier
    (gen (λ (x) (if (eq? x 'halt) 1 0))
         (make-gen-meta 'turing-carrier (list 'binary))))
  
  (define turing-totality
    (λ (x) (and (number? x) (>= x 0) (<= x 1))))
  
  (define turing-q-vector (hash 'threshold threshold 'max-steps 1000))
  
  (domain-port turing-kernel turing-carrier turing-totality turing-q-vector))

;; Lambda domain port
(define (make-lambda-port)
  "Create Lambda domain port for functional computation"
  (define lambda-kernel
    (gen (λ (x) (if (procedure? x) (x 1) x))
         (make-gen-meta 'lambda-kernel (list 'functional))))
  
  (define lambda-carrier
    (gen (λ (x) (if (number? x) x 0))
         (make-gen-meta 'lambda-carrier (list 'numeric))))
  
  (define lambda-totality
    (λ (x) (or (number? x) (procedure? x))))
  
  (define lambda-q-vector (hash 'arity 1 'type 'functional))
  
  (domain-port lambda-kernel lambda-carrier lambda-totality lambda-q-vector))

;; Path domain port
(define (make-path-port #:euclidean? [euclidean? #t])
  "Create Path domain port for geometric computation"
  (define path-kernel
    (gen (λ (x) (if euclidean? (sqrt x) x))
         (make-gen-meta 'path-kernel (list 'geometric))))
  
  (define path-carrier
    (gen (λ (x) (if (number? x) (* x x) 0))
         (make-gen-meta 'path-carrier (list 'squared))))
  
  (define path-totality
    (λ (x) (and (number? x) (>= x 0))))
  
  (define path-q-vector (hash 'euclidean euclidean? 'dimension 2))
  
  (domain-port path-kernel path-carrier path-totality path-q-vector))

;; Infoflow domain port
(define (make-infoflow-port)
  "Create Infoflow domain port for information flow analysis"
  (define infoflow-kernel
    (gen (λ (x) (if (list? x) (length x) 0))
         (make-gen-meta 'infoflow-kernel (list 'information))))
  
  (define infoflow-carrier
    (gen (λ (x) (if (number? x) (log (+ x 1)) 0))
         (make-gen-meta 'infoflow-carrier (list 'logarithmic))))
  
  (define infoflow-totality
    (λ (x) (or (number? x) (list? x))))
  
  (define infoflow-q-vector (hash 'flow-type 'information 'sensitivity 'high))
  
  (domain-port infoflow-kernel infoflow-carrier infoflow-totality infoflow-q-vector))

;; ============================================================================
;; V10 DOMAIN PORT OPERATIONS
;; ============================================================================

;; Apply domain port to input
(define (apply-domain-port port input)
  "Apply domain port to input with totality checking"
  (if ((domain-port-totality-predicate port) input)
      (apply-gen (domain-port-kernel port) input)
      (error "Domain port: input not in totality domain")))

;; Domain port composition
(define (compose-domain-ports port1 port2)
  "Compose two domain ports"
  (define composed-kernel (gen-compose (domain-port-kernel port1) (domain-port-kernel port2)))
  (define composed-carrier (gen-compose (domain-port-carrier port1) (domain-port-carrier port2)))
  (define composed-totality (λ (x) (and ((domain-port-totality-predicate port2) x)
                                         ((domain-port-totality-predicate port1) 
                                          (apply-gen (domain-port-kernel port2) x)))))
  (define composed-q-vector (hash-union (domain-port-q-vector port1) 
                                        (domain-port-q-vector port2)))
  (domain-port composed-kernel composed-carrier composed-totality composed-q-vector))

;; ============================================================================
;; V10 TRUTH THEOREMS (Extended from V2)
;; ============================================================================

;; Triality consistency theorem
(define (test-triality-consistency gen-elem)
  "Test triality consistency: T_L ∘ T_R = T_R ∘ T_L"
  (define left-right (T_L (T_R gen-elem)))
  (define right-left (T_R (T_L gen-elem)))
  (equal? (apply-gen left-right 1) (apply-gen right-left 1)))

;; PSDM stability theorem
(define (test-psdm-stability psdm-gen)
  "Test PSDM stability: stable inputs produce stable outputs"
  (define test-inputs '(0 1 2 3 4 5))
  (for/and ([x test-inputs])
    (with-handlers ([exn:fail? (λ (e) #f)])
      (define result (apply-gen psdm-gen x))
      (number? result))))

;; Domain port totality theorem
(define (test-domain-port-totality port)
  "Test domain port totality: all inputs in domain produce outputs"
  (define test-inputs '(0.1 0.3 0.5 0.7 0.9))  ; Use decimal inputs for Turing port
  (for/and ([x test-inputs])
    (with-handlers ([exn:fail? (λ (e) #f)])
      (define result (apply-domain-port port x))
      (not (void? result)))))

;; ============================================================================
;; V10 INTEGRATION TESTS
;; ============================================================================

(define (run-v10-core-tests)
  "Run comprehensive V10 Core integration tests"
  (displayln "=== V10 Core Integration Tests ===")
  
  ;; Test triality functors
  (displayln "Testing triality functors...")
  (define test-gen (make-central-scalar 'test 2))
  (check-true (test-triality-consistency test-gen) "Triality consistency")
  
  ;; Test PSDM generators
  (displayln "Testing PSDM generators...")
  (define stable-psdm (make-psdm-generator 
                       'numbers 'numbers 
                       (λ (x) (* x 2))
                       (λ (x) (and (number? x) (>= x 0)))))
  (check-true (test-psdm-stability stable-psdm) "PSDM stability")
  
  ;; Test domain ports
  (displayln "Testing domain ports...")
  (define turing-port (make-turing-port))
  (define lambda-port (make-lambda-port))
  (define path-port (make-path-port))
  (define infoflow-port (make-infoflow-port))
  
  (check-true (test-domain-port-totality turing-port) "Turing port totality")
  (check-true (test-domain-port-totality lambda-port) "Lambda port totality")
  (check-true (test-domain-port-totality path-port) "Path port totality")
  (check-true (test-domain-port-totality infoflow-port) "Infoflow port totality")
  
  ;; Test domain port composition
  (displayln "Testing domain port composition...")
  (define composed-port (compose-domain-ports turing-port lambda-port))
  (check-true (test-domain-port-totality composed-port) "Composed port totality")
  
  (displayln "=== V10 Core Integration Tests Complete ==="))

;; Initialize V10 Core
(displayln "V10 Core Extensions initialized")
