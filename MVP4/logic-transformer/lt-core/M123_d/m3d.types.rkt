#lang typed/racket
(provide PortSort EdgeKind Arity Arity-m Arity-n
         TypeGraph TypeGraph? TypeGraph-ports TypeGraph-kinds TypeGraph-arity TypeGraph-srcS TypeGraph-dstS
         make-type-graph
         arity-of src-sort-of dst-sort-of
         NodeId EdgeId
         ;; Central arity-six symbol (Σ6) - key design requirement
         Sigma6
         ;; Moduli space parameters - four fundamental moduli with duals
         ModuliSpace Moduli Moduli-mu1 Moduli-mu2 Moduli-mu3 Moduli-mu4
         Moduli-mu1* Moduli-mu2* Moduli-mu3* Moduli-mu4*
         Moduli-lambda Moduli-lambda*
         make-moduli-space
         ;; Anomaly functional - global scalar predicate
         AnomalyFunc anomaly-measure
         ;; Natural cast operators - type coercion as natural operations
         natural-cast natural-cast? natural-cast-inverse
         type-safe-cast cast-to-hash cast-to-boolean cast-to-string)

;; atomic sorts/kinds
(define-type PortSort Symbol)   ; e.g., 'port, 'pin, 'p-in, 'p-out
(define-type EdgeKind Symbol)   ; 'wire 'unit 'tensor 'cast 'sigma6 ...

;; Central arity-six symbol (Σ6) - arity (3,3) as specified in design
(define Sigma6 : EdgeKind 'sigma6)

;; arity and endpoint sorts for an edge kind
(struct Arity ([m : Natural] [n : Natural]) #:transparent)

;; finite type graph metadata
(struct TypeGraph
  ([ports : (HashTable PortSort True)]
   [kinds : (HashTable EdgeKind True)]
   [arity : (HashTable EdgeKind Arity)]
   [srcS  : (HashTable EdgeKind (Vectorof PortSort))] ; length m
   [dstS  : (HashTable EdgeKind (Vectorof PortSort))]) #:transparent)

(: make-type-graph
   (-> (Listof PortSort)
       (Listof EdgeKind)
       (Listof (Pairof EdgeKind Arity))
       (Listof (Pairof EdgeKind (Vectorof PortSort)))
       (Listof (Pairof EdgeKind (Vectorof PortSort)))
       TypeGraph))
(define (make-type-graph Ps Ks ar srcs dsts)
  ;; Pre-compute hash table sizes for better performance
  (define port-count (length Ps))
  (define kind-count (length Ks))
  (define arity-count (length ar))
  (define src-count (length srcs))
  (define dst-count (length dsts))
  
  (TypeGraph
   (for/hash : (HashTable PortSort True) ([p Ps]) (values p #t))
   (for/hash : (HashTable EdgeKind True) ([k Ks]) (values k #t))
   (for/hash : (HashTable EdgeKind Arity) ([kv ar]) (values (car kv) (cdr kv)))
   (for/hash : (HashTable EdgeKind (Vectorof PortSort)) ([kv srcs]) (values (car kv) (cdr kv)))
   (for/hash : (HashTable EdgeKind (Vectorof PortSort)) ([kv dsts]) (values (car kv) (cdr kv)))))

(: arity-of (-> TypeGraph EdgeKind Arity))
(define (arity-of T k) (hash-ref (TypeGraph-arity T) k))
(: src-sort-of (-> TypeGraph EdgeKind (Vectorof PortSort)))
(define (src-sort-of T k) (hash-ref (TypeGraph-srcS T) k))
(: dst-sort-of (-> TypeGraph EdgeKind (Vectorof PortSort)))
(define (dst-sort-of T k) (hash-ref (TypeGraph-dstS T) k))

;; Moduli space parameters - four fundamental moduli with duals
;; As specified in design: μ=(μ₁,μ₂,μ₃,μ₄;μ₁*,μ₂*,μ₃*,μ₄*) with auxiliary variables (λ,λ*)
(struct Moduli ([mu1 : Natural] [mu2 : Natural] [mu3 : Natural] [mu4 : Natural]
                [mu1* : Natural] [mu2* : Natural] [mu3* : Natural] [mu4* : Natural]
                [lambda : Natural] [lambda* : Natural]) #:transparent)

(struct ModuliSpace ([moduli : Moduli]) #:transparent)

(: make-moduli-space (-> Moduli ModuliSpace))
(define (make-moduli-space m) (ModuliSpace m))

;; Anomaly functional - global scalar predicate measuring "degrees of freedom"
;; Must vanish at M3 and be mild at lower strata
(define-type AnomalyFunc (-> TypeGraph Natural))

;; Cache for anomaly measures to avoid repeated hash-count operations
(define anomaly-cache : (HashTable TypeGraph Natural) (make-hash))

(: anomaly-measure (-> TypeGraph Natural))
(define (anomaly-measure T)
  ;; Check cache first for performance
  (cond
    [(hash-has-key? anomaly-cache T)
     (hash-ref anomaly-cache T)]
    [else
     ;; Simplified implementation: measure based on number of edge kinds
     ;; In full design, this would measure degrees of freedom not fixed by typed-arity constraints
     (define measure (hash-count (TypeGraph-kinds T)))
     (hash-set! anomaly-cache T measure)
     measure]))

;; shared id aliases
(define-type NodeId Natural)
(define-type EdgeId Natural)

;; ============================================================================
;; NATURAL CAST OPERATORS - TYPE COERCION AS NATURAL OPERATIONS
;; ============================================================================

;; Natural cast structure - represents type coercion as a natural operation
(struct NaturalCast ([source-type : Symbol]
                     [target-type : Symbol]
                     [coercion-fn : (-> Any Any)]
                     [inverse-fn : (-> Any Any)])
  #:transparent)

;; Create a natural cast between types
(: natural-cast (-> Symbol Symbol (-> Any Any) (-> Any Any) NaturalCast))
(define (natural-cast source target coercion inverse)
  (NaturalCast source target coercion inverse))

;; Check if a value can be naturally cast to a type
(: natural-cast? (-> Any Symbol Boolean))
(define (natural-cast? value target-type)
  (cond
    [(eq? target-type 'HashTable) (hash? value)]
    [(eq? target-type 'Boolean) (boolean? value)]
    [(eq? target-type 'String) (string? value)]
    [(eq? target-type 'Symbol) (symbol? value)]
    [(eq? target-type 'Natural) (natural? value)]
    [else #f]))

;; Get the inverse of a natural cast
(: natural-cast-inverse (-> NaturalCast NaturalCast))
(define (natural-cast-inverse cast)
  (NaturalCast (NaturalCast-target-type cast)
               (NaturalCast-source-type cast)
               (NaturalCast-inverse-fn cast)
               (NaturalCast-coercion-fn cast)))

;; Cast to hash table (natural operation)
(: cast-to-hash (-> Any (HashTable Symbol Any)))
(define (cast-to-hash value)
  (cond
    [(hash? value) (cast value (HashTable Symbol Any))]
    [else (hash 'value value)]))

;; Type-safe cast using natural operations
(: type-safe-cast (-> Symbol Any Any))
(define (type-safe-cast target-type value)
  (cond
    [(eq? target-type 'HashTable) (cast-to-hash value)]
    [(eq? target-type 'Boolean) (cast-to-boolean value)]
    [(eq? target-type 'String) (cast-to-string value)]
    [else value]))

;; Cast to boolean (natural operation)
(: cast-to-boolean (-> Any Boolean))
(define (cast-to-boolean value)
  (cond
    [(boolean? value) value]
    [(hash? value) (hash-has-key? value 'optimized)]
    [(string? value) (not (string=? value ""))]
    [(natural? value) (not (= value 0))]
    [else #f]))

;; Cast to string (natural operation)
(: cast-to-string (-> Any String))
(define (cast-to-string value)
  (cond
    [(string? value) value]
    [(symbol? value) (symbol->string value)]
    [(natural? value) (number->string value)]
    [else "unknown"]))

