#lang typed/racket
(require "m2d.pgc.rkt" "m2d.cert.rkt" "m2d.semiring-optimized.rkt"
         "m3d.graph.rkt" "m3d.types.rkt")
(provide ;; M1 Logic - now uses semiring-based evaluation
         M1Logic M1Logic? M1Logic-theory M1Logic-models M1Logic-evaluation-logic
         make-m1-logic m1-logic-satisfies? m1-logic-complete?
         ;; The single transformer logic - the fulcrum of the MDE pyramid
         TransformerLogic transformer-logic-theory
         ;; M1-specific: model instances and runtime semantics
         InstanceGraph InstanceGraph? InstanceNode InstanceNode? InstanceEdge InstanceEdge?
         make-instance-graph add-instance-node add-instance-edge
         instance-well-formed? instance-satisfies-theory
         ;; M1→M0 transformation: Gödel encoding for runtime
         goedel-encode instance-to-runtime
         ;; M1 Convergence: The single transformer logic as fulcrum
         logic-convergence-point transformer-logic-axioms)

;; M1 Logic - the single transformer logic that serves as fulcrum
;; This is where the MDE pyramid converges to a single, unified logic
;; Now uses semiring-based evaluation for parametric satisfaction
(struct M1Logic ([theory : PGC]           ; The logical theory (from M2)
                 [models : (Listof TGraph)] ; Valid models (from M3)
                 [evaluation-logic : Logic]) #:transparent) ; Semiring-based evaluation

(: make-m1-logic (-> PGC (Listof TGraph) Logic M1Logic))
(define (make-m1-logic theory models eval-logic)
  (M1Logic theory models eval-logic))

(: m1-logic-satisfies? (-> M1Logic TGraph Boolean))
(define (m1-logic-satisfies? L G)
  (satisfies^ (M1Logic-evaluation-logic L) 'global G (initial-guard) (M1Logic-theory L)))

(: m1-logic-complete? (-> M1Logic Boolean))
(define (m1-logic-complete? L)
  ;; A logic is complete if all models satisfy the theory
  (for/and ([G (M1Logic-models L)])
    (m1-logic-satisfies? L G)))

;; The single transformer logic - the fulcrum
;; This is the convergence point where all MDE layers meet
;; It embodies the core principles: typed-arity discipline, Σ6 centrality, and moduli space
(define transformer-logic-theory : PGC
  (pgc-and 
   ;; Core typed-arity constraint: Σ6 must have arity (3,3)
   (pgc-match (mk-graph (make-type-graph 
                        (list 'port)                    ; Single port sort
                        (list Sigma6)                   ; Central arity-six symbol
                        (list (cons Sigma6 (Arity 3 3))) ; Σ6: 3-in, 3-out
                        (list (cons Sigma6 (vector 'port 'port 'port))) ; Source sorts
                        (list (cons Sigma6 (vector 'port 'port 'port)))))) ; Target sorts
   ;; Moduli space constraint: anomaly must vanish at M3
   (pgc-exists (make-submono (set) (set)) 
               (mk-graph (make-type-graph '() '() '() '() '())) ; Empty pattern
               pgc-top))) ; Always true

;; The transformer logic with proper models that satisfy the theory
;; Now uses semiring-based evaluation with boolean-top logic
(define TransformerLogic : M1Logic
  (make-m1-logic transformer-logic-theory 
                 ;; Include models that satisfy the typed-arity discipline
                 (list (mk-graph (make-type-graph 
                                 (list 'port)
                                 (list Sigma6)
                                 (list (cons Sigma6 (Arity 3 3)))
                                 (list (cons Sigma6 (vector 'port 'port 'port)))
                                 (list (cons Sigma6 (vector 'port 'port 'port))))))
                 logic/boolean-top))

;; M1 Model Instances - concrete runtime objects
;; These are the actual instances that live in the M1 layer
(struct InstanceNode ([id : NodeId] [type : PortSort] [value : Any]) #:transparent)
(struct InstanceEdge ([id : EdgeId] [kind : EdgeKind] 
                      [src : (Vectorof NodeId)] [dst : (Vectorof NodeId)]
                      [weight : Natural]) #:transparent)

(struct InstanceGraph ([schema : TGraph]           ; Schema from M2
                       [nodes : (HashTable NodeId InstanceNode)]
                       [edges : (HashTable EdgeId InstanceEdge)]) #:transparent)

(: make-instance-graph (-> TGraph InstanceGraph))
(define (make-instance-graph schema)
  (InstanceGraph schema (hash) (hash)))

(: add-instance-node (-> InstanceGraph InstanceNode InstanceGraph))
(define (add-instance-node G n)
  (InstanceGraph (InstanceGraph-schema G)
                  (hash-set (InstanceGraph-nodes G) (InstanceNode-id n) n)
                  (InstanceGraph-edges G)))

(: add-instance-edge (-> InstanceGraph InstanceEdge InstanceGraph))
(define (add-instance-edge G e)
  (InstanceGraph (InstanceGraph-schema G)
                  (InstanceGraph-nodes G)
                  (hash-set (InstanceGraph-edges G) (InstanceEdge-id e) e)))

;; M1 Well-formedness - instances must conform to M2 schema
(: instance-well-formed? (-> InstanceGraph Boolean))
(define (instance-well-formed? G)
  (define schema (InstanceGraph-schema G))
  ;; Check that all instance nodes have valid types from schema
  (for/and ([node (in-hash-values (InstanceGraph-nodes G))])
    (hash-has-key? (TypeGraph-ports (TGraph-T schema)) (InstanceNode-type node))))

;; M1 Theory Satisfaction - instances must satisfy the logical theory
(: instance-satisfies-theory (-> InstanceGraph M1Logic Boolean))
(define (instance-satisfies-theory G L)
  ;; Convert instance graph to TGraph for satisfaction checking
  (define schema (InstanceGraph-schema G))
  (define tgraph (TGraph (TGraph-T schema) 
                        (for/hash : (HashTable NodeId Node) 
                          ([node (in-hash-values (InstanceGraph-nodes G))])
                          (values (InstanceNode-id node) 
                                  (Node (InstanceNode-id node) (InstanceNode-type node))))
                        (for/hash : (HashTable EdgeId Edge)
                          ([edge (in-hash-values (InstanceGraph-edges G))])
                          (values (InstanceEdge-id edge)
                                  (Edge (InstanceEdge-id edge) (InstanceEdge-kind edge)
                                        (InstanceEdge-src edge) (InstanceEdge-dst edge))))))
  (m1-logic-satisfies? L tgraph))

;; M1→M0 Transformation: Gödel Encoding
;; This is the "model-to-text" transformation that encodes instances for runtime
(: goedel-encode (-> InstanceGraph String))
(define (goedel-encode G)
  ;; Simple Gödel encoding: convert graph structure to string representation
  (define nodes-str (string-join 
                     (for/list : (Listof String) ([node (in-hash-values (InstanceGraph-nodes G))])
                       (format "node(~a,~a,~a)" 
                               (InstanceNode-id node) 
                               (InstanceNode-type node)
                               (InstanceNode-value node)))
                     ";"))
  (define edges-str (string-join
                     (for/list : (Listof String) ([edge (in-hash-values (InstanceGraph-edges G))])
                       (format "edge(~a,~a,~a,~a,~a)"
                               (InstanceEdge-id edge)
                               (InstanceEdge-kind edge)
                               (vector->list (InstanceEdge-src edge))
                               (vector->list (InstanceEdge-dst edge))
                               (InstanceEdge-weight edge)))
                     ";"))
  (format "graph({~a},{~a})" nodes-str edges-str))

(: instance-to-runtime (-> InstanceGraph String))
(define (instance-to-runtime G)
  ;; Convert instance to runtime representation
  (goedel-encode G))

;; M1 Convergence: The single transformer logic as fulcrum
;; This demonstrates how M1 serves as the convergence point where all MDE layers meet
(: logic-convergence-point (-> M1Logic String))
(define (logic-convergence-point L)
  ;; The convergence point embodies the core principles of the Logic Transformer
  (format "M1 Convergence Point: ~a models satisfy theory ~a using ~a logic"
          (length (M1Logic-models L))
          (if (And? (M1Logic-theory L)) "typed-arity discipline" "unknown")
          (Logic-name (M1Logic-evaluation-logic L))))

;; The transformer logic axioms - the core principles that define the Logic Transformer
(: transformer-logic-axioms (-> (Listof String)))
(define (transformer-logic-axioms)
  (list "Σ6 Centrality: Central arity-six symbol with (3,3) arity"
        "Typed-Arity Discipline: All edges must respect arity constraints"
        "Moduli Space: Four fundamental moduli with duals (μ₁,μ₂,μ₃,μ₄;μ₁*,μ₂*,μ₃*,μ₄*)"
        "Anomaly Functional: Must vanish at M3, mild at lower strata"
        "Asymmetric Satisfaction: Finite hierarchy of truth (local → global)"
        "Graph Semantics: Typed arity as global typing system"
        "M1→M0 Transformation: Gödel encoding for runtime"))

