#lang typed/racket
(require "../M123_d/m3d.types.rkt" "../M123_d/m3d.graph.rkt")
(provide dual-graph dual-node dual-edge dual-type-graph dual-type-graph-only
         Node Node? Node-id Node-sort Edge Edge? Edge-id Edge-kind Edge-src Edge-dst
         TGraph TGraph? TGraph-T TGraph-nodes TGraph-edges
         TypeGraph TypeGraph? TypeGraph-ports TypeGraph-kinds TypeGraph-arity TypeGraph-srcS TypeGraph-dstS
         Arity Arity-m Arity-n make-type-graph arity-of src-sort-of dst-sort-of
         mk-graph add-node add-edge well-typed-edge? well-typed-graph?
         Submono Submono? Submono-node-dom Submono-edge-dom make-submono submono?
         View View? View-dom View-host View-mono make-view)

;; Dual Graph Construction - Node-Edge Duality
;; This implements the precise dual graph relationship from the ChatGPT design
;; Nodes become edges, edges become nodes, with proper arity constraints

;; Dual of a node: becomes an edge with arity (1,1)
(: dual-node (-> Node Edge))
(define (dual-node n)
  (Edge (Node-id n)                    ; edge id = node id
        (string->symbol (string-append "node-" (symbol->string (Node-sort n)))) ; edge kind
        (vector (Node-id n))           ; source = self
        (vector (Node-id n))))         ; target = self

;; Dual of an edge: becomes a node
(: dual-edge (-> Edge Node))
(define (dual-edge e)
  (Node (Edge-id e)                    ; node id = edge id
        (string->symbol (string-append "edge-" (symbol->string (Edge-kind e)))))) ; node sort

;; Dual of a type graph: swaps nodes and edges
(: dual-type-graph (-> TypeGraph TypeGraph))
(define (dual-type-graph T)
  (TypeGraph
   ;; Port sorts become edge kinds (with dual naming)
   (for/hash : (HashTable PortSort True) ([k (hash-keys (TypeGraph-kinds T))])
     (values (string->symbol (string-append "edge-" (symbol->string k))) #t))
   ;; Edge kinds become port sorts (with dual naming)  
   (for/hash : (HashTable EdgeKind True) ([p (hash-keys (TypeGraph-ports T))])
     (values (string->symbol (string-append "node-" (symbol->string p))) #t))
   ;; Arity constraints: edge arity (m,n) becomes node arity constraints
   (for/hash : (HashTable EdgeKind Arity) ([k (hash-keys (TypeGraph-arity T))])
     (values (string->symbol (string-append "edge-" (symbol->string k)))
             (Arity (Arity-m (hash-ref (TypeGraph-arity T) k))
                    (Arity-n (hash-ref (TypeGraph-arity T) k)))))
   ;; Source/target sorts become dual constraints
   (for/hash : (HashTable EdgeKind (Vectorof PortSort)) ([k (hash-keys (TypeGraph-srcS T))])
     (let* ([src-vec (hash-ref (TypeGraph-srcS T) k)]
            [src-sort (if (> (vector-length src-vec) 0)
                         (vector-ref src-vec 0)
                         'port)])
       (values (string->symbol (string-append "edge-" (symbol->string k)))
               (vector (string->symbol (string-append "node-" (symbol->string src-sort)))))))
   (for/hash : (HashTable EdgeKind (Vectorof PortSort)) ([k (hash-keys (TypeGraph-dstS T))])
     (let* ([dst-vec (hash-ref (TypeGraph-dstS T) k)]
            [dst-sort (if (> (vector-length dst-vec) 0)
                         (vector-ref dst-vec 0)
                         'port)])
       (values (string->symbol (string-append "edge-" (symbol->string k)))
               (vector (string->symbol (string-append "node-" (symbol->string dst-sort)))))))))

;; Dual of a graph: applies dual transformation to all nodes and edges
(: dual-graph (-> TGraph TGraph))
(define (dual-graph G)
  (define dual-T (dual-type-graph (TGraph-T G)))
  (define dual-nodes (for/hash : (HashTable NodeId Node) ([e (in-hash-values (TGraph-edges G))])
                       (values (Edge-id e) (dual-edge e))))
  (define dual-edges (for/hash : (HashTable EdgeId Edge) ([n (in-hash-values (TGraph-nodes G))])
                       (values (Node-id n) (dual-node n))))
  (TGraph dual-T dual-nodes dual-edges))

;; Dual type graph only (for adjunction compatibility)
(: dual-type-graph-only (-> TypeGraph TypeGraph))
(define (dual-type-graph-only T) (dual-type-graph T))

