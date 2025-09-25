#lang typed/racket
(require "m3d.types.rkt")
(provide Node Node? Node-id Node-sort Edge Edge? Edge-id Edge-kind Edge-src Edge-dst TGraph TGraph? TGraph-T TGraph-nodes TGraph-edges
         mk-graph add-node add-edge
         well-typed-edge? well-typed-graph?
         ;; Typed-arity constraints - enforce at syntax time
         typed-arity-constraint? enforce-typed-arity
         ;; Asymmetric satisfaction rules - now implemented as observers
         ;; These are now provided by the semiring system
         Submono Submono? Submono-node-dom Submono-edge-dom make-submono submono?
         View View? View-dom View-host View-mono make-view view-host view-dom view-mono)

;; concrete typed graph
(struct Node ([id : NodeId] [sort : PortSort]) #:transparent)
(struct Edge ([id : EdgeId] [kind : EdgeKind]
             [src  : (Vectorof NodeId)] [dst : (Vectorof NodeId)]) #:transparent)

(struct TGraph ([T : TypeGraph]
                [nodes : (HashTable NodeId Node)]
                [edges : (HashTable EdgeId Edge)]) #:transparent)

(: mk-graph (-> TypeGraph TGraph))
(define (mk-graph T)
  (TGraph T (hash) (hash)))

(: add-node (-> TGraph Node TGraph))
(define (add-node G n)
  (TGraph (TGraph-T G)
          (hash-set (TGraph-nodes G) (Node-id n) n)
          (TGraph-edges G)))

(: add-edge (-> TGraph Edge TGraph))
(define (add-edge G e)
  (TGraph (TGraph-T G)
          (TGraph-nodes G)
          (hash-set (TGraph-edges G) (Edge-id e) e)))

;; simplified typing checks
(: well-typed-edge? (-> TGraph Edge Boolean))
(define (well-typed-edge? G e)
  (define T (TGraph-T G))
  (define k (Edge-kind e))
  (define a (arity-of T k))
  (and (= (vector-length (Edge-src e)) (Arity-m a))
       (= (vector-length (Edge-dst e)) (Arity-n a))))

(: well-typed-graph? (-> TGraph Boolean))
(define (well-typed-graph? G)
  (for/and ([e (in-hash-values (TGraph-edges G))]) (well-typed-edge? G e)))

;; Typed-arity constraints - enforce at syntax time that patterns respect arity/types
(: typed-arity-constraint? (-> EdgeKind Natural Natural Boolean))
(define (typed-arity-constraint? kind m n)
  (match kind
    [(== Sigma6) (and (= m 3) (= n 3))]  ; Σ6 has arity (3,3)
    ['wire (and (= m 1) (= n 1))]        ; Wire has arity (1,1)
    ['unit (and (= m 0) (= n 0))]        ; Unit has arity (0,0)
    ['tensor (and (= m 2) (= n 2))]      ; Tensor has arity (2,2)
    ['cast (and (= m 2) (= n 2))]        ; Cast has arity (2,2)
    [_ #f]))                             ; Unknown edge kinds are rejected

(: enforce-typed-arity (-> TGraph Edge Boolean))
(define (enforce-typed-arity G e)
  (define kind (Edge-kind e))
  (define m (vector-length (Edge-src e)))
  (define n (vector-length (Edge-dst e)))
  (typed-arity-constraint? kind m n))

;; Asymmetric satisfaction rules - now implemented as observers in semiring system
;; The local-truth and global-truth functions are now provided by the semiring
;; system as observers (q-local and q-global) that can be composed with
;; different semirings for different evaluation semantics.

;; monos and views
(struct Submono ([node-dom : (Setof NodeId)]
                 [edge-dom : (Setof EdgeId)]) #:transparent)
(: make-submono (-> (Setof NodeId) (Setof EdgeId) Submono))
(define (make-submono ns es) (Submono ns es))

(: submono? (-> TGraph TGraph Submono Boolean))
(define (submono? A G m)
  ;; Simplified implementation for now
  #t)

(struct View ([dom : TGraph] [host : TGraph] [mono : Submono]) #:transparent)
(: make-view (-> TGraph TGraph Submono (U View #f)))
(define (make-view A G m) (if (submono? A G m) (View A G m) #f))
(define view-host View-host)
(define view-dom  View-dom)
(define view-mono View-mono)
