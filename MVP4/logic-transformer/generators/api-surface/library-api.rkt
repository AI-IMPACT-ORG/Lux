#lang typed/racket
;; Library API Surface Definitions
;; This module defines the clean API surface that all generated libraries should expose
;; Language-specific details are abstracted away through this interface

(provide LibraryAPI LibraryAPI? LibraryAPI-name LibraryAPI-version LibraryAPI-description
         LibraryAPI-modules LibraryAPI-functions LibraryAPI-types LibraryAPI-axioms LibraryAPI-theorems
         LibraryModule LibraryModule? LibraryModule-name LibraryModule-description
         LibraryModule-exports LibraryModule-dependencies
         LibraryFunction LibraryFunction? LibraryFunction-name LibraryFunction-signature
         LibraryFunction-description LibraryFunction-module LibraryFunction-is-pure
         LibraryType LibraryType? LibraryType-name LibraryType-definition
         LibraryType-description LibraryType-module LibraryType-constructors
         LibraryAxiom LibraryAxiom? LibraryAxiom-name LibraryAxiom-statement
         LibraryAxiom-description LibraryAxiom-module
         LibraryTheorem LibraryTheorem? LibraryTheorem-name LibraryTheorem-statement
         LibraryTheorem-proof LibraryTheorem-description LibraryTheorem-module LibraryTheorem-dependencies
         
         ;; API Surface Construction
         make-library-api
         add-module add-function add-type add-axiom add-theorem
         
         ;; API Surface Queries
         get-modules get-functions get-types get-axioms get-theorems
         find-module find-function find-type
         
         ;; API Surface Validation
         validate-api-surface
         
         ;; Standard Library API Templates
         minimal-logic-api propositional-logic-api
         graph-theory-api category-theory-api
         mde-pyramid-api)

;; Core API Surface Types
(struct LibraryAPI ([name : String]
                    [version : String]
                    [description : String]
                    [modules : (Listof LibraryModule)]
                    [functions : (Listof LibraryFunction)]
                    [types : (Listof LibraryType)]
                    [axioms : (Listof LibraryAxiom)]
                    [theorems : (Listof LibraryTheorem)]) #:transparent)

(struct LibraryModule ([name : String]
                       [description : String]
                       [exports : (Listof String)]
                       [dependencies : (Listof String)]) #:transparent)

(struct LibraryFunction ([name : String]
                         [signature : String]
                         [description : String]
                         [module : String]
                         [is-pure : Boolean]) #:transparent)

(struct LibraryType ([name : String]
                     [definition : String]
                     [description : String]
                     [module : String]
                     [constructors : (Listof String)]) #:transparent)

(struct LibraryAxiom ([name : String]
                       [statement : String]
                       [description : String]
                       [module : String]) #:transparent)

(struct LibraryTheorem ([name : String]
                         [statement : String]
                         [proof : String]
                         [description : String]
                         [module : String]
                         [dependencies : (Listof String)]) #:transparent)

;; API Surface Construction
(: make-library-api (-> String String String LibraryAPI))
(define (make-library-api name version description)
  (LibraryAPI name version description '() '() '() '() '()))

(: add-module (-> LibraryAPI LibraryModule LibraryAPI))
(define (add-module api module)
  (struct-copy LibraryAPI api [modules (cons module (LibraryAPI-modules api))]))

(: add-function (-> LibraryAPI LibraryFunction LibraryAPI))
(define (add-function api func)
  (struct-copy LibraryAPI api [functions (cons func (LibraryAPI-functions api))]))

(: add-type (-> LibraryAPI LibraryType LibraryAPI))
(define (add-type api type)
  (struct-copy LibraryAPI api [types (cons type (LibraryAPI-types api))]))

(: add-axiom (-> LibraryAPI LibraryAxiom LibraryAPI))
(define (add-axiom api axiom)
  (struct-copy LibraryAPI api [axioms (cons axiom (LibraryAPI-axioms api))]))

(: add-theorem (-> LibraryAPI LibraryTheorem LibraryAPI))
(define (add-theorem api theorem)
  (struct-copy LibraryAPI api [theorems (cons theorem (LibraryAPI-theorems api))]))

;; API Surface Queries
(: get-modules (-> LibraryAPI (Listof LibraryModule)))
(define (get-modules api) (LibraryAPI-modules api))

(: get-functions (-> LibraryAPI (Listof LibraryFunction)))
(define (get-functions api) (LibraryAPI-functions api))

(: get-types (-> LibraryAPI (Listof LibraryType)))
(define (get-types api) (LibraryAPI-types api))

(: get-axioms (-> LibraryAPI (Listof LibraryAxiom)))
(define (get-axioms api) (LibraryAPI-axioms api))

(: get-theorems (-> LibraryAPI (Listof LibraryTheorem)))
(define (get-theorems api) (LibraryAPI-theorems api))

(: find-module (-> LibraryAPI String (U LibraryModule #f)))
(define (find-module api name)
  (findf (lambda ([m : LibraryModule]) (string=? (LibraryModule-name m) name))
         (LibraryAPI-modules api)))

(: find-function (-> LibraryAPI String (U LibraryFunction #f)))
(define (find-function api name)
  (findf (lambda ([f : LibraryFunction]) (string=? (LibraryFunction-name f) name))
         (LibraryAPI-functions api)))

(: find-type (-> LibraryAPI String (U LibraryType #f)))
(define (find-type api name)
  (findf (lambda ([t : LibraryType]) (string=? (LibraryType-name t) name))
         (LibraryAPI-types api)))

;; API Surface Validation
(: validate-api-surface (-> LibraryAPI Boolean))
(define (validate-api-surface api)
  (and
   ;; Check that all functions reference valid modules
   (for/and : Boolean ([func (LibraryAPI-functions api)])
     (not (not (find-module api (LibraryFunction-module func)))))
   
   ;; Check that all types reference valid modules
   (for/and : Boolean ([type (LibraryAPI-types api)])
     (not (not (find-module api (LibraryType-module type)))))
   
   ;; Check that all axioms reference valid modules
   (for/and : Boolean ([axiom (LibraryAPI-axioms api)])
     (not (not (find-module api (LibraryAxiom-module axiom)))))
   
   ;; Check that all theorems reference valid modules
   (for/and : Boolean ([theorem (LibraryAPI-theorems api)])
     (not (not (find-module api (LibraryTheorem-module theorem)))))
   
   ;; Check that theorem dependencies exist
   (for/and : Boolean ([theorem (LibraryAPI-theorems api)])
     (for/and : Boolean ([dep (LibraryTheorem-dependencies theorem)])
       (or (not (not (find-axiom api dep))) (not (not (find-theorem api dep))))))))

(: find-axiom (-> LibraryAPI String (U LibraryAxiom #f)))
(define (find-axiom api name)
  (findf (lambda ([a : LibraryAxiom]) (string=? (LibraryAxiom-name a) name))
         (LibraryAPI-axioms api)))

(: find-theorem (-> LibraryAPI String (U LibraryTheorem #f)))
(define (find-theorem api name)
  (findf (lambda ([t : LibraryTheorem]) (string=? (LibraryTheorem-name t) name))
         (LibraryAPI-theorems api)))

;; Standard Library API Templates

;; Minimal Logic API - Graph-based semantics with minimal logical primitives
(: minimal-logic-api (-> LibraryAPI))
(define (minimal-logic-api)
  (let* ([api (make-library-api "MinimalLogic" "1.0.0" 
                                "Minimal logic with graph-based semantics - the foundation of all mathematics")]
         [core-module (LibraryModule "Core" "Core logical primitives" 
                                     '("Prop" "Implication" "Truth" "Falsity") '())]
         [graph-semantics-module (LibraryModule "GraphSemantics" "Graph-based logical semantics" 
                                               '("Graph" "Node" "Edge" "Connection" "Communication") '("Core"))]
         [api (add-module api core-module)]
         [api (add-module api graph-semantics-module)]
         
         ;; Core logical types
         [prop-type (LibraryType "Prop" "Propositional formula" "Core propositional type" "Core" '())]
         [impl-type (LibraryType "Implication" "Implication connective" "Logical implication" "Core" '())]
         [truth-type (LibraryType "Truth" "Truth constant" "Logical truth" "Core" '())]
         [falsity-type (LibraryType "Falsity" "Falsity constant" "Logical falsity" "Core" '())]
         [api (add-type api prop-type)]
         [api (add-type api impl-type)]
         [api (add-type api truth-type)]
         [api (add-type api falsity-type)]
         
         ;; Graph semantics types
         [graph-type (LibraryType "Graph" "Graph structure" "Basic unit of connection" "GraphSemantics" '())]
         [node-type (LibraryType "Node" "Graph node" "Connection point" "GraphSemantics" '())]
         [edge-type (LibraryType "Edge" "Graph edge" "Connection between nodes" "GraphSemantics" '())]
         [connection-type (LibraryType "Connection" "Connection relation" "Fundamental connection" "GraphSemantics" '())]
         [communication-type (LibraryType "Communication" "Communication channel" "Information flow" "GraphSemantics" '())]
         [api (add-type api graph-type)]
         [api (add-type api node-type)]
         [api (add-type api edge-type)]
         [api (add-type api connection-type)]
         [api (add-type api communication-type)]
         
         ;; Core logical functions
         [satisfies-func (LibraryFunction "satisfies" "Prop -> Graph -> Boolean" 
                                         "Graph-based satisfaction relation" "Core" #t)]
         [valid-func (LibraryFunction "valid" "Prop -> Boolean" 
                                     "Validity predicate" "Core" #t)]
         [modus-ponens-func (LibraryFunction "modus-ponens" "Implication -> Prop -> Prop" 
                                            "Modus ponens inference rule" "Core" #t)]
         [api (add-function api satisfies-func)]
         [api (add-function api valid-func)]
         [api (add-function api modus-ponens-func)]
         
         ;; Graph semantics functions
         [connect-func (LibraryFunction "connect" "Node -> Node -> Edge" 
                                       "Create connection between nodes" "GraphSemantics" #t)]
         [communicate-func (LibraryFunction "communicate" "Edge -> Communication" 
                                           "Establish communication channel" "GraphSemantics" #t)]
         [flow-func (LibraryFunction "flow" "Communication -> Graph -> Boolean" 
                                    "Information flow predicate" "GraphSemantics" #t)]
         [api (add-function api connect-func)]
         [api (add-function api communicate-func)]
         [api (add-function api flow-func)]
         
         ;; Core axioms
         [truth-axiom (LibraryAxiom "truth-axiom" "Truth is always satisfied" "Truth is always true" "Core")]
         [falsity-axiom (LibraryAxiom "falsity-axiom" "Falsity implies anything" "Ex falso quodlibet" "Core")]
         [impl-axiom1 (LibraryAxiom "implication-axiom-1" "Implication introduction" "P implies Q implies P" "Core")]
         [impl-axiom2 (LibraryAxiom "implication-axiom-2" "Implication distribution" "Implication distributes" "Core")]
         [api (add-axiom api truth-axiom)]
         [api (add-axiom api falsity-axiom)]
         [api (add-axiom api impl-axiom1)]
         [api (add-axiom api impl-axiom2)]
         
         ;; Graph semantics axioms
         [connection-axiom (LibraryAxiom "connection-axiom" "All connections are bidirectional" "Connection symmetry" "GraphSemantics")]
         [communication-axiom (LibraryAxiom "communication-axiom" "Communication preserves information" "Information preservation" "GraphSemantics")]
         [flow-axiom (LibraryAxiom "flow-axiom" "Information flows along connections" "Flow along edges" "GraphSemantics")]
         [api (add-axiom api connection-axiom)]
         [api (add-axiom api communication-axiom)]
         [api (add-axiom api flow-axiom)]
         
         ;; Core theorems
         [modus-ponens-thm (LibraryTheorem "modus-ponens-theorem" 
                                          "Modus ponens is valid" 
                                          "Proof of modus ponens validity"
                                          "Modus ponens inference rule" 
                                          "Core" 
                                          '("implication-axiom-1" "implication-axiom-2"))]
         [connection-thm (LibraryTheorem "connection-theorem" 
                                         "Connections form graphs" 
                                         "Proof that connections form graph structure"
                                         "Graph formation from connections" 
                                         "GraphSemantics" 
                                         '("connection-axiom"))]
         [api (add-theorem api modus-ponens-thm)]
         [api (add-theorem api connection-thm)])
    api))

;; Propositional Logic API - Extended from minimal logic
(: propositional-logic-api (-> LibraryAPI))
(define (propositional-logic-api)
  (let* ([api (minimal-logic-api)]
         [api (struct-copy LibraryAPI api [name "PropositionalLogic"] 
                           [description "Complete propositional logic with all connectives"])]
         
         ;; Additional types
         [conj-type (LibraryType "Conjunction" "P /\\ Q" "Conjunction connective" "Core" '("make-conjunction"))]
         [disj-type (LibraryType "Disjunction" "P \\/ Q" "Disjunction connective" "Core" '("make-disjunction"))]
         [neg-type (LibraryType "Negation" "~P" "Negation connective" "Core" '("make-negation"))]
         [api (add-type api conj-type)]
         [api (add-type api disj-type)]
         [api (add-type api neg-type)]
         
         ;; Additional axioms
         [conj-axiom (LibraryAxiom "conjunction-axiom" "P /\\ Q <-> ~(P -> ~Q)" "Conjunction definition" "Core")]
         [disj-axiom (LibraryAxiom "disjunction-axiom" "P \\/ Q <-> (~P -> Q)" "Disjunction definition" "Core")]
         [neg-axiom (LibraryAxiom "negation-axiom" "~P <-> (P -> F)" "Negation definition" "Core")]
         [api (add-axiom api conj-axiom)]
         [api (add-axiom api disj-axiom)]
         [api (add-axiom api neg-axiom)])
    api))

;; Graph Theory API - Built on propositional logic with graph-based semantics
(: graph-theory-api (-> LibraryAPI))
(define (graph-theory-api)
  (let* ([api (propositional-logic-api)]
         [api (struct-copy LibraryAPI api [name "GraphTheory"] 
                           [description "Graph theory with graph-based semantics - connections and communication"])]
         
         [graph-module (LibraryModule "Graph" "Core graph primitives" 
                                     '("Graph" "Node" "Edge" "Path" "Cycle") '("PropositionalLogic"))]
         [transformation-module (LibraryModule "Transformation" "Graph transformations" 
                                             '("transform" "normalize" "dual") '("Graph"))]
         [api (add-module api graph-module)]
         [api (add-module api transformation-module)]
         
         ;; Core graph types
         [graph-type (LibraryType "Graph" "Graph structure" "Basic unit of connection" "Graph" '())]
         [node-type (LibraryType "Node" "Graph node" "Connection point" "Graph" '())]
         [edge-type (LibraryType "Edge" "Graph edge" "Connection between nodes" "Graph" '())]
         [path-type (LibraryType "Path" "Graph path" "Sequence of connected edges" "Graph" '())]
         [cycle-type (LibraryType "Cycle" "Graph cycle" "Closed path" "Graph" '())]
         [api (add-type api graph-type)]
         [api (add-type api node-type)]
         [api (add-type api edge-type)]
         [api (add-type api path-type)]
         [api (add-type api cycle-type)]
         
         ;; Graph construction functions
         [create-graph-func (LibraryFunction "create-graph" "Listof Node -> Listof Edge -> Graph" "Create graph from nodes and edges" "Graph" #t)]
         [add-node-func (LibraryFunction "add-node" "Graph -> Node -> Graph" "Add node to graph" "Graph" #t)]
         [add-edge-func (LibraryFunction "add-edge" "Graph -> Edge -> Graph" "Add edge to graph" "Graph" #t)]
         [find-path-func (LibraryFunction "find-path" "Graph -> Node -> Node -> Path" "Find path between nodes" "Graph" #t)]
         [api (add-function api create-graph-func)]
         [api (add-function api add-node-func)]
         [api (add-function api add-edge-func)]
         [api (add-function api find-path-func)]
         
         ;; Transformation functions
         [transform-func (LibraryFunction "transform" "Graph -> Graph" "Transform graph structure" "Transformation" #t)]
         [normalize-func (LibraryFunction "normalize" "Graph -> Graph" "Normalize graph" "Transformation" #t)]
         [dual-func (LibraryFunction "dual" "Graph -> Graph" "Compute dual graph" "Transformation" #t)]
         [api (add-function api transform-func)]
         [api (add-function api normalize-func)]
         [api (add-function api dual-func)]
         
         ;; Graph axioms
         [path-axiom (LibraryAxiom "path-axiom" "Paths connect nodes" "Path connectivity" "Graph")]
         [cycle-axiom (LibraryAxiom "cycle-axiom" "Cycles are closed paths" "Cycle closure" "Graph")]
         [dual-axiom (LibraryAxiom "dual-axiom" "Dual is involutive" "Dual involution" "Transformation")]
         [normalization-axiom (LibraryAxiom "normalization-axiom" "Normalization preserves connectivity" "Normalization preservation" "Transformation")]
         [api (add-axiom api path-axiom)]
         [api (add-axiom api cycle-axiom)]
         [api (add-axiom api dual-axiom)]
         [api (add-axiom api normalization-axiom)])
    api))

;; Category Theory API - Built on graph theory with graph-based semantics
(: category-theory-api (-> LibraryAPI))
(define (category-theory-api)
  (let* ([api (graph-theory-api)]
         [api (struct-copy LibraryAPI api [name "CategoryTheory"] 
                           [description "Category theory with graph-based semantics - structured connections"])]
         
         [category-module (LibraryModule "Category" "Category theory primitives" 
                                        '("Category" "Functor" "NaturalTransformation") '("GraphTheory"))]
         [structure-module (LibraryModule "Structure" "Categorical structure" 
                                         '("compose" "identity" "associativity") '("Category"))]
         [api (add-module api category-module)]
         [api (add-module api structure-module)]
         
         ;; Category types
         [category-type (LibraryType "Category" "Category structure" "Mathematical category" "Category" '())]
         [functor-type (LibraryType "Functor" "Category functor" "Structure-preserving map" "Category" '())]
         [naturaltrans-type (LibraryType "NaturalTransformation" "Natural transformation" "Structure-preserving transformation" "Category" '())]
         [api (add-type api category-type)]
         [api (add-type api functor-type)]
         [api (add-type api naturaltrans-type)]
         
         ;; Category functions
         [compose-func (LibraryFunction "compose" "Graph -> Graph -> Graph" "Compose graph transformations" "Category" #t)]
         [identity-func (LibraryFunction "identity" "Graph -> Graph" "Identity transformation" "Category" #t)]
         [map-func (LibraryFunction "map" "Functor -> Graph -> Graph" "Apply functor to graph" "Category" #t)]
         [api (add-function api compose-func)]
         [api (add-function api identity-func)]
         [api (add-function api map-func)]
         
         ;; Structure functions
         [associativity-func (LibraryFunction "associativity" "Graph -> Graph -> Graph -> Boolean" "Check associativity" "Structure" #t)]
         [identity-law-func (LibraryFunction "identity-law" "Graph -> Boolean" "Check identity laws" "Structure" #t)]
         [api (add-function api associativity-func)]
         [api (add-function api identity-law-func)]
         
         ;; Category axioms
         [associativity-axiom (LibraryAxiom "associativity-axiom" "Composition is associative" "Associativity law" "Structure")]
         [identity-axiom (LibraryAxiom "identity-axiom" "Identity preserves structure" "Identity law" "Structure")]
         [functor-axiom (LibraryAxiom "functor-axiom" "Functors preserve structure" "Functor preservation" "Category")]
         [api (add-axiom api associativity-axiom)]
         [api (add-axiom api identity-axiom)]
         [api (add-axiom api functor-axiom)])
    api))

;; MDE Pyramid API - The Logic Transformer's core contribution with graph-based semantics
(: mde-pyramid-api (-> LibraryAPI))
(define (mde-pyramid-api)
  (let* ([api (category-theory-api)]
         [api (struct-copy LibraryAPI api [name "MDEPyramid"] 
                           [description "Model-Driven Engineering pyramid: M3->M2->M1 with transformer logic convergence"])]
         
         [m3-module (LibraryModule "M3" "Metametamodel - Foundation" 
                                  '("TypeGraph" "Sigma6" "Arity") '("CategoryTheory"))]
         [m2-module (LibraryModule "M2" "Metamodel - Structure" 
                                  '("PGC" "Certificate" "GuardEnv") '("M3"))]
         [m1-module (LibraryModule "M1" "Model - Logic" 
                                  '("Logic" "TransformerLogic" "InstanceGraph") '("M2"))]
         [convergence-module (LibraryModule "Convergence" "M1 convergence point" 
                                           '("logic-convergence-point" "transformer-logic-axioms" "encode") '("M1"))]
         [api (add-module api m3-module)]
         [api (add-module api m2-module)]
         [api (add-module api m1-module)]
         [api (add-module api convergence-module)]
         
         ;; M3 Foundation types
         [typegraph-type (LibraryType "TypeGraph" "M3 type graph" "Foundation type system" "M3" '())]
         [sigma6-type (LibraryType "Sigma6" "Central arity-six symbol" "Core Σ6 with (3,3) arity" "M3" '())]
         [arity-type (LibraryType "Arity" "Edge arity" "Input/output arity specification" "M3" '())]
         [api (add-type api typegraph-type)]
         [api (add-type api sigma6-type)]
         [api (add-type api arity-type)]
         
         ;; M2 Structure types
         [pgc-type (LibraryType "PGC" "Positive Guarded Condition" "M2 logical condition" "M2" '())]
         [certificate-type (LibraryType "Certificate" "M2 certificate" "M2 proof certificate" "M2" '())]
         [guard-env-type (LibraryType "GuardEnv" "Guard environment" "M2 guard context" "M2" '())]
         [api (add-type api pgc-type)]
         [api (add-type api certificate-type)]
         [api (add-type api guard-env-type)]
         
         ;; M1 Logic types
         [logic-type (LibraryType "Logic" "M1 logic" "Convergent logic system" "M1" '())]
         [transformer-logic-type (LibraryType "TransformerLogic" "Single transformer logic" "The fulcrum of MDE pyramid" "M1" '())]
         [instance-graph-type (LibraryType "InstanceGraph" "M1 instance graph" "Runtime graph instance" "M1" '())]
         [api (add-type api logic-type)]
         [api (add-type api transformer-logic-type)]
         [api (add-type api instance-graph-type)]
         
         ;; M3 Foundation functions
         [create-type-graph-func (LibraryFunction "create-type-graph" "Graph -> TypeGraph" "Create M3 type graph from graph" "M3" #t)]
         [measure-arity-func (LibraryFunction "measure-arity" "Graph -> Arity" "Measure graph arity" "M3" #t)]
         [api (add-function api create-type-graph-func)]
         [api (add-function api measure-arity-func)]
         
         ;; M2 Structure functions
         [satisfies-func (LibraryFunction "satisfies" "Graph -> GuardEnv -> PGC -> Boolean" 
                                         "M2 satisfaction relation" "M2" #t)]
         [create-guard-func (LibraryFunction "create-guard" "Graph -> GuardEnv" "Create guard environment from graph" "M2" #t)]
         [api (add-function api satisfies-func)]
         [api (add-function api create-guard-func)]
         
         ;; M1 Logic functions
         [create-logic-func (LibraryFunction "create-logic" "PGC -> Graph -> Logic" "Create M1 logic from PGC and graph" "M1" #t)]
         [logic-satisfies-func (LibraryFunction "logic-satisfies" "Logic -> Graph -> Boolean" 
                                               "Check logic satisfaction" "M1" #t)]
         [instance-well-formed-func (LibraryFunction "instance-well-formed" "InstanceGraph -> Boolean" 
                                                    "Check instance well-formedness" "M1" #t)]
         [api (add-function api create-logic-func)]
         [api (add-function api logic-satisfies-func)]
         [api (add-function api instance-well-formed-func)]
         
         ;; Convergence functions
         [logic-convergence-point-func (LibraryFunction "logic-convergence-point" "Logic -> String" 
                                                        "Describe convergence point" "Convergence" #t)]
         [transformer-logic-axioms-func (LibraryFunction "transformer-logic-axioms" "Unit -> Listof String" 
                                                        "Get transformer logic axioms" "Convergence" #t)]
         [encode-func (LibraryFunction "encode" "InstanceGraph -> String" 
                                       "Encode for runtime" "Convergence" #t)]
         [api (add-function api logic-convergence-point-func)]
         [api (add-function api transformer-logic-axioms-func)]
         [api (add-function api encode-func)]
         
         ;; MDE axioms
         [sigma6-centrality-axiom (LibraryAxiom "sigma6-centrality" "Sigma6 has arity (3,3)" "Central arity-six symbol" "M3")]
         [typed-arity-discipline-axiom (LibraryAxiom "typed-arity-discipline" "All edges respect arity constraints" "Typed-arity discipline" "M3")]
         [graph-semantics-axiom (LibraryAxiom "graph-semantics" "Graphs provide semantics" "Graph semantics" "M2")]
         [m1-convergence-axiom (LibraryAxiom "m1-convergence" "Single transformer logic as fulcrum" "M1 convergence point" "M1")]
         [encoding-axiom (LibraryAxiom "encoding-axiom" "M1→M0 transformation for runtime" "Runtime encoding" "Convergence")]
         [api (add-axiom api sigma6-centrality-axiom)]
         [api (add-axiom api typed-arity-discipline-axiom)]
         [api (add-axiom api graph-semantics-axiom)]
         [api (add-axiom api m1-convergence-axiom)]
         [api (add-axiom api encoding-axiom)])
    api))
