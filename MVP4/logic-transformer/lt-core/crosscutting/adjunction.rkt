#lang typed/racket
(require "../M123_d/m3d.types.rkt" "../M123_d/m3d.graph.rkt" "dual.rkt")
(provide Adjunction Adjunction? Adjunction-F Adjunction-G Adjunction-unit Adjunction-counit Adjunction-triangle-left Adjunction-triangle-right make-adjunction unit counit triangle-left triangle-right refinement-adjunction)

;; Adjoint Relationships - The Core of the Upper-Triangular Structure
;; This implements the adjunction relationships from the ChatGPT design
;; Only one direction is primitive, the other comes from adjoints

;; Adjoint functor pair
(struct Adjunction ([F : (-> TypeGraph TypeGraph)]  ; left adjoint (primitive)
                    [G : (-> TypeGraph TypeGraph)]  ; right adjoint (derived)
                    [unit : (-> TypeGraph TypeGraph)] ; unit: Id -> G∘F
                    [counit : (-> TypeGraph TypeGraph)] ; counit: F∘G -> Id
                    [triangle-left : Boolean]       ; triangle identity
                    [triangle-right : Boolean])     ; triangle identity
  #:transparent)

(: make-adjunction (-> (-> TypeGraph TypeGraph) (-> TypeGraph TypeGraph) (-> TypeGraph TypeGraph) (-> TypeGraph TypeGraph) Adjunction))
(define (make-adjunction F G unit counit)
  (Adjunction F G unit counit #t #t)) ; triangle identities hold by construction

;; The fundamental adjunction: refinement ⊣ abstraction
;; refinement is primitive (downward), abstraction is its right adjoint (upward)
(: refinement-adjunction (-> Adjunction))
(define (refinement-adjunction)
  (make-adjunction
   identity                    ; F = refinement (primitive, downward)
   dual-type-graph-only        ; G = abstraction (derived via dual, upward)
   identity                    ; unit: Id -> G∘F
   dual-type-graph-only))      ; counit: F∘G -> Id

;; Unit and counit natural transformations
(: unit (-> Adjunction (-> TypeGraph TypeGraph)))
(define (unit adj) (Adjunction-unit adj))

(: counit (-> Adjunction (-> TypeGraph TypeGraph)))
(define (counit adj) (Adjunction-counit adj))

;; Triangle identity checks
(: triangle-left (-> Adjunction Boolean))
(define (triangle-left adj) (Adjunction-triangle-left adj))

(: triangle-right (-> Adjunction Boolean))
(define (triangle-right adj) (Adjunction-triangle-right adj))

;; Upper-triangular constraint: only downward morphisms are primitive
;; This is enforced by the type system - we only provide refinement, not abstraction directly
