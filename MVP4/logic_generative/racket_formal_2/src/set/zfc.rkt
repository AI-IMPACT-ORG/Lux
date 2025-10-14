#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; ZFC-strength skeleton with internalized axioms as L-level witnesses

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/guarded-negation.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/quantifiers.rkt"))

(provide (all-defined-out))

;; Primitive symbols (symbolic), embedded as L-propositions via asL-bool
(define (Set x) (abstract-op 'Set (list x) 'set))
(define (in x y) (abstract-op '∈ (list x y) 'boolean))
(define (eq x y) (abstract-op '= (list x y) 'boolean))
(define (subset x y) (abstract-op '⊆ (list x y) 'boolean))
(define (asL-bool b) (embed-proposition b))

;; Variables
(define (var s) (abstract-op 'var (list (make-abstract-const s 'symbol)) 'term))

;; Extensionality: ∀x∀y [ (∀z (z∈x ⇔ z∈y)) ⇒ x=y ]
(define (axiom-extensionality)
  (define x (var 'x)) (define y (var 'y)) (define z (var 'z))
  (define zx (in z x)) (define zy (in z y))
  (define equiv (abstract-op 'equiv (list zx zy) 'boolean))
  (define inner (b-forall z equiv))
  (define implies (abstract-op 'implies (list inner (eq x y)) 'boolean))
  (define formula (b-forall x (b-forall y implies)))
  (asL-bool formula))

;; Pairing: ∀x∀y ∃p ∀z [ z∈p ⇔ (z=x ∨ z=y) ]
(define (axiom-pairing)
  (define x (var 'x)) (define y (var 'y)) (define z (var 'z)) (define p (var 'p))
  (define zInP (in z p))
  (define zEq (abstract-op 'or (list (eq z x) (eq z y)) 'boolean))
  (define equiv (abstract-op 'equiv (list zInP zEq) 'boolean))
  (define body (b-exists p (b-forall z equiv)))
  (asL-bool (b-forall x (b-forall y body))))

;; Union: ∀x ∃u ∀z [ z∈u ⇔ ∃y (z∈y ∧ y∈x) ]
(define (axiom-union)
  (define x (var 'x)) (define y (var 'y)) (define z (var 'z)) (define u (var 'u))
  (define zInU (in z u))
  (define conj (abstract-op 'and (list (in z y) (in y x)) 'boolean))
  (define rhs (b-exists y conj))
  (define equiv (abstract-op 'equiv (list zInU rhs) 'boolean))
  (asL-bool (b-forall x (b-exists u (b-forall z equiv)))))

;; Power set: ∀x ∃p ∀y [ y∈p ⇔ y⊆x ]
(define (axiom-powerset)
  (define x (var 'x)) (define y (var 'y)) (define p (var 'p))
  (define yInP (in y p))
  (define ySubX (subset y x))
  (define equiv (abstract-op 'equiv (list yInP ySubX) 'boolean))
  (asL-bool (b-forall x (b-exists p (b-forall y equiv)))))

;; Infinity: ∃I [ ∅∈I ∧ ∀x∈I (x∪{x})∈I ] (symbolic schema)
(define (axiom-infinity)
  (define I (var 'I))
  (asL-bool (b-exists I (abstract-op 'Infinity (list I) 'boolean))))

;; Choice (symbolic): AC — ∀X (family of nonempty, pairwise disjoint) ⇒ ∃f choice function
(define (axiom-choice)
  (asL-bool (abstract-op 'AC '() 'boolean)))

;; Schemas (guarded): rely on a GuardWF(G) side condition
(define (schema-separation-guarded φ G)
  (define x (var 'x)) (define y (var 'y)) (define z (var 'z))
  (define zInY (in z y))
  (define zInX (in z x))
  (define guard (abstract-op 'Guard (list z G) 'boolean))
  (define conj (abstract-op 'and (list zInX guard (abstract-op 'holds (list z φ) 'boolean)) 'boolean))
  (define equiv (abstract-op 'equiv (list zInY conj) 'boolean))
  (define body (b-forall x (b-exists y (b-forall z equiv))))
  (gn-implies (guard-wf G) (asL-bool body)))

(define (schema-replacement-guarded φ G)
  (define x (var 'x)) (define y (var 'y)) (define u (var 'u)) (define v (var 'v))
  (define vInY (in v y))
  (define guardU (abstract-op 'Guard (list u G) 'boolean))
  (define existsUV (b-exists u (abstract-op 'and (list (in u x)
                                                       guardU
                                                       (abstract-op 'holds (list (abstract-op 'pair (list u v) 'term) φ) 'boolean)) 'boolean)))
  (define equiv (abstract-op 'equiv (list vInY existsUV) 'boolean))
  (define body (b-forall x (b-exists y (b-forall v equiv))))
  (gn-implies (guard-wf G) (asL-bool body)))

;; Bundle of standard axioms as L-level witnesses
(define (zfc-axioms)
  (list (cons 'Extensionality (axiom-extensionality))
        (cons 'Pairing (axiom-pairing))
        (cons 'Union (axiom-union))
        (cons 'PowerSet (axiom-powerset))
        (cons 'Infinity (axiom-infinity))
        (cons 'Choice (axiom-choice))))

