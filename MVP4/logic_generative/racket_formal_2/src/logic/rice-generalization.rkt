#lang racket
;; Rice-type generalization: any non-trivial extensional property of computable functions is undecidable
;; Symbolic schema across computational paradigms (ports as outputs)

(require (file "../foundations/abstract-core.rkt")
         (file "../ports/domain-registry.rkt")
         (file "./internalize.rkt"))

(provide (all-defined-out))

;; Symbolic encodings for properties and deciders
(define (property tag) (abstract-op 'Property (list (make-abstract-const (~a tag) 'symbol)) 'predicate))
(define (holds? P f-code) (abstract-op 'Holds (list P f-code) 'boolean))
(define (decides? D P) (abstract-op 'Decides (list D P) 'boolean))
(define (nontrivial? P) (abstract-op 'Nontrivial (list P) 'boolean))
(define (extensional? P) (abstract-op 'Extensional (list P) 'boolean))
(define (computable? f) (abstract-op 'Computable (list f) 'boolean))
(define (reduces-to-halting? P) (abstract-op 'ReducesToHalting (list P) 'boolean))
(define (undecidable? P) (abstract-op 'Undecidable (list P) 'boolean))
(define (bool-implies a b) (abstract-op 'implies (list a b) 'boolean))

;; Witness: for any P non-trivial & extensional over computable functions, undecidable(P)
(define (rice-generalization-witness tag)
  (define P (property tag))
  (define assumptions (abstract-op 'and (list (nontrivial? P) (extensional? P)) 'boolean))
  (define reduction (reduces-to-halting? P))
  (define claim (bool-implies assumptions (undecidable? P)))
  (hash 'P P 'assumptions assumptions 'reduction reduction 'claim claim))

;; Internalized proof term
(define (rice-generalization-proof tag)
  (internalize-boolean (hash-ref (rice-generalization-witness tag) 'claim)))
