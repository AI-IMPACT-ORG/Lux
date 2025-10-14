#lang racket
;; S-matrix optical identity (renormalised, symbolic)

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../logic/internalize.rkt")
         (file "../../logic/inference.rkt"))

(provide (all-defined-out))

(define (L-lsz-boundary) (embed-proposition (abstract-op 'BoundaryLSZ '() 'meta)))
(define (L-spectral) (embed-proposition (abstract-op 'SpectralCondition (list (make-abstract-const 'qft-default 'symbol)) 'meta)))
(define (L-cluster) (embed-proposition (abstract-op 'ClusterDecomposition (list (make-abstract-const 'qft-default 'symbol)) 'meta)))
(define (L-optical-ren) (embed-proposition (abstract-op 'OpticalIdentityRen '() 'meta)))

;; Sequent: LSZ boundary + spectral + cluster ⇒ OpticalIdentityRen
(define (optical-identity-sequent)
  (sequent (list (L-lsz-boundary) (L-spectral) (L-cluster)) (L-optical-ren)))

(define (smatrix-pack)
  (semiring-element? (optical-identity-sequent)))

;; Partial unitarity under renormalised semantics (symbolic)
(define (L-partial-unit) (embed-proposition (abstract-op 'PartialUnitarityRen '() 'meta)))
(define (partial-unitarity-sequent)
  (sequent (list (L-lsz-boundary) (L-spectral)) (L-partial-unit)))
