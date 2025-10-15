#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Analytic S‑matrix axioms (symbolic, port-level): analyticity, crossing, unitarity cuts,
;; polynomial boundedness, dispersion relations, Froissart–Martin bound.

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../logic/internalize.rkt")
         (file "../../logic/inference.rkt")
         (file "./evidence.rkt")
         (file "./smatrix.rkt"))

(provide (all-defined-out))

;; Notation: Mandelstam variables (symbolic)
(define s (make-abstract-const 's 'symbol))
(define t (make-abstract-const 't 'symbol))
(define u (make-abstract-const 'u 'symbol))

;; L-level proposition constructors
(define (L-analytic-region region)
  (embed-proposition (abstract-op 'AnalyticSM (list s t (make-abstract-const region 'symbol)) 'meta)))
(define (L-crossing) (embed-proposition (abstract-op 'CrossingSymmetry (list s t u) 'meta)))
(define (L-unitarity-cut) (embed-proposition (abstract-op 'UnitarityCut (list s) 'meta)))
(define (L-poly-bound n) (embed-proposition (abstract-op 'PolynomialBound (list s t (make-abstract-const n 'integer)) 'meta)))
(define (L-dispersion k) (embed-proposition (abstract-op 'DispersionRelation (list s t (make-abstract-const k 'integer)) 'meta)))
(define (L-froissart) (embed-proposition (abstract-op 'FroissartMartin (list s) 'meta)))

;; Assumptions reused from S-matrix and QFT evidence packs
(define (L-locality lbl) (embed-proposition (abstract-op 'Locality (list (make-abstract-const lbl 'symbol)) 'meta)))
(define (L-microcausality lbl) (embed-proposition (abstract-op 'Microcausality (list (make-abstract-const lbl 'symbol)) 'meta)))
(define (L-spectral lbl) (embed-proposition (abstract-op 'SpectralCondition (list (make-abstract-const lbl 'symbol)) 'meta)))
(define (L-cluster lbl) (embed-proposition (abstract-op 'ClusterDecomposition (list (make-abstract-const lbl 'symbol)) 'meta)))

;; 1) Analyticity: LSZ+Spectral+Locality+Microcausality ⇒ Analytic region (Lehmann–Martin ellipse)
(define (sm-analyticity-sequent #:label [label 'qft-default])
  (define Γ (list (L-lsz-boundary)
                  (L-spectral label)
                  (L-locality label)
                  (L-microcausality label)))
  (sequent Γ (L-analytic-region 'LehmannMartinEllipse)))

;; 2) Crossing symmetry: Locality+Microcausality ⇒ CrossingSymmetry
(define (sm-crossing-sequent #:label [label 'qft-default])
  (define Γ (list (L-locality label) (L-microcausality label)))
  (sequent Γ (L-crossing)))

;; 3) Unitarity cuts: OpticalIdentityRen+PartialUnitarityRen ⇒ UnitarityCut
(define (sm-unitarity-cut-sequent)
  (sequent (list (L-optical-ren) (L-partial-unit)) (L-unitarity-cut)))

;; 4) Dispersion relation: Analytic + PolynomialBound ⇒ DispersionRelation (once-subtracted)
(define (sm-dispersion-sequent)
  (define Γ (list (L-analytic-region 'LehmannMartinEllipse)
                  (L-poly-bound 2)))
  (sequent Γ (L-dispersion 1)))

;; 5) Froissart–Martin bound: UnitarityCut + Dispersion + PolynomialBound ⇒ FroissartMartin
(define (sm-froissart-sequent)
  (define Γ (list (L-unitarity-cut)
                  (L-dispersion 1)
                  (L-poly-bound 2)))
  (sequent Γ (L-froissart)))

;; Pack aggregator for heavy scan
(define (smatrix-analytic-pack)
  (and (semiring-element? (sm-analyticity-sequent))
       (semiring-element? (sm-crossing-sequent))
       (semiring-element? (sm-unitarity-cut-sequent))
       (semiring-element? (sm-dispersion-sequent))
       (semiring-element? (sm-froissart-sequent))))

