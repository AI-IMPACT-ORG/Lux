#lang racket
;; QFT evidence witnesses (symbolic, port-level) with open choices

(require (file "../../foundations/abstract-core.rkt")
         (file "../../logic/internalize.rkt"))

(provide (all-defined-out))

(define (qft-evidence-witnesses #:label [label 'qft-default])
  (define LBL (make-abstract-const label 'symbol))
  (list
   (embed-proposition (abstract-op 'ReflectionPositivity (list LBL) 'meta))
   (embed-proposition (abstract-op 'UnitaryEvolution (list LBL) 'meta))
   (embed-proposition (abstract-op 'WickRotation (list LBL) 'meta))
   (embed-proposition (abstract-op 'GaugeInvariant (list LBL) 'meta))
   (embed-proposition (abstract-op 'BRSTNilpotent (list LBL) 'meta))
   (embed-proposition (abstract-op 'WardIdentity (list LBL) 'meta))
   (embed-proposition (abstract-op 'Locality (list LBL) 'meta))
   (embed-proposition (abstract-op 'Microcausality (list LBL) 'meta))
   (embed-proposition (abstract-op 'ClusterDecomposition (list LBL) 'meta))
   (embed-proposition (abstract-op 'SpectralCondition (list LBL) 'meta))
   ;; Open choices: metric signature and cosmological constant are not fixed
   (embed-proposition (abstract-op 'MetricSignatureOpen (list LBL) 'meta))
   (embed-proposition (abstract-op 'CosmologicalConstantOpen (list LBL) 'meta))))

