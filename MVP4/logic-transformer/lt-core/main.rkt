#lang typed/racket
;; Logic Transformer - MDE Pyramid Implementation
;; M3 (metametamodel) → M2 (metamodel) → M1 (model) → M0 (runtime)
;; This file orchestrates the complete MDE hierarchy
;;
;; Inverted MDE Pyramid Flow (M3→M2→M1):
;; ┌─────────────────────────────────────────────────────────────┐
;; │ M3: Metametamodel (Foundation) - MAXIMUM DETAIL           │
;; │ ├─ M3_types.rkt: Types, signatures, arity constraints    │
;; │ ├─ M3_graph.rkt: Graph structures, validation             │
;; │ └─ M3_rules.rkt: DPO rules, normalization interfaces     │
;; └─────────────────────────────────────────────────────────────┘
;;                              ↓ depends on
;; ┌─────────────────────────────────────────────────────────────┐
;; │ M2: Metamodel (Structure) - INTERMEDIATE DETAIL           │
;; │ ├─ M2_pgc.rkt: Positive guarded conditions                │
;; │ └─ M2_cert.rkt: Certificates, witnesses                   │
;; └─────────────────────────────────────────────────────────────┘
;;                              ↓ depends on
;; ┌─────────────────────────────────────────────────────────────┐
;; │ M1: Model (Single Transformer Logic) - MINIMAL DETAIL     │
;; │ └─ M1_logic.rkt: The fulcrum - single unified logic        │
;; └─────────────────────────────────────────────────────────────┘

;; M3 Layer: Metametamodel - Foundation types and signatures (MAXIMUM DETAIL)
(provide (all-from-out "M123_d/m3d.types.rkt")
         (all-from-out "M123_d/m3d.graph.rkt")
         (all-from-out "M123_d/m3d.rules.rkt"))

;; M2 Layer: Metamodel - Structure and certificates (INTERMEDIATE DETAIL)
(provide (all-from-out "M123_d/m2d.pgc.rkt")
         (all-from-out "M123_d/m2d.cert.rkt"))

;; M1 Layer: Model - Single Transformer Logic (MINIMAL DETAIL)
(provide (all-from-out "M123_d/m1d.logic.rkt"))

;; Inverted MDE Pyramid Dependencies (M3 → M2 → M1)
(require "M123_d/m3d.types.rkt"    ; M3: Foundation (MAXIMUM DETAIL)
         "M123_d/m3d.graph.rkt"    ; M3: Graph structures
         "M123_d/m3d.rules.rkt"    ; M3: DPO rules and normalization
         "M123_d/m2d.pgc.rkt"      ; M2: Positive guarded conditions (INTERMEDIATE DETAIL)
         "M123_d/m2d.cert.rkt"     ; M2: Certificates and witnesses
         "M123_d/m1d.logic.rkt")   ; M1: Single transformer logic (MINIMAL DETAIL)

;; Host bundle function for generation
(define (host-bundle)
  (define sample-tg
    (make-type-graph
     (list 'port 'input 'output)
     (list 'sigma6 'tensor 'wire)
     (list (cons 'sigma6 (Arity 3 3))
           (cons 'tensor (Arity 2 2))
           (cons 'wire (Arity 2 2)))
     (list (cons 'sigma6 (vector 'port 'port 'port))
           (cons 'tensor (vector 'port 'port))
           (cons 'wire (vector 'input 'output)))
     (list (cons 'sigma6 (vector 'port 'port 'port))
           (cons 'tensor (vector 'port 'port))
           (cons 'wire (vector 'output 'input)))))
  
  (define sample-graph
    (add-edge
     (add-node
      (mk-graph sample-tg)
      (Node 1 'port))
     (Edge 1 'sigma6 (vector 1 1 1) (vector 1 1 1))))
  
  (values sample-graph (Top) '()))

(provide host-bundle)
