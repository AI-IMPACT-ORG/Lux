#lang typed/racket
(require "m3d.graph.rkt" "m3d.types.rkt")
(provide Cert make-cert cert->submono
         cert-well-formed?)

(struct Cert ([node-map : (Setof NodeId)]
              [edge-map : (Setof EdgeId)]) #:transparent)

(: make-cert (-> (Setof NodeId) (Setof EdgeId) Cert))
(define (make-cert ns es) (Cert ns es))

(: cert->submono (-> Cert Submono))
(define (cert->submono c) (Submono (Cert-node-map c) (Cert-edge-map c)))

(: cert-well-formed? (-> TGraph TGraph Cert Boolean))
(define (cert-well-formed? X G c)
  ;; Simplified implementation for now
  #t)
