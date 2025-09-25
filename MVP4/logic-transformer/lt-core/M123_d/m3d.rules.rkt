#lang typed/racket
(require "m3d.graph.rkt")
(provide Rule Match Normalizer
         Rule-name Rule-L Rule-K Rule-R
         Match-host Match-rule Match-mL
         make-rule find-matches apply-match normal-form)

(struct Rule ([name : Symbol]
              [L : TGraph] [K : TGraph] [R : TGraph]) #:transparent)
(struct Match ([host : TGraph] [rule : Rule] [mL : Submono]) #:transparent)

;; interfaces only — implementations can be stubs for now
(: make-rule (-> Symbol TGraph TGraph TGraph Rule))
(define (make-rule n L K R) (Rule n L K R))
(: find-matches (-> Rule TGraph (Listof Match)))
(define (find-matches r G) '())
(: apply-match (-> Match TGraph TGraph))
(define (apply-match m G) G)

;; normalizer as a list of rules (no algorithm enforced here)
(define-type Normalizer (Listof Rule))
(: normal-form (-> Normalizer TGraph TGraph))
(define (normal-form R* G) G)
