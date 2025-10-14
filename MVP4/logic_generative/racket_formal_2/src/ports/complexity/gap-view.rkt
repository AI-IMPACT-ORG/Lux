#lang racket
;; Gap → Complexity consequences (symbolic, observer-level)

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../theorems/complexity-separation.rkt"))

(provide (all-defined-out))

(define (gap->complexity)
  (list
   (cons 'P-neq-NP (pnp-separation-sequent))
   (cons 'NP-neq-coNP (npcnp-separation-sequent))))

