#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Gap → Complexity consequences (symbolic, observer-level)

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../theorems/complexity-separation.rkt"))

(provide (all-defined-out))

(define (gap->complexity)
  (define ra (regime-assumptions-L))
  (list
   ;; Regime/lens tags (fine-grained)
   (cons 'det-nonexp (list-ref ra 0))
   (cons 'nondet-neutral (list-ref ra 1))
   (cons 'lens-soundness (list-ref ra 2))
   ;; Separation manifestations
   (cons 'P-neq-NP (pnp-separation-sequent))
   (cons 'NP-neq-coNP (npcnp-separation-sequent))))
