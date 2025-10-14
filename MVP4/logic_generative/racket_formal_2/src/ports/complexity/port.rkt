#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Complexity port (modular wrapper) built on central lens scaffolding

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../logic/lens-framework.rkt")
         (file "../../theorems/complexity-separation.rkt"))

(provide (all-defined-out))

;; Port evaluator: report key lens + separation booleans
(define (complexity-port-evaluator _)
  (list (semiring-element? (lens-lipschitz-sequent 'Rdet (make-abstract-const 9/10 'real) 'B))
        (semiring-element? (lens-neutrality-sequent 'Rnd))
        (verify-pnp-separations)))

