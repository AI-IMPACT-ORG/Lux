#lang racket
; (c) 2025 AI.IMPACT GmbH

(require (file "./isomorphisms.rkt"))
(provide (all-defined-out))

;; For now, the generating-functionals isomorphism is the identity
;; (pure relabelling). Later, attach labels/metadata if needed.

(define gf-iso (evidence-iso 'generating-functionals identity-forward identity-backward))

