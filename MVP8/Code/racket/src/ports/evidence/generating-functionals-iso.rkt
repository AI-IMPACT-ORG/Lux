#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

(require (file "./isomorphisms.rkt"))
(provide (all-defined-out))

;; For now, the generating-functionals isomorphism is the identity
;; (pure relabelling). Later, attach labels/metadata if needed.

(define gf-iso (evidence-iso 'generating-functionals identity-forward identity-backward))

