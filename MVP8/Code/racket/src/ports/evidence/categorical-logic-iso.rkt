#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

(require (file "./isomorphisms.rkt"))
(provide (all-defined-out))

(define categorical-logic-iso (evidence-iso 'categorical-logic identity-forward identity-backward))

