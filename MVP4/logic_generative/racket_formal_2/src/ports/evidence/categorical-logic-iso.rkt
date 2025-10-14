#lang racket
; (c) 2025 AI.IMPACT GmbH

(require (file "./isomorphisms.rkt"))
(provide (all-defined-out))

(define categorical-logic-iso (evidence-iso 'categorical-logic identity-forward identity-backward))

