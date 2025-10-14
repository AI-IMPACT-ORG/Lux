#lang racket

(require (file "./isomorphisms.rkt"))
(provide (all-defined-out))

(define categorical-logic-iso (evidence-iso 'categorical-logic identity-forward identity-backward))

