#lang Lux
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

(require (file "../../src/main.rkt"))

(provide prove-rice-generalization prove-rice-generalization-internal)

(define (prove-rice-generalization)
  ;; Example property tag 'has-fixed-point; any nontrivial extensional property will do
  (rice-generalization-witness 'has-fixed-point))

(define (prove-rice-generalization-internal)
  (rice-generalization-proof 'has-fixed-point))
