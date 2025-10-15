#lang racket

(require "../export/generator.rkt")

;; Generate all formalizations
(define base-path "/Users/rutgerboels/BootstrapPaper/MVP4/formal")

(printf "Generating formalizations in ~a~n" base-path)
(generate-all-formalizations base-path)
(printf "Generation complete!~n")
