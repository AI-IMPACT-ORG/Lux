#lang racket

;; @logic/gen Language Reader
;; Provides the #lang logic/gen reader that loads surface forms

(require "surface.rkt")

(provide (all-from-out "surface.rkt"))

;; Re-export everything from surface forms
(provide (all-defined-out))

