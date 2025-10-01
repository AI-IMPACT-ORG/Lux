#lang racket

(require "../../api.rkt"
         racket/format
         racket/file
         racket/path
         "coq-dependent-generator.rkt")

(provide emit-coq
         emit-coq-library)

;; Main Coq library generator using sophisticated dependent types
(define (emit-coq-library output-dir)
  (displayln "🚀 Generating CLEAN v10 Coq Library with Complex Dependent Types...")
  (displayln "")
  (emit-coq-dependent-generator-main output-dir)
  (displayln "")
  (displayln "🔧 To compile:")
  (printf "  cd %s && coqc lib/Core.v\n" output-dir)
  (printf "  cd %s && coqc lib/Observers.v\n" output-dir)
  (printf "  cd %s && coqc lib/Kernels.v\n" output-dir)
  (printf "  cd %s && coqc api/CLEAN.v\n" output-dir)
  (displayln ""))

;; Legacy function for backward compatibility
(define (emit-coq)
  (emit-coq-library "output"))