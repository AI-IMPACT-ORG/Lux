#lang racket

(require "../../api.rkt"
         racket/format
         racket/file
         racket/path
         "coq-dependent-generator.rkt"
         "unified-library-generator.rkt")

(provide emit-coq
         emit-coq-library)

;; Main Coq library generator using unified architecture
(define (emit-coq-library output-dir)
  (displayln "🚀 Generating CLEAN v10 Coq Library with Unified Architecture...")
  (displayln "")
  (generate-coq-library-unified output-dir)
  (displayln "")
  (displayln "🔧 To compile:")
  (printf "  cd %s && coqc lib/Core.v\n" output-dir)
  (printf "  cd %s && coqc lib/Observers.v\n" output-dir)
  (printf "  cd %s && coqc lib/Kernels.v\n" output-dir)
  (printf "  cd %s && coqc CLEAN.v\n" output-dir)
  (displayln ""))

;; Legacy function for backward compatibility
(define (emit-coq)
  (emit-coq-library "coq-output"))