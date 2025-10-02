#lang racket

(require "../../api.rkt"
         "unified-library-generator.rkt")

(provide emit-lean
         emit-lean-library)

;; Main Lean library generator using unified architecture
(define (emit-lean-library output-dir)
  (displayln "🚀 Generating CLEAN v10 Lean Library with Unified Architecture...")
  (displayln "")
  (generate-lean-library-unified output-dir)
  (displayln "")
  (displayln "🔧 To compile:")
  (printf "  cd %s && lean lib/Core.lean\n" output-dir)
  (printf "  cd %s && lean lib/Observers.lean\n" output-dir)
  (printf "  cd %s && lean lib/Kernels.lean\n" output-dir)
  (printf "  cd %s && lean CLEAN.lean\n" output-dir)
  (displayln ""))

;; Legacy function for backward compatibility
(define (emit-lean)
  (emit-lean-library "lean-output"))
