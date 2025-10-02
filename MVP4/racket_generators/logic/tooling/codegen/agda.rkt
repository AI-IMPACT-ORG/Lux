#lang racket

(require "../../api.rkt"
         "unified-library-generator.rkt")

(provide emit-agda
         emit-agda-library)

;; Main Agda library generator using unified architecture
(define (emit-agda-library output-dir)
  (displayln "🚀 Generating CLEAN v10 Agda Library with Unified Architecture...")
  (displayln "")
  (generate-agda-library-unified output-dir)
  (displayln "")
  (displayln "🔧 To compile:")
  (printf "  cd %s && agda lib/Core.agda\n" output-dir)
  (printf "  cd %s && agda lib/Observers.agda\n" output-dir)
  (printf "  cd %s && agda lib/Kernels.agda\n" output-dir)
  (printf "  cd %s && agda CLEAN.agda\n" output-dir)
  (displayln ""))

;; Legacy function for backward compatibility
(define (emit-agda)
  (emit-agda-library "agda-output"))
