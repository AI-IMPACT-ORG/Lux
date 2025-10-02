#lang racket

(require "../../api.rkt"
         "unified-library-generator.rkt")

(provide emit-isabelle
         emit-isabelle-library)

;; Main Isabelle library generator using unified architecture
(define (emit-isabelle-library output-dir)
  (displayln "🚀 Generating CLEAN v10 Isabelle Library with Unified Architecture...")
  (displayln "")
  (generate-isabelle-library-unified output-dir)
  (displayln "")
  (displayln "🔧 To compile:")
  (printf "  cd %s && isabelle build -D .\n" output-dir)
  (printf "  cd %s && isabelle jedit lib/Core.thy\n" output-dir)
  (printf "  cd %s && isabelle jedit lib/Observers.thy\n" output-dir)
  (printf "  cd %s && isabelle jedit lib/Kernels.thy\n" output-dir)
  (printf "  cd %s && isabelle jedit CLEAN.thy\n" output-dir)
  (displayln ""))

;; Legacy function for backward compatibility
(define (emit-isabelle)
  (emit-isabelle-library "isabelle-output"))
