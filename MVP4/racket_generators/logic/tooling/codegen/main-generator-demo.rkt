#lang racket

(require "unified-library-generator.rkt"
         "agda.rkt"
         "coq.rkt"
         "lean.rkt"
         "isabelle.rkt")

(provide (all-defined-out))

;; ============================================================================
;; MAIN GENERATOR SCRIPT - DEMONSTRATING UNIFIED ARCHITECTURE
;; ============================================================================

;; Generate all libraries using the unified architecture
(define (generate-all-libraries-demo)
  (displayln "🚀 CLEAN v10 Library Generator - Unified Architecture Demo")
  (displayln "========================================================")
  (displayln "")
  
  (displayln "This demo showcases the unified architecture that generates")
  (displayln "consistent libraries across Coq, Agda, Lean, and Isabelle from the")
  (displayln "same CLEAN v10 signature.")
  (displayln "")
  
  ;; Generate using unified architecture
  (displayln "📚 Generating libraries with unified architecture...")
  (generate-all-libraries-unified "demo-unified-output")
  
  (displayln "")
  (displayln "📚 Generating libraries with individual generators...")
  
  ;; Generate using individual generators
  (emit-coq-library "demo-coq-output")
  (emit-agda-library "demo-agda-output")
  (emit-lean-library "demo-lean-output")
  (emit-isabelle-library "demo-isabelle-output")
  
  (displayln "")
  (displayln "✅ Demo completed! Check the output directories:")
  (displayln "  - demo-unified-output/coq-unified/")
  (displayln "  - demo-unified-output/agda-unified/")
  (displayln "  - demo-unified-output/lean-unified/")
  (displayln "  - demo-unified-output/isabelle-unified/")
  (displayln "  - demo-coq-output/")
  (displayln "  - demo-agda-output/")
  (displayln "  - demo-lean-output/")
  (displayln "  - demo-isabelle-output/")
  (displayln "")
  (displayln "🎯 Architecture Benefits:")
  (displayln "  • Consistent structure across all target languages")
  (displayln "  • Single source of truth for CLEAN v10 signature")
  (displayln "  • Easy to extend to new formal verification languages")
  (displayln "  • Maintainable and reusable code generation logic")
  (displayln "  • Language-specific optimizations where needed"))

;; Generate a specific language library
(define (generate-language-library target-language output-dir)
  (case target-language
    ['coq (emit-coq-library output-dir)]
    ['agda (emit-agda-library output-dir)]
    ['lean (emit-lean-library output-dir)]
    ['isabelle (emit-isabelle-library output-dir)]
    [else (error (format "Unsupported target language: ~a" target-language))]))

;; Compare generated libraries
(define (compare-generated-libraries)
  (displayln "🔍 Comparing Generated Libraries")
  (displayln "=================================")
  (displayln "")
  
  (displayln "Coq Library Structure:")
  (displayln "  - lib/Core.v: Sorts, Operations, Constants, Terms, Axioms")
  (displayln "  - lib/Observers.v: Observer functions (project_L, inject_L, etc.)")
  (displayln "  - lib/Kernels.v: Kernel functions (compose, apply, identity)")
  (displayln "  - CLEAN.v: Main library with convenience definitions")
  (displayln "")
  
  (displayln "Agda Library Structure:")
  (displayln "  - lib/Core.agda: Sorts, Operations, Constants, Terms, Axioms")
  (displayln "  - lib/Observers.agda: Observer functions (project-L, inject-L, etc.)")
  (displayln "  - lib/Kernels.agda: Kernel functions (compose, apply, identity)")
  (displayln "  - CLEAN.agda: Main library with convenience definitions")
  (displayln "")
  
  (displayln "Lean Library Structure:")
  (displayln "  - lib/Core.lean: Sorts, Operations, Constants, Terms, Axioms")
  (displayln "  - lib/Observers.lean: Observer functions (project_L, inject_L, etc.)")
  (displayln "  - lib/Kernels.lean: Kernel functions (compose, apply, identity)")
  (displayln "  - CLEAN.lean: Main library with convenience definitions")
  (displayln "")
  
  (displayln "Isabelle Library Structure:")
  (displayln "  - lib/Core.thy: Sorts, Operations, Constants, Terms, Axioms")
  (displayln "  - lib/Observers.thy: Observer functions (project_L, inject_L, etc.)")
  (displayln "  - lib/Kernels.thy: Kernel functions (compose, apply, identity)")
  (displayln "  - CLEAN.thy: Main library with convenience definitions")
  (displayln "")
  
  (displayln "🎯 Key Architectural Features:")
  (displayln "  • Unified module structure across all languages")
  (displayln "  • Language-specific syntax adaptation")
  (displayln "  • Consistent naming conventions")
  (displayln "  • Comprehensive axiom sets")
  (displayln "  • Type-safe term constructors")
  (displayln "  • Observer pattern implementation")
  (displayln "  • Kernel composition system"))

;; Main execution
(module+ main
  (generate-all-libraries-demo)
  (displayln "")
  (compare-generated-libraries))
