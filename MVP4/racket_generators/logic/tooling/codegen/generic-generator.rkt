#lang racket

(require "../../api.rkt"
         "language-configs.rkt"
         racket/format
         racket/file
         racket/path
         racket/string)

(provide (all-defined-out))

;; ============================================================================
;; GENERIC GENERATOR CORE
;; ============================================================================

;; Generate comment
(define (comment config text)
  (format (lang-config-comment config) text))

;; Generate inductive type using language-specific generator
(define (inductive config name constructors)
  ((lang-config-inductive-generator config) name constructors))

;; Generate function body with proper syntax for each language
(define (function-body config body)
  body) ; Function body is now handled by the function generator

;; Generate function definition using language-specific generator
(define (function config name type body)
  ((lang-config-function-generator config) name type body))

;; Generate axiom using language-specific generator
(define (axiom config name statement)
  ((lang-config-axiom-generator config) name statement))

;; ============================================================================
;; MODULE GENERATORS
;; ============================================================================

;; Generate core module
(define (generate-core config sig)
  (define sorts (signature-sorts sig))
  (define operations (signature-operations sig))
  (define constants (signature-constants sig))
  
  ;; Generate constructors using language-specific formatters
  (define sort-constructors ((lang-config-sort-constructor-format config) sorts))
  (define op-constructors ((lang-config-op-constructor-format config) operations))
  (define const-constructors ((lang-config-const-constructor-format config) constants))
  
  ;; Generate term constructors using language-specific formatter
  (define term-constructors ((lang-config-term-constructor-format config) sorts operations))
  
  (string-join
   (list
    ((lang-config-module-header-generator config) "Core" ((lang-config-get-core-imports config)))
    (comment config "CLEAN v10 Core - Expanded with Logical Structure")
    ""
    (inductive config (lang-config-sort-name config) sort-constructors)
    ""
    (inductive config "Operation" op-constructors)
    ""
    (inductive config "Constant" const-constructors)
    ""
    (inductive config "Term" term-constructors)
    ""
    ;; Additional logical structure
    (case (lang-config-name config)
      ['lean (string-join (list
        (inductive config "Header" (list "header_zero" "header_add Header Header" "header_multiply Header Header"))
        (inductive config "NormalForm" (list "nf_phase Header" "nf_scale Header" "nf_core Term"))
        "") "\n")]
      [else ""])
    ;; Observer functions (simplified to avoid cycles)
    (function config "reflect_L" (format "Term ~a Term" (lang-config-arrow config)) 
      (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
    ""
    (function config "reflect_R" (format "Term ~a Term" (lang-config-arrow config))
      (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
    ""
    (function config "observer_value" (format "Term ~a Term" (lang-config-arrow config))
      (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
    "")
   "\n"))

;; Generate observers module
(define (generate-observers config)
  (string-join
   (list
    ((lang-config-module-header-generator config) "Observers" ((lang-config-get-observers-imports config)))
    (comment config "CLEAN v10 Observers - Expanded with Logical Functions")
    ""
    ;; Basic observer functions (simplified to avoid cycles)
    (function config "project_L" (format "Term ~a Term" (lang-config-arrow config)) 
      (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
    ""
    (function config "project_R" (format "Term ~a Term" (lang-config-arrow config))
      (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
    ""
    (function config "reconstitute" (format "Term ~a Term" (lang-config-arrow config))
      (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
    ""
    (function config "residual" (format "Term ~a Term" (lang-config-arrow config))
      (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
    ""
    (function config "triality_sum" (format "Term ~a Term ~a Term ~a Term" (lang-config-arrow config) (lang-config-arrow config) (lang-config-arrow config))
      (format "~a l b r ~a l" (lang-config-lambda config) (lang-config-arrow config)))
    "")
   "\n"))

;; Generate kernels module
(define (generate-kernels config)
  (string-join
   (list
    ((lang-config-module-header-generator config) "Kernels" ((lang-config-get-kernels-imports config)))
    (comment config "CLEAN v10 Kernels - Expanded with Logical Operations")
    ""
    ;; Define Kernel type locally to avoid external dependencies
    (case (lang-config-name config)
      ['lean (inductive config "Kernel" (list "KernelId"))]
      [else ""])
    ""
    ;; Kernel operations
    (case (lang-config-name config)
      ['lean (string-join (list
        (function config "kernel_header_add" (format "Header ~a Header ~a Header" (lang-config-arrow config) (lang-config-arrow config))
          (format "~a h1 h2 ~a h1" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "kernel_header_product" (format "Header ~a Header ~a Header" (lang-config-arrow config) (lang-config-arrow config))
          (format "~a h1 h2 ~a h1" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "kernel_header_zero" (format "Header ~a Header" (lang-config-arrow config))
          (format "~a k ~a k" (lang-config-lambda config) (lang-config-arrow config)))
        "") "\n")]
      [else (string-join (list
        (function config "kernel_header_add" (format "Term ~a Term ~a Term" (lang-config-arrow config) (lang-config-arrow config))
          (format "~a h1 h2 ~a h1" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "kernel_header_product" (format "Term ~a Term ~a Term" (lang-config-arrow config) (lang-config-arrow config))
          (format "~a h1 h2 ~a h1" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "kernel_header_zero" (format "Term ~a Term" (lang-config-arrow config))
          (format "~a k ~a k" (lang-config-lambda config) (lang-config-arrow config)))
        "") "\n")])
    ""
    (function config "identity_kernel" (format "Term ~a Term" (lang-config-arrow config))
      (format "~a k ~a k" (lang-config-lambda config) (lang-config-arrow config)))
    "")
   "\n"))

;; Generate normal forms module
(define (generate-normal-forms config)
  (string-join
   (list
    ((lang-config-module-header-generator config) "NormalForms" ((lang-config-get-normal-forms-imports config)))
    (comment config "CLEAN v10 Normal Forms - Logical Structure")
    ""
    ;; Define types locally to avoid external dependencies
    (case (lang-config-name config)
      ['lean (string-join (list
        (inductive config "Term" (list "ConstB"))
        (inductive config "Header" (list "header_zero" "header_add Header Header" "header_multiply Header Header"))
        (inductive config "NormalForm" (list "nf_phase Header" "nf_scale Header" "nf_core Term"))
        "") "\n")]
      [else ""])
    ""
    ;; Normal form operations
    (case (lang-config-name config)
      ['lean (string-join (list
        (function config "normal_form" (format "Term ~a NormalForm" (lang-config-arrow config))
          (format "~a t ~a NormalForm.nf_core t" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "nf_phase" (format "NormalForm ~a Header" (lang-config-arrow config))
          (format "~a nf ~a nf" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "nf_scale" (format "NormalForm ~a Header" (lang-config-arrow config))
          (format "~a nf ~a nf" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "nf_core" (format "NormalForm ~a Term" (lang-config-arrow config))
          (format "~a nf ~a nf" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "normalize_terms" (format "Term ~a Term ~a NormalForm" (lang-config-arrow config) (lang-config-arrow config))
          (format "~a t1 t2 ~a NormalForm.nf_core t1" (lang-config-lambda config) (lang-config-arrow config)))
        "") "\n")]
      [else (string-join (list
        (function config "normal_form" (format "Term ~a Term" (lang-config-arrow config))
          (format "~a t ~a t" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "nf_phase" (format "Term ~a Term" (lang-config-arrow config))
          (format "~a nf ~a nf" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "nf_scale" (format "Term ~a Term" (lang-config-arrow config))
          (format "~a nf ~a nf" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "nf_core" (format "Term ~a Term" (lang-config-arrow config))
          (format "~a nf ~a nf" (lang-config-lambda config) (lang-config-arrow config)))
        ""
        (function config "normalize_terms" (format "Term ~a Term ~a Term" (lang-config-arrow config) (lang-config-arrow config))
          (format "~a t1 t2 ~a t1" (lang-config-lambda config) (lang-config-arrow config)))
        "") "\n")])
    "")
   "\n"))

;; Generate main library using language-specific generator
(define (generate-main config)
  (string-join
   (list
    ((lang-config-main-module-generator config) ((lang-config-get-main-imports config)))
    (comment config "CLEAN v10 Main Library - Unified Interface")
    "")
   "\n"))

;; ============================================================================
;; MAIN GENERATION FUNCTION
;; ============================================================================

;; Generate library for a specific language
(define (generate-library config output-dir verbose?)
  (define sig (current-signature))
  
  ;; Generate modules
  (define core-content (generate-core config sig))
  (define observers-content (generate-observers config))
  (define kernels-content (generate-kernels config))
  (define normal-forms-content (generate-normal-forms config))
  (define main-content (generate-main config))
  
  ;; Write files with language-specific prefix
  (define ext (lang-config-ext config))
  (define prefix (lang-config-file-prefix config))
  (make-directory* (build-path output-dir "lib"))
  
  (display-to-file core-content (build-path output-dir "lib" (string-append prefix "Core" ext)) #:exists 'replace)
  (display-to-file observers-content (build-path output-dir "lib" (string-append prefix "Observers" ext)) #:exists 'replace)
  (display-to-file kernels-content (build-path output-dir "lib" (string-append prefix "Kernels" ext)) #:exists 'replace)
  (display-to-file normal-forms-content (build-path output-dir "lib" (string-append prefix "NormalForms" ext)) #:exists 'replace)
  (display-to-file main-content (build-path output-dir (string-append prefix "CLEAN" ext)) #:exists 'replace)
  
  ;; Create language-specific project files
  (create-project-files config output-dir prefix ext)
  
  (when verbose?
    (displayln (format "📁 Generated files:"))
    (displayln (format "  - lib/~aCore~a" prefix ext))
    (displayln (format "  - lib/~aObservers~a" prefix ext))
    (displayln (format "  - lib/~aKernels~a" prefix ext))
    (displayln (format "  - lib/~aNormalForms~a" prefix ext))
    (displayln (format "  - ~aCLEAN~a" prefix ext))))

;; Create language-specific project files using configuration
(define (create-project-files config output-dir prefix ext)
  ((lang-config-deployment-function config) output-dir prefix ext))

;; ============================================================================
;; COMPATIBILITY FUNCTIONS
;; ============================================================================

;; Convenience functions for backward compatibility
(define (generate-coq-library-unified output-dir) 
  (generate-library (get-language-config 'coq) output-dir #f))

(define (generate-agda-library-unified output-dir) 
  (generate-library (get-language-config 'agda) output-dir #f))

(define (generate-lean-library-unified output-dir) 
  (generate-library (get-language-config 'lean) output-dir #f))

(define (generate-isabelle-library-unified output-dir) 
  (generate-library (get-language-config 'isabelle) output-dir #f))

(define (generate-all-libraries-unified base-output-dir)
  (displayln "🚀 Generating CLEAN v10 Libraries for All Languages (Simplified)...")
  (generate-coq-library-unified (build-path base-output-dir "coq"))
  (generate-agda-library-unified (build-path base-output-dir "agda"))
  (generate-lean-library-unified (build-path base-output-dir "lean"))
  (generate-isabelle-library-unified (build-path base-output-dir "isabelle"))
  (displayln "✅ All CLEAN v10 libraries generated successfully!"))
