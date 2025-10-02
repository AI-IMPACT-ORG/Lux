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

;; Generate inductive type
(define (inductive config name constructors)
  (case (lang-config-name config)
    ['coq (format "Inductive ~a : Type :=\n| ~a." name (string-join constructors "\n| "))]
    ['agda (format "data ~a : Set where\n~a" name (string-join constructors "\n"))]
    ['lean (format "inductive ~a : Type where\n| ~a" name (string-join constructors "\n| "))]
    ['isabelle (format "datatype ~a = ~a" name (string-join constructors " | "))]))

;; Generate function body with proper syntax for each language
(define (function-body config body)
  (case (lang-config-name config)
    ['coq body]
    ['agda body]
    ['lean body]
    ['isabelle body]))

;; Generate function definition
(define (function config name type body)
  (case (lang-config-name config)
    ['coq (format "Definition ~a : ~a :=\n  ~a." name type body)]
    ['agda (format "~a : ~a\n~a = ~a" name type name body)]
    ['lean (format "def ~a : ~a :=\n  ~a" name type body)]
    ['isabelle (format "definition ~a :: \"~a\" where \"~a = ~a\"" name type name body)]))

;; Generate axiom
(define (axiom config name statement)
  (case (lang-config-name config)
    ['coq (format "Axiom ~a : ~a." name statement)]
    ['agda (format "postulate ~a : ~a" name statement)]
    ['lean (format "axiom ~a : ~a" name statement)]
    ['isabelle (format "axiomatization ~a where \"~a\"" name statement)]))

;; ============================================================================
;; MODULE GENERATORS
;; ============================================================================

;; Generate core module
(define (generate-core config sig)
  (define sorts (signature-sorts sig))
  (define operations (signature-operations sig))
  (define constants (signature-constants sig))
  
  ;; Generate constructors
  (define sort-constructors (case (lang-config-name config)
    ['lean (map (λ (s) (format "~a" s)) sorts)]
    [else (map (λ (s) (format "  ~a : Sort" s)) sorts)]))
  (define op-constructors (case (lang-config-name config)
    ['lean (map (λ (op) (format "~a" (clean-name (car op)))) operations)]
    [else (map (λ (op) (format "  ~a : Operation" (clean-name (car op)))) operations)]))
  (define const-constructors (case (lang-config-name config)
    ['lean (map (λ (c) (format "~a" (clean-name (car c)))) constants)]
    [else (map (λ (c) (format "  ~a : Constant" (clean-name (car c)))) constants)]))
  
  ;; Generate term constructors
  (define arrow (lang-config-arrow config))
  (define term-constructors (case (lang-config-name config)
    ['lean (append
      (map (λ (s) (format "Const~a" s)) sorts)
      (map (λ (op) (format "~a" (clean-name (car op)))) operations))]
    [else (append
      (map (λ (s) (format "  Const~a : Term" s)) sorts)
      (map (λ (op) (format "  ~a : Term ~a Term ~a Term" (clean-name (car op)) arrow arrow)) operations))]))
  
  (string-join
   (list
    ((lang-config-module-header-generator config) "Core" (case (lang-config-name config)
      ['coq '("Arith.Arith" "Arith.PeanoNat")]
      ['agda '("Agda.Builtin.Nat" "Agda.Builtin.String" "Agda.Builtin.Equality")]
      ['lean '()]
      ['isabelle '("Main")]))
    (comment config "CLEAN v10 Core - Expanded with Logical Structure")
    ""
    (case (lang-config-name config)
      ['lean (inductive config "CleanSort" sort-constructors)]
      [else (inductive config "Sort" sort-constructors)])
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
    (function config "reflect_L" (format "Term ~a Term" arrow) 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "reflect_R" (format "Term ~a Term" arrow)
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "observer_value" (format "Term ~a Term" arrow)
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    "")
   "\n"))

;; Generate observers module
(define (generate-observers config)
  (define imports (case (lang-config-name config)
    ['agda '("lib.generated-Core")]
    ['coq '("lib.generated_Core")]
    ['lean '()]
    [else '("generated-Core")]))
  
  (string-join
   (list
    ((lang-config-module-header-generator config) "Observers" imports)
    (comment config "CLEAN v10 Observers - Expanded with Logical Functions")
    ""
    ;; Basic observer functions (simplified to avoid cycles)
    (function config "project_L" (format "Term ~a Term" (lang-config-arrow config)) 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "project_R" (format "Term ~a Term" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "reconstitute" (format "Term ~a Term" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "residual" (format "Term ~a Term" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "triality_sum" (format "Term ~a Term ~a Term ~a Term" (lang-config-arrow config) (lang-config-arrow config) (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun l b r => l" "λ l b r → l"))
    "")
   "\n"))

;; Generate kernels module
(define (generate-kernels config)
  (define imports (case (lang-config-name config)
    ['agda '("lib.generated-Core")]
    ['coq '("lib.generated_Core")]
    ['lean '()]
    [else '("generated-Core")]))
  
  (string-join
   (list
    ((lang-config-module-header-generator config) "Kernels" imports)
    (comment config "CLEAN v10 Kernels - Expanded with Logical Operations")
    ""
    ;; Define Kernel type locally to avoid external dependencies
    (case (lang-config-name config)
      ['lean (inductive config "Kernel" (list "KernelId"))]
      [else ""])
    ""
    ;; Kernel operations
    (function config "kernel_header_add" (format "Header ~a Header ~a Header" (lang-config-arrow config) (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun h1 h2 => h1" "λ h1 h2 → h1"))
    ""
    (function config "kernel_header_product" (format "Header ~a Header ~a Header" (lang-config-arrow config) (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun h1 h2 => h1" "λ h1 h2 → h1"))
    ""
    (function config "kernel_header_zero" (format "Header ~a Header" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun k => k" "λ k → k"))
    ""
    (function config "identity_kernel" (format "Kernel ~a Kernel" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "KernelId" 
          (if (eq? (lang-config-name config) 'lean) "Kernel.KernelId" "KernelId")))
    "")
   "\n"))

;; Generate normal forms module
(define (generate-normal-forms config)
  (define imports (case (lang-config-name config)
    ['agda '("lib.generated-Core" "Agda.Builtin.Bool")]
    ['coq '("lib.generated_Core")]
    ['lean '()]
    [else '("generated-Core")]))
  
  (string-join
   (list
    ((lang-config-module-header-generator config) "NormalForms" imports)
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
    (function config "normal_form" (format "Term ~a NormalForm" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun t => NormalForm.nf_core t" "λ t → NormalForm.nf_core t"))
    ""
    (function config "nf_phase" (format "NormalForm ~a Header" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun nf => nf" "λ nf → nf"))
    ""
    (function config "nf_scale" (format "NormalForm ~a Header" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun nf => nf" "λ nf → nf"))
    ""
    (function config "nf_core" (format "NormalForm ~a Term" (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun nf => nf" "λ nf → nf"))
    ""
    (function config "normalize_terms" (format "Term ~a Term ~a NormalForm" (lang-config-arrow config) (lang-config-arrow config))
      (if (eq? (lang-config-name config) 'coq) "fun t1 t2 => NormalForm.nf_core t1" "λ t1 t2 → NormalForm.nf_core t1"))
    "")
   "\n"))

;; Generate main library
(define (generate-main config)
  (string-join
   (list
    (case (lang-config-name config)
      ['coq (string-join (list
        "Require Import lib.generated_Core."
        "Require Import lib.generated_Observers."
        "Require Import lib.generated_Kernels."
        "Require Import lib.generated_NormalForms."
        "")
        "\n")]
      ['agda (string-join (list
        "module CLEAN where"
        ""
        "open import lib.generated_Core"
        "open import lib.generated_Observers"
        "open import lib.generated_Kernels"
        "open import lib.generated_NormalForms"
        "")
        "\n")]
      ['lean (string-join (list
        "")
        "\n")]
      ['isabelle (string-join (list
        "theory CLEAN"
        "imports Main"
        "begin"
        ""
        "datatype Sort = L | B | R | I"
        "datatype Term = ConstL | ConstB | ConstR | ConstI | PlusB Term Term | MultB Term Term"
        ""
        "definition CLEAN_Sort :: \"Sort\" where \"CLEAN_Sort = L\""
        "definition CLEAN_Term :: \"Term\" where \"CLEAN_Term = ConstB\""
        "definition CLEAN_PlusB :: \"Term => Term => Term\" where \"CLEAN_PlusB = PlusB\""
        "")
        "\n")])
    (comment config "CLEAN v10 Main Library - Unified Interface")
    ""
    ;; Main definitions
    (case (lang-config-name config)
      ['lean (string-join (list
        "inductive CleanSort : Type where | L | B | R | I"
        "inductive Term : Type where | ConstL | ConstB | ConstR | ConstI | PlusB Term Term | MultB Term Term"
        ""
        "def CLEAN_Sort : Type := CleanSort"
        "def CLEAN_Term : Type := Term"
        "def CLEAN_PlusB : Term → Term → Term := Term.PlusB"
        "") "\n")]
      ['isabelle ""]
      [else (string-join (list
        (function config "CLEAN_Sort" "Type" "Sort")
        (function config "CLEAN_Term" "Type" "Term")
        (function config "CLEAN_PlusB" (format "Term ~a Term ~a Term" (lang-config-arrow config) (lang-config-arrow config)) "PlusB")
        "") "\n")])
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

;; Create language-specific project files
(define (create-project-files config output-dir prefix ext)
  (case (lang-config-name config)
    ['coq (create-coq-project output-dir prefix ext)]
    ['isabelle (create-isabelle-root output-dir prefix ext)]
    [else (void)]))

;; Create Coq project file
(define (create-coq-project output-dir prefix ext)
  (define coq-project-content
    (string-join
     (list
      "-Q lib lib"
      (format "lib/~aCore~a" prefix ext)
      (format "lib/~aObservers~a" prefix ext)
      (format "lib/~aKernels~a" prefix ext)
      (format "lib/~aNormalForms~a" prefix ext)
      (format "~aCLEAN~a" prefix ext))
     "\n"))
  (display-to-file coq-project-content (build-path output-dir "_CoqProject") #:exists 'replace))

;; Create Isabelle ROOT file
(define (create-isabelle-root output-dir prefix ext)
  (define root-content
    (string-join
     (list
      "session CLEAN = HOL +"
      "  theories"
      (format "    \"~aCLEAN\"" prefix))
     "\n"))
  (display-to-file root-content (build-path output-dir "ROOT") #:exists 'replace))
