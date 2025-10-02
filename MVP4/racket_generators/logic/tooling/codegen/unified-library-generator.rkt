#lang racket

(require "../../api.rkt"
         racket/format
         racket/file
         racket/path
         racket/string)

(provide (all-defined-out))

;; ============================================================================
;; SIMPLIFIED UNIFIED LIBRARY GENERATOR
;; ============================================================================

;; Simple language configuration
(define-struct lang-config (name ext arrow lambda comment))

;; Language configurations
(define coq-config (lang-config 'coq ".v" "->" "fun" "(* ~a *)"))
(define agda-config (lang-config 'agda ".agda" "→" "λ" "-- ~a"))
(define lean-config (lang-config 'lean ".lean" "→" "λ" "-- ~a"))
(define isabelle-config (lang-config 'isabelle ".thy" "⇒" "λ" "(* ~a *)"))

;; Clean identifiers using simple mapping
(define (clean-name name)
  (define name-str (symbol->string name))
  (define cleaned (string-replace (string-replace (string-replace (string-replace name-str "⊕" "Plus") "⊗" "Mult") "ι" "Inject") "ν" "Project"))
  
  ;; Simple semantic mapping
  (case cleaned
    [("0_B") "ZeroB"] [("1_B") "OneB"] 
    [("0_L") "ZeroL"] [("1_L") "OneL"]
    [("0_R") "ZeroR"] [("1_R") "OneR"]
    [("ad_0") "Ad0"] [("ad_1") "Ad1"] [("ad_2") "Ad2"] [("ad_3") "Ad3"]
    [("φ") "Phi"] [("barφ") "BarPhi"] [("z") "Z"] [("barz") "BarZ"] [("Λ") "Lambda"]
    [else cleaned]))

;; Clean identifiers for constructors (replace hyphens with underscores)
(define (clean-constructor-name name)
  (string-replace (clean-name (string->symbol name)) "-" "_"))

;; Generate module header
(define (module-header config name imports)
  (case (lang-config-name config)
    ['coq (if (empty? imports) 
              "" 
              (format "Require Import ~a.\n\n" (string-join imports ".\nRequire Import ")))]
    ['agda (format "module lib.~a where\n~a\n" name (string-join (map (λ (imp) (format "open import ~a" imp)) imports) "\n"))]
    ['lean (if (empty? imports) 
              (format "namespace ~a\n\n" name)
              (format "import ~a\n\nnamespace ~a\n\n" (string-join imports " ") name))]
    ['isabelle (format "theory ~a\nimports ~a\nbegin\n\n" name (string-join imports " "))]))

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
    ['lean (string-replace body "→" "=>")]
    ['isabelle body]))

;; Generate function
(define (function config name type body)
  (define clean-type (string-replace type "→" (lang-config-arrow config)))
  (define coq-type (if (eq? (lang-config-name config) 'coq) 
                       (string-replace clean-type "Bool" "bool")
                       clean-type))
  (define lean-body (function-body config body))
  (case (lang-config-name config)
    ['coq (format "Definition ~a : ~a :=\n  ~a." name coq-type body)]
    ['agda (format "~a : ~a\n~a = ~a" name type name body)]
    ['lean (format "def ~a : ~a := ~a" name clean-type lean-body)]
    ['isabelle (format "definition ~a :: \"~a\" where\n  \"~a ≡ ~a\"" name clean-type name body)]))

;; Generate core module with expanded functionality
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
      (map (λ (op) 
        (define name (clean-name (car op)))
        (define is-unary (or (string-contains? name "Inject") (string-contains? name "Project")))
        (if is-unary
            (format "Term~a : Term → Term" name)
            (format "Term~a : Term → Term → Term" name)))
        operations))]
    [else (append
      (map (λ (s) (format "  Const~a : Constant ~a Term" s arrow)) sorts)
      (map (λ (op) 
        (define name (clean-name (car op)))
        (define is-unary (or (string-contains? name "Inject") (string-contains? name "Project")))
        (define term-name (if (eq? (lang-config-name config) 'coq) (string-append "Term" name) name))
        (if is-unary
            (format "  ~a : Term ~a Term" term-name arrow)
            (format "  ~a : Term ~a Term ~a Term" term-name arrow arrow)))
        operations))]))
  
  ;; Generate kernel constructor
  (define kernel-constructor (case (lang-config-name config)
    ['lean "KernelId"]
    [else (format "  KernelId : Kernel")]))
  
  ;; Generate header type for logical structure
  (define header-constructors (case (lang-config-name config)
    ['lean (list
      (clean-constructor-name "header-zero")
      (clean-constructor-name "header-add")
      (clean-constructor-name "header-multiply"))]
    [else (list
      (format "  ~a : Header" (clean-constructor-name "header-zero"))
      (format "  ~a : Header ~a Header ~a Header" (clean-constructor-name "header-add") arrow arrow)
      (format "  ~a : Header ~a Header ~a Header" (clean-constructor-name "header-multiply") arrow arrow))]))
  
  ;; Generate normal form type
  (define nf-constructors (case (lang-config-name config)
    ['lean (list
      (clean-constructor-name "nf-phase")
      (clean-constructor-name "nf-scale")
      (clean-constructor-name "nf-core"))]
    [else (list
      (format "  ~a : NormalForm" (clean-constructor-name "nf-phase"))
      (format "  ~a : NormalForm" (clean-constructor-name "nf-scale"))
      (format "  ~a : NormalForm" (clean-constructor-name "nf-core")))]))
  
  (string-join
   (list
    (module-header config "Core" (case (lang-config-name config)
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
    (inductive config "Kernel" (list kernel-constructor))
    ""
    (inductive config "Header" header-constructors)
    ""
    (inductive config "NormalForm" nf-constructors)
    ""
    ;; Expanded axioms using logical structure
    (case (lang-config-name config)
      ['coq (string-join (list
        "Axiom plusB_comm : forall x y : Term, TermPlusB x y = TermPlusB y x."
        "Axiom multB_comm : forall x y : Term, TermMultB x y = TermMultB y x."
        "Axiom bulk_equals_boundaries : forall t : Term, exists l r : Term, t = TermPlusB l r."
        "Axiom observer_invisibility : forall t : Term, TermProject_L t = TermProject_R t -> t = TermInject_L (TermProject_L t).")
        "\n")]
      ['agda (string-join (list
        "postulate plusB-comm : ∀ x y → PlusB x y ≡ PlusB y x"
        "postulate multB-comm : ∀ x y → MultB x y ≡ MultB y x"
        "postulate bulk-equals-boundaries : ∀ t → t ≡ PlusB t t"
        "postulate observer-invisibility : ∀ t → Project_L t ≡ Project_R t → t ≡ Inject_L (Project_L t)")
        "\n")]
      ['lean (string-join (list
        "axiom plusB_comm : ∀ x y : Term, Term.TermPlusB x y = Term.TermPlusB y x"
        "axiom multB_comm : ∀ x y : Term, Term.TermMultB x y = Term.TermMultB y x"
        "axiom bulk_equals_boundaries : ∀ t : Term, ∃ l r : Term, t = Term.TermPlusB l r"
        "axiom observer_invisibility : ∀ t : Term, Term.TermProject_L t = Term.TermProject_R t → t = Term.TermInject_L (Term.TermProject_L t)")
        "\n")]
      ['isabelle (string-join (list
        "axiomatization plusB_comm where \"∀ x y. PlusB x y = PlusB y x\""
        "axiomatization multB_comm where \"∀ x y. MultB x y = MultB y x\""
        "axiomatization bulk_equals_boundaries where \"∀ t. ∃ l r. t = PlusB l r\""
        "axiomatization observer_invisibility where \"∀ t. Project_L t = Project_R t ⟶ t = Inject_L (Project_L t)\"")
        "\n")])
    "")
   "\n"))

;; Generate observers module with expanded functionality
(define (generate-observers config)
  (define imports (case (lang-config-name config)
    ['agda '("lib.Core")]
    ['coq '("Core")]
    ['lean '()]
    [else '("Core")]))
  
  (string-join
   (list
    (module-header config "Observers" imports)
    (comment config "CLEAN v10 Observers - Expanded with Logical Functions")
    ""
    ;; Basic observer functions (simplified to avoid cycles)
    (function config "project_L" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "project_R" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "inject_L" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "inject_R" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    ;; Logical observer functions from the API (simplified to avoid external dependencies)
    (function config "reflect_L" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "reflect_R" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "observer_value" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "reconstitute" "Term → Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun l r => l" "λ l r → l"))
    ""
    (function config "residual" "Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun t => t" "λ t → t"))
    ""
    (function config "triality_sum" "Term → Term → Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun l b r => l" "λ l b r → l"))
    "")
   "\n"))

;; Generate kernels module with expanded functionality
(define (generate-kernels config)
  (define imports (case (lang-config-name config)
    ['agda '("lib.Core")]
    ['coq '("Core")]
    ['lean '()]
    [else '("Core")]))
  
  (string-join
   (list
    (module-header config "Kernels" imports)
    (comment config "CLEAN v10 Kernels - Expanded with Logical Operations")
    ""
    ;; Define Kernel type locally to avoid external dependencies
    (case (lang-config-name config)
      ['lean (inductive config "Kernel" (list "KernelId"))]
      [else ""])
    ""
    ;; Basic kernel functions
    (function config "kernel_compose" "Kernel → Kernel → Kernel" 
      (if (eq? (lang-config-name config) 'coq) "fun k1 k2 => k1" "λ k1 k2 → k1"))
    ""
    (function config "kernel_apply" "Kernel → Term → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun k t => t" "λ k t → t"))
    ""
    (function config "kernel_identity" "Kernel" 
      (if (eq? (lang-config-name config) 'coq) "KernelId" 
          (if (eq? (lang-config-name config) 'lean) "Kernel.KernelId" "KernelId")))
    ""
    ;; Logical kernel functions from the API
    (function config "kernel_header_add" "Kernel → Header → Header → Kernel" 
      (if (eq? (lang-config-name config) 'coq) "fun k h1 h2 => k" "λ k h1 h2 → k"))
    ""
    (function config "kernel_header_product" "Kernel → Header → Header → Kernel" 
      (if (eq? (lang-config-name config) 'coq) "fun k h1 h2 => k" "λ k h1 h2 → k"))
    ""
    (function config "kernel_header_zero" "Kernel → Kernel" 
      (if (eq? (lang-config-name config) 'coq) "fun k => KernelId" 
          (if (eq? (lang-config-name config) 'lean) "λ k => Kernel.KernelId" "λ k → KernelId")))
    ""
    (function config "identity_kernel" "Kernel" 
      (if (eq? (lang-config-name config) 'coq) "KernelId" 
          (if (eq? (lang-config-name config) 'lean) "Kernel.KernelId" "KernelId")))
    "")
   "\n"))

;; Generate normal forms module
(define (generate-normal-forms config)
  (define imports (case (lang-config-name config)
    ['agda '("lib.Core" "Agda.Builtin.Bool")]
    ['coq '("Core")]
    ['lean '()]
    [else '("Core")]))
  
  (string-join
   (list
    (module-header config "NormalForms" imports)
    (comment config "CLEAN v10 Normal Forms - Logical Structure")
    ""
    ;; Define types locally to avoid external dependencies
    (case (lang-config-name config)
      ['lean (string-join (list
        (inductive config "Term" (list "ConstB"))
        (inductive config "Header" (list "header_zero"))
        (inductive config "NormalForm" (list "nf_core")))
        "\n")]
      [else ""])
    ""
    ;; Normal form functions from the API
    (function config "normal_form" "Term → NormalForm" 
      (if (eq? (lang-config-name config) 'coq) "fun t => nf_core" 
          (if (eq? (lang-config-name config) 'lean) "λ t => NormalForm.nf_core" "λ t → nf_core")))
    ""
    (function config "get_nf_phase" "NormalForm → Header" 
      (if (eq? (lang-config-name config) 'coq) "fun nf => header_zero" 
          (if (eq? (lang-config-name config) 'lean) "λ nf => Header.header_zero" "λ nf → header_zero")))
    ""
    (function config "get_nf_scale" "NormalForm → Header" 
      (if (eq? (lang-config-name config) 'coq) "fun nf => header_zero" 
          (if (eq? (lang-config-name config) 'lean) "λ nf => Header.header_zero" "λ nf → header_zero")))
    ""
    (function config "get_nf_core" "NormalForm → Term" 
      (if (eq? (lang-config-name config) 'coq) "fun nf => ConstB ZeroB" 
          (if (eq? (lang-config-name config) 'lean) "λ nf => Term.ConstB" "λ nf → ConstB ZeroB")))
    ""
    (function config "equal_up_to_nf" "Term → Term → Bool" 
      (if (eq? (lang-config-name config) 'coq) "fun t1 t2 => true" "λ t1 t2 → true"))
    "")
   "\n"))

;; Generate main library
(define (generate-main config)
  (string-join
   (list
    (case (lang-config-name config)
      ['coq (string-join (list
        "Require Import Core."
        "Require Import Observers."
        "Require Import Kernels."
        "Require Import NormalForms."
        "")
        "\n")]
      ['agda (string-join (list
        "module CLEAN where"
        ""
        "open import lib.Core"
        "open import lib.Observers"
        "open import lib.Kernels"
        "open import lib.NormalForms"
        "")
        "\n")]
      ['lean (string-join (list
        "")
        "\n")]
      ['isabelle (string-join (list
        "theory CLEAN"
        "imports Main"
        "begin"
        "")
        "\n")])
    (comment config "CLEAN v10 Main Library - Simplified")
    ""
    (case (lang-config-name config)
      ['coq (string-join (list
        "Definition CLEAN_Sort := Sort."
        "Definition CLEAN_Term := Term."
        "Definition CLEAN_PlusB := PlusB.")
        "\n")]
      ['agda (string-join (list
        "CLEAN-Sort : Set"
        "CLEAN-Sort = Sort"
        ""
        "CLEAN-Term : Set"
        "CLEAN-Term = Term"
        ""
        "CLEAN-PlusB : Term → Term → Term"
        "CLEAN-PlusB = PlusB")
        "\n")]
      ['lean (string-join (list
        "inductive CleanSort : Type where"
        "| L"
        "| B" 
        "| R"
        "| I"
        ""
        "inductive Term : Type where"
        "| ConstL : Term"
        "| ConstB : Term"
        "| ConstR : Term"
        "| ConstI : Term"
        "| PlusB : Term → Term → Term"
        "| MultB : Term → Term → Term"
        ""
        "def CLEAN_Sort : Type := CleanSort"
        "def CLEAN_Term : Type := Term"
        "def CLEAN_PlusB : Term → Term → Term := Term.PlusB")
        "\n")]
      ['isabelle (string-join (list
        "datatype Sort = L | B | R | I"
        "datatype Term = ConstL | ConstB | ConstR | ConstI | PlusB Term Term | MultB Term Term"
        ""
        "definition CLEAN_Sort :: \"Sort\" where \"CLEAN_Sort = L\""
        "definition CLEAN_Term :: \"Term\" where \"CLEAN_Term = ConstB\""
        "definition CLEAN_PlusB :: \"Term => Term => Term\" where \"CLEAN_PlusB = PlusB\"")
        "\n")])
    (case (lang-config-name config)
      ['isabelle "end"]
      [else ""])
    "")
   "\n"))

;; Main generation function
(define (generate-library target-lang output-dir)
  (define config (case target-lang
                   ['coq coq-config]
                   ['agda agda-config]
                   ['lean lean-config]
                   ['isabelle isabelle-config]))
  
  (define sig (current-signature))
  
  (displayln (format "🚀 Generating CLEAN v10 ~a Library (Simplified)..." (symbol->string target-lang)))
  
  ;; Generate modules
  (define core-content (generate-core config sig))
  (define observers-content (generate-observers config))
  (define kernels-content (generate-kernels config))
  (define normal-forms-content (generate-normal-forms config))
  (define main-content (generate-main config))
  
  ;; Write files
  (define ext (lang-config-ext config))
  (make-directory* (build-path output-dir "lib"))
  
  (display-to-file core-content (build-path output-dir "lib" (string-append "Core" ext)) #:exists 'replace)
  (display-to-file observers-content (build-path output-dir "lib" (string-append "Observers" ext)) #:exists 'replace)
  (display-to-file kernels-content (build-path output-dir "lib" (string-append "Kernels" ext)) #:exists 'replace)
  (display-to-file normal-forms-content (build-path output-dir "lib" (string-append "NormalForms" ext)) #:exists 'replace)
  (display-to-file main-content (build-path output-dir (string-append "CLEAN" ext)) #:exists 'replace)
  
  (displayln (format "✅ CLEAN v10 ~a Library generated successfully!" (symbol->string target-lang)))
  (displayln (format "📁 Output directory: ~a" output-dir)))

;; Convenience functions
(define (generate-coq-library-unified output-dir) (generate-library 'coq output-dir))
(define (generate-agda-library-unified output-dir) (generate-library 'agda output-dir))
(define (generate-lean-library-unified output-dir) (generate-library 'lean output-dir))
(define (generate-isabelle-library-unified output-dir) (generate-library 'isabelle output-dir))

(define (generate-all-libraries-unified base-output-dir)
  (displayln "🚀 Generating CLEAN v10 Libraries for All Languages (Simplified)...")
  (generate-coq-library-unified (build-path base-output-dir "coq-simple"))
  (generate-agda-library-unified (build-path base-output-dir "agda-simple"))
  (generate-lean-library-unified (build-path base-output-dir "lean-simple"))
  (generate-isabelle-library-unified (build-path base-output-dir "isabelle-simple"))
  (displayln "✅ All CLEAN v10 libraries generated successfully!"))