#lang racket

(require racket/struct
         racket/file
         racket/path
         racket/format
         racket/string)

(provide (all-defined-out))

;; ============================================================================
;; LANGUAGE CONFIGURATIONS
;; ============================================================================

;; Language configuration structure
(define-struct lang-config 
  (name                    ; Symbol: 'coq, 'agda, 'lean, 'isabelle
   ext                     ; String: file extension ".v", ".agda", etc.
   arrow                   ; String: function arrow "->", "→", "⇒"
   lambda                  ; String: lambda symbol "fun", "λ"
   comment                 ; String: comment format "(* ~a *)", "-- ~a"
   identifier-cleaner      ; Function: clean identifier names
   constructor-cleaner     ; Function: clean constructor names
   module-header-generator ; Function: generate module headers
   file-prefix            ; String: prefix for generated files
   import-separator       ; String: separator for imports
   constructor-prefix     ; String: prefix for constructors ("Term" for Coq, "" for others)
   sort-name              ; String: name for sort type ("Sort" or "CleanSort")
   sort-constructor-format ; Function: format sort constructors
   op-constructor-format   ; Function: format operation constructors
   const-constructor-format ; Function: format constant constructors
   term-constructor-format ; Function: format term constructors
   get-core-imports       ; Function: get core module imports
   get-observers-imports  ; Function: get observers module imports
   get-kernels-imports    ; Function: get kernels module imports
   get-normal-forms-imports ; Function: get normal forms module imports
   get-main-imports       ; Function: get main module imports
   inductive-generator    ; Function: generate inductive types
   function-generator     ; Function: generate function definitions
   axiom-generator        ; Function: generate axioms
   main-module-generator  ; Function: generate main module content
   deployment-function    ; Function: create deployment files
   ))

;; Identifier cleaning functions
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

;; Constructor cleaning functions
(define (clean-constructor-name-coq name)
  (string-replace (clean-name (string->symbol name)) "-" "_"))

(define (clean-constructor-name-default name)
  (clean-name (string->symbol name)))

;; Import functions
(define (get-core-imports-coq) '("Arith.Arith" "Arith.PeanoNat"))
(define (get-core-imports-agda) '("Agda.Builtin.Nat" "Agda.Builtin.String" "Agda.Builtin.Equality"))
(define (get-core-imports-lean) '())
(define (get-core-imports-isabelle) '("Main"))

(define (get-observers-imports-coq) '("lib.generated_Core"))
(define (get-observers-imports-agda) '("lib.generated-Core"))
(define (get-observers-imports-lean) '())
(define (get-observers-imports-isabelle) '("generated_Core"))

(define (get-kernels-imports-coq) '("lib.generated_Core"))
(define (get-kernels-imports-agda) '("lib.generated-Core"))
(define (get-kernels-imports-lean) '())
(define (get-kernels-imports-isabelle) '("generated_Core"))

(define (get-normal-forms-imports-coq) '("lib.generated_Core"))
(define (get-normal-forms-imports-agda) '("lib.generated-Core" "Agda.Builtin.Bool"))
(define (get-normal-forms-imports-lean) '())
(define (get-normal-forms-imports-isabelle) '("generated_Core"))

(define (get-main-imports-coq) '("lib.generated_Core" "lib.generated_Observers" "lib.generated_Kernels" "lib.generated_NormalForms"))
(define (get-main-imports-agda) '("lib.generated-Core" "lib.generated-Observers" "lib.generated-Kernels" "lib.generated-NormalForms"))
(define (get-main-imports-lean) '())
(define (get-main-imports-isabelle) '("generated_Core" "generated_Observers" "generated_Kernels" "generated_NormalForms"))

;; Deployment functions
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

(define (create-isabelle-root output-dir prefix ext)
  (define root-content
    (string-join
     (list
      "session CLEAN = HOL +"
      "  directories \"lib\""
      "  theories"
      (format "    \"lib/~aCore\"" prefix)
      (format "    \"lib/~aObservers\"" prefix)
      (format "    \"lib/~aKernels\"" prefix)
      (format "    \"lib/~aNormalForms\"" prefix)
      (format "    \"~aCLEAN\"" prefix))
     "\n"))
  (display-to-file root-content (build-path output-dir "ROOT") #:exists 'replace))

(define (deployment-coq output-dir prefix ext)
  (create-coq-project output-dir prefix ext))

(define (deployment-agda output-dir prefix ext)
  (void)) ; Agda doesn't need special deployment files

(define (deployment-lean output-dir prefix ext)
  (void)) ; Lean doesn't need special deployment files

(define (deployment-isabelle output-dir prefix ext)
  (create-isabelle-root output-dir prefix ext))

;; Main module generators
(define (main-module-generator-coq imports)
  (string-join (list
    "Require Import lib.generated_Core."
    "Require Import lib.generated_Observers."
    "Require Import lib.generated_Kernels."
    "Require Import lib.generated_NormalForms."
    ""
    "Module CLEAN."
    ""
    "Definition CLEAN_Sort : Type := Sort."
    "Definition CLEAN_Term : Type := Term."
    "Definition CLEAN_PlusB : Term -> Term -> Term := TermPlusB."
    ""
    "End CLEAN."
    "") "\n"))

(define (main-module-generator-agda imports)
  (string-join (list
    "module lib.CLEAN where"
    ""
    "open import lib.generated-Core"
    "open import lib.generated-Observers"
    "open import lib.generated-Kernels"
    "open import lib.generated-NormalForms"
    ""
    "CLEAN_Sort : Set"
    "CLEAN_Sort = Sort"
    ""
    "CLEAN_Term : Set"
    "CLEAN_Term = Term"
    ""
    "CLEAN_PlusB : Term → Term → Term"
    "CLEAN_PlusB = TermPlusB"
    "") "\n"))

(define (main-module-generator-lean imports)
  (string-join (list
    "inductive CleanSort : Type where | L | B | R | I"
    "inductive Term : Type where | ConstL | ConstB | ConstR | ConstI | PlusB Term Term | MultB Term Term"
    ""
    "def CLEAN_Sort : Type := CleanSort"
    "def CLEAN_Term : Type := Term"
    "def CLEAN_PlusB : Term → Term → Term := Term.PlusB"
    "") "\n"))

(define (main-module-generator-isabelle imports)
  (string-join (list
    "theory generated_CLEAN"
    "imports Main"
    "begin"
    ""
    "datatype Sort = L | B | R | I"
    "datatype Term = ConstL | ConstB | ConstR | ConstI | PlusB Term Term | MultB Term Term"
    ""
    "definition CLEAN_Sort :: \"Sort\" where \"CLEAN_Sort = L\""
    "definition CLEAN_Term :: \"Term\" where \"CLEAN_Term = ConstB\""
    "definition CLEAN_PlusB :: \"Term => Term => Term\" where \"CLEAN_PlusB = PlusB\""
    ""
    "end"
    "") "\n"))

;; Generation functions
(define (inductive-generator-coq name constructors)
  (format "Inductive ~a : Type :=\n| ~a." name (string-join constructors "\n| ")))

(define (inductive-generator-agda name constructors)
  (format "data ~a : Set where\n~a" name (string-join constructors "\n")))

(define (inductive-generator-lean name constructors)
  (format "inductive ~a : Type where\n| ~a" name (string-join constructors "\n| ")))

(define (inductive-generator-isabelle name constructors)
  (format "datatype ~a = ~a" name (string-join constructors " | ")))

(define (function-generator-coq name type body)
  (format "Definition ~a : ~a :=\n  ~a." name type (string-replace body "->" "=>")))

(define (function-generator-agda name type body)
  (format "~a : ~a\n~a = ~a" name type name body))

(define (function-generator-lean name type body)
  (format "def ~a : ~a :=\n  ~a" name type body))

(define (function-generator-isabelle name type body)
  (format "definition ~a :: \"~a\" where \"~a = ~a\"" name type name body))

(define (axiom-generator-coq name statement)
  (format "Axiom ~a : ~a." name statement))

(define (axiom-generator-agda name statement)
  (format "postulate ~a : ~a" name statement))

(define (axiom-generator-lean name statement)
  (format "axiom ~a : ~a" name statement))

(define (axiom-generator-isabelle name statement)
  (format "axiomatization ~a where \"~a\"" name statement))

;; Constructor formatting functions
(define (sort-constructor-format-lean sorts)
  (map (λ (s) (format "~a" s)) sorts))

(define (sort-constructor-format-default sorts)
  (map (λ (s) (format "~a" s)) sorts))

(define (op-constructor-format-lean operations)
  (map (λ (op) (format "~a" (clean-name (car op)))) operations))

(define (op-constructor-format-default operations)
  (map (λ (op) (format "~a" (clean-name (car op)))) operations))

(define (const-constructor-format-lean constants)
  (map (λ (c) (format "~a" (clean-name (car c)))) constants))

(define (const-constructor-format-default constants)
  (map (λ (c) (format "~a" (clean-name (car c)))) constants))

(define (term-constructor-format-lean sorts operations)
  (append
    (map (λ (s) (format "Const~a" s)) sorts)
    (map (λ (op) 
      (define name (clean-name (car op)))
      (define is-unary (or (string-contains? name "Inject") (string-contains? name "Project")))
      (if is-unary
          (format "Term~a : Term → Term" name)
          (format "Term~a : Term → Term → Term" name)))
      operations)))

(define (term-constructor-format-coq sorts operations)
  (append
    (map (λ (s) (format "  Const~a : Constant -> Term" s)) sorts)
    (map (λ (op) 
      (define name (clean-name (car op)))
      (define is-unary (or (string-contains? name "Inject") (string-contains? name "Project")))
      (define term-name (string-append "Term" name))
      (if is-unary
          (format "  ~a : Term -> Term" term-name)
          (format "  ~a : Term -> Term -> Term" term-name)))
      operations)))

(define (term-constructor-format-isabelle sorts operations)
  (append
    (map (λ (s) (format "Const~a" s)) sorts)
    (map (λ (op) 
      (define name (clean-name (car op)))
      (format "~a" name))
      operations)))

(define (term-constructor-format-default sorts operations)
  (append
    (map (λ (s) (format "  Const~a : Constant -> Term" s)) sorts)
    (map (λ (op) 
      (define name (clean-name (car op)))
      (define is-unary (or (string-contains? name "Inject") (string-contains? name "Project")))
      (if is-unary
          (format "  ~a : Term -> Term" name)
          (format "  ~a : Term -> Term -> Term" name)))
      operations)))

;; Module header generators
(define (module-header-coq name imports)
  (if (empty? imports) 
      "" 
      (string-join (map (λ (imp) (format "Require Import ~a." imp)) imports) "\n" #:after-last "\n\n")))

(define (module-header-agda name imports)
  (format "module lib.~a where\n~a\n" name (string-join (map (λ (imp) (format "open import ~a" imp)) imports) "\n")))

(define (module-header-lean name imports)
  (if (empty? imports) 
      (format "namespace ~a\n\n" name)
      (format "import ~a\n\nnamespace ~a\n\n" (string-join imports " ") name)))

(define (module-header-isabelle name imports)
  (format "theory ~a\nimports ~a\nbegin\n\n" name (string-join imports " ")))

;; Language configurations
(define coq-config 
  (lang-config 'coq ".v" "->" "fun" "(* ~a *)"
               clean-name clean-constructor-name-coq module-header-coq
               "generated_" "." "Term" "Sort"
               sort-constructor-format-default op-constructor-format-default 
               const-constructor-format-default term-constructor-format-coq
               get-core-imports-coq get-observers-imports-coq get-kernels-imports-coq
               get-normal-forms-imports-coq get-main-imports-coq
               inductive-generator-coq function-generator-coq axiom-generator-coq
               main-module-generator-coq deployment-coq))

(define agda-config 
  (lang-config 'agda ".agda" "→" "λ" "-- ~a"
               clean-name clean-constructor-name-default module-header-agda
               "generated-" "." "" "Sort"
               sort-constructor-format-default op-constructor-format-default 
               const-constructor-format-default term-constructor-format-default
               get-core-imports-agda get-observers-imports-agda get-kernels-imports-agda
               get-normal-forms-imports-agda get-main-imports-agda
               inductive-generator-agda function-generator-agda axiom-generator-agda
               main-module-generator-agda deployment-agda))

(define lean-config 
  (lang-config 'lean ".lean" "→" "λ" "-- ~a"
               clean-name clean-constructor-name-default module-header-lean
               "generated-" " " "" "CleanSort"
               sort-constructor-format-lean op-constructor-format-lean 
               const-constructor-format-lean term-constructor-format-lean
               get-core-imports-lean get-observers-imports-lean get-kernels-imports-lean
               get-normal-forms-imports-lean get-main-imports-lean
               inductive-generator-lean function-generator-lean axiom-generator-lean
               main-module-generator-lean deployment-lean))

(define isabelle-config 
  (lang-config 'isabelle ".thy" "⇒" "λ" "(* ~a *)"
               clean-name clean-constructor-name-default module-header-isabelle
               "generated_" " " "" "Sort"
               sort-constructor-format-default op-constructor-format-default 
               const-constructor-format-default term-constructor-format-isabelle
               get-core-imports-isabelle get-observers-imports-isabelle get-kernels-imports-isabelle
               get-normal-forms-imports-isabelle get-main-imports-isabelle
               inductive-generator-isabelle function-generator-isabelle axiom-generator-isabelle
               main-module-generator-isabelle deployment-isabelle))

;; ============================================================================
;; LANGUAGE CONFIGURATION VALIDATION
;; ============================================================================

;; Validate language configuration completeness
(define (validate-language-config config)
  (define errors '())
  
  ;; Check required fields
  (when (not (lang-config-name config))
    (set! errors (cons "Missing language name" errors)))
  
  (when (not (lang-config-ext config))
    (set! errors (cons "Missing file extension" errors)))
  
  (when (not (lang-config-arrow config))
    (set! errors (cons "Missing arrow symbol" errors)))
  
  (when (not (lang-config-lambda config))
    (set! errors (cons "Missing lambda symbol" errors)))
  
  (when (not (lang-config-comment config))
    (set! errors (cons "Missing comment format" errors)))
  
  ;; Check functions
  (when (not (procedure? (lang-config-identifier-cleaner config)))
    (set! errors (cons "Invalid identifier cleaner function" errors)))
  
  (when (not (procedure? (lang-config-constructor-cleaner config)))
    (set! errors (cons "Invalid constructor cleaner function" errors)))
  
  (when (not (procedure? (lang-config-module-header-generator config)))
    (set! errors (cons "Invalid module header generator function" errors)))
  
  (when (not (procedure? (lang-config-inductive-generator config)))
    (set! errors (cons "Invalid inductive generator function" errors)))
  
  (when (not (procedure? (lang-config-function-generator config)))
    (set! errors (cons "Invalid function generator function" errors)))
  
  (when (not (procedure? (lang-config-axiom-generator config)))
    (set! errors (cons "Invalid axiom generator function" errors)))
  
  (when (not (procedure? (lang-config-main-module-generator config)))
    (set! errors (cons "Invalid main module generator function" errors)))
  
  (when (not (procedure? (lang-config-deployment-function config)))
    (set! errors (cons "Invalid deployment function" errors)))
  
  ;; Return validation result
  (if (empty? errors)
      #t
      (error (format "Language configuration validation failed: ~a" (string-join errors ", ")))))

;; Validate all language configurations
(define (validate-all-configurations)
  (validate-language-config coq-config)
  (validate-language-config agda-config)
  (validate-language-config lean-config)
  (validate-language-config isabelle-config)
  (displayln "✅ All language configurations validated successfully!"))

;; Get language configuration by name
(define (get-language-config lang-name)
  (case lang-name
    ['coq coq-config]
    ['agda agda-config]
    ['lean lean-config]
    ['isabelle isabelle-config]
    [else (error (format "Unknown language: ~a" lang-name))]))

;; Get all supported languages
(define (get-all-languages)
  '(coq agda lean isabelle))
