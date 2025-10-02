#lang racket

(require racket/struct)

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
(define (get-observers-imports-isabelle) '("lib.generated-Core"))

(define (get-kernels-imports-coq) '("lib.generated_Core"))
(define (get-kernels-imports-agda) '("lib.generated-Core"))
(define (get-kernels-imports-lean) '())
(define (get-kernels-imports-isabelle) '("lib.generated-Core"))

(define (get-normal-forms-imports-coq) '("lib.generated_Core"))
(define (get-normal-forms-imports-agda) '("lib.generated-Core" "Agda.Builtin.Bool"))
(define (get-normal-forms-imports-lean) '())
(define (get-normal-forms-imports-isabelle) '("lib.generated-Core"))

(define (get-main-imports-coq) '("lib.generated_Core" "lib.generated_Observers" "lib.generated_Kernels" "lib.generated_NormalForms"))
(define (get-main-imports-agda) '("lib.generated-Core" "lib.generated-Observers" "lib.generated-Kernels" "lib.generated-NormalForms"))
(define (get-main-imports-lean) '())
(define (get-main-imports-isabelle) '("lib.generated-Core" "lib.generated-Observers" "lib.generated-Kernels" "lib.generated-NormalForms"))

;; Constructor formatting functions
(define (sort-constructor-format-lean sorts)
  (map (λ (s) (format "~a" s)) sorts))

(define (sort-constructor-format-default sorts)
  (map (λ (s) (format "  ~a : Sort" s)) sorts))

(define (op-constructor-format-lean operations)
  (map (λ (op) (format "~a" (clean-name (car op)))) operations))

(define (op-constructor-format-default operations)
  (map (λ (op) (format "  ~a : Operation" (clean-name (car op)))) operations))

(define (const-constructor-format-lean constants)
  (map (λ (c) (format "~a" (clean-name (car c)))) constants))

(define (const-constructor-format-default constants)
  (map (λ (c) (format "  ~a : Constant" (clean-name (car c)))) constants))

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
               get-normal-forms-imports-coq get-main-imports-coq))

(define agda-config 
  (lang-config 'agda ".agda" "→" "λ" "-- ~a"
               clean-name clean-constructor-name-default module-header-agda
               "generated-" "." "" "Sort"
               sort-constructor-format-default op-constructor-format-default 
               const-constructor-format-default term-constructor-format-default
               get-core-imports-agda get-observers-imports-agda get-kernels-imports-agda
               get-normal-forms-imports-agda get-main-imports-agda))

(define lean-config 
  (lang-config 'lean ".lean" "→" "λ" "-- ~a"
               clean-name clean-constructor-name-default module-header-lean
               "generated-" " " "" "CleanSort"
               sort-constructor-format-lean op-constructor-format-lean 
               const-constructor-format-lean term-constructor-format-lean
               get-core-imports-lean get-observers-imports-lean get-kernels-imports-lean
               get-normal-forms-imports-lean get-main-imports-lean))

(define isabelle-config 
  (lang-config 'isabelle ".thy" "⇒" "λ" "(* ~a *)"
               clean-name clean-constructor-name-default module-header-isabelle
               "generated-" " " "" "Sort"
               sort-constructor-format-default op-constructor-format-default 
               const-constructor-format-default term-constructor-format-default
               get-core-imports-isabelle get-observers-imports-isabelle get-kernels-imports-isabelle
               get-normal-forms-imports-isabelle get-main-imports-isabelle))

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
