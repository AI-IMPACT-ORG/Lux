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
               "generated_" "."))

(define agda-config 
  (lang-config 'agda ".agda" "→" "λ" "-- ~a"
               clean-name clean-constructor-name-default module-header-agda
               "generated-" "."))

(define lean-config 
  (lang-config 'lean ".lean" "→" "λ" "-- ~a"
               clean-name clean-constructor-name-default module-header-lean
               "generated-" " "))

(define isabelle-config 
  (lang-config 'isabelle ".thy" "⇒" "λ" "(* ~a *)"
               clean-name clean-constructor-name-default module-header-isabelle
               "generated-" " "))

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
