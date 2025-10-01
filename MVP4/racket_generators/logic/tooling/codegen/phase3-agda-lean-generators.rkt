#lang racket

(require "../../api.rkt"
         racket/format
         racket/file
         racket/path
         racket/string
         racket/list)

(provide (all-defined-out))

;; ============================================================================
;; PHASE 3: AGDA AND LEAN GENERATORS USING NEW ARCHITECTURE
;; ============================================================================

;; Agda template system
(define-struct agda-template
  (name content parameters))

;; Agda template registry
(define agda-template-registry (make-hash))

;; Register Agda template
(define (register-agda-template name content parameters)
  (hash-set! agda-template-registry name 
             (agda-template name content parameters)))

;; Load Agda templates
(define (load-agda-templates)
  ;; Core module template
  (register-agda-template "agda-core-module"
                         "module ~a where\n\n~a\n\n~a"
                         '(module-name imports content))
  
  ;; Sort definition template
  (register-agda-template "agda-sort-definition"
                         "data Sort : Set where\n~a"
                         '(constructors))
  
  ;; Operation definition template
  (register-agda-template "agda-operation-definition"
                         "data Operation : Set where\n~a"
                         '(constructors))
  
  ;; Constant definition template
  (register-agda-template "agda-constant-definition"
                         "data Constant : Set where\n~a"
                         '(constructors))
  
  ;; Term definition template
  (register-agda-template "agda-term-definition"
                         "data Term : Set where\n~a"
                         '(constructors))
  
  ;; Axiom template
  (register-agda-template "agda-axiom"
                         "postulate ~a : ~a"
                         '(name statement))
  
  ;; Function template
  (register-agda-template "agda-function"
                         "~a : ~a\n~a = ~a"
                         '(name type body))

;; Process Agda template with parameters
(define (process-agda-template template-name parameters)
  (define template (hash-ref agda-template-registry template-name #f))
  (if template
      (let ([content (agda-template-content template)]
            [param-list (agda-template-parameters template)])
        (apply format content (map (λ (param) (hash-ref parameters param #f)) param-list)))
      (error (format "Agda template ~a not found" template-name))))

;; ============================================================================
;; AGDA GENERATOR USING NEW ARCHITECTURE
;; ============================================================================

;; Main Agda generator using new architecture
(define (generate-agda-library-new-architecture output-dir)
  (define lib-dir (build-path output-dir "lib"))
  (make-directory* lib-dir)
  
  ;; Load Agda templates
  (load-agda-templates)
  
  ;; Get signature information
  (define sig (current-signature))
  (define sorts (signature-sorts sig))
  (define operations (signature-operations sig))
  (define constants (signature-constants sig))
  
  ;; Generate all modules
  (generate-agda-core-module lib-dir sorts operations constants)
  (generate-agda-observers-module lib-dir)
  (generate-agda-kernels-module lib-dir)
  (generate-agda-main-library output-dir)
  
  (displayln "✅ Agda library generated with new architecture!"))

;; Generate Agda core module
(define (generate-agda-core-module lib-dir sorts operations constants)
  (define core-file (build-path lib-dir "Core.agda"))
  
  ;; Format imports
  (define imports "open import Agda.Builtin.Nat using (Nat)\nopen import Agda.Builtin.String using (String)")
  
  ;; Generate sorts
  (define sort-constructors (map (λ (sort) (format "  ~a : Sort" sort)) sorts))
  (define sorts-content (process-agda-template "agda-sort-definition" 
                                               (hash 'constructors (string-join sort-constructors "\n"))))
  
  ;; Generate operations
  (define op-constructors (map format-agda-operation-constructor operations))
  (define operations-content (process-agda-template "agda-operation-definition"
                                                    (hash 'constructors (string-join op-constructors "\n"))))
  
  ;; Generate constants
  (define const-constructors (map format-agda-constant-constructor constants))
  (define constants-content (process-agda-template "agda-constant-definition"
                                                    (hash 'constructors (string-join const-constructors "\n"))))
  
  ;; Generate terms
  (define term-constructors (generate-agda-term-constructors sorts operations constants))
  (define terms-content (process-agda-template "agda-term-definition"
                                                (hash 'constructors (string-join term-constructors "\n"))))
  
  ;; Generate axioms
  (define axioms-content (generate-agda-axioms-content))
  
  ;; Combine all content
  (define content (string-join (list sorts-content operations-content constants-content 
                                     terms-content axioms-content) "\n\n"))
  
  ;; Generate final core module
  (define core-content (process-agda-template "agda-core-module"
                                              (hash 'module-name "Core"
                                                    'imports imports
                                                    'content content)))
  
  (display-to-file core-content core-file #:exists 'replace))

;; Format Agda operation constructor
(define (format-agda-operation-constructor op)
  (define name (car op))
  (define type (cdr op))
  ;; Convert Unicode symbols to ASCII equivalents
  (define clean-name (string-replace (string-replace (string-replace (string-replace (symbol->string name) "⊕" "Plus") "⊗" "Mult") "ι" "Inject") "ν" "Project"))
  ;; Skip empty names
  (if (equal? clean-name "")
      ""
      (format "  ~a : Operation" clean-name)))

;; Format Agda constant constructor
(define (format-agda-constant-constructor const)
  (define name (car const))
  (define type (cdr const))
  ;; Convert Unicode symbols to ASCII equivalents
  (define clean-name (string-replace (string-replace (string-replace (symbol->string name) "⊕" "Plus") "⊗" "Mult") "ι" "Inject"))
  (format "  ~a : Constant" clean-name))

;; Generate Agda term constructors
(define (generate-agda-term-constructors sorts operations constants)
  (define constructors '())
  
  ;; Add constructors for each sort
  (for ([sort sorts])
    (set! constructors (append constructors (list (format "  Const~a : Constant → Term" sort)))))
  
  ;; Add operation constructors
  (for ([op operations])
    (define name (car op))
    (define clean-name (string-replace (string-replace (string-replace (string-replace (symbol->string name) "⊕" "Plus") "⊗" "Mult") "ι" "Inject") "ν" "Project"))
    (when (not (equal? clean-name ""))
      (set! constructors (append constructors (list (format "  Term~a : Term" clean-name))))))
  
  ;; Add Unit sort constructors
  (set! constructors (append constructors (list "  TermPlusU : Term → Term → Term")))
  (set! constructors (append constructors (list "  TermMultU : Term → Term → Term")))
  
  constructors)

;; Generate Agda axioms content
(define (generate-agda-axioms-content)
  (define axioms '())
  
  ;; Add basic semiring axioms
  (set! axioms (append axioms (list "postulate plusL-comm : ∀ x y → TermPlusL x y ≡ TermPlusL y x")))
  (set! axioms (append axioms (list "postulate plusL-assoc : ∀ x y z → TermPlusL (TermPlusL x y) z ≡ TermPlusL x (TermPlusL y z)")))
  (set! axioms (append axioms (list "postulate plusL-idempotent : ∀ x → TermPlusL x x ≡ x")))
  (set! axioms (append axioms (list "postulate plusL-zero : ∀ x → TermPlusL (ConstL ZeroL) x ≡ x")))
  
  (set! axioms (append axioms (list "postulate multL-comm : ∀ x y → TermMultL x y ≡ TermMultL y x")))
  (set! axioms (append axioms (list "postulate multL-assoc : ∀ x y z → TermMultL (TermMultL x y) z ≡ TermMultL x (TermMultL y z)")))
  (set! axioms (append axioms (list "postulate multL-idempotent : ∀ x → TermMultL x x ≡ x")))
  (set! axioms (append axioms (list "postulate multL-one : ∀ x → TermMultL (ConstL OneL) x ≡ x")))
  (set! axioms (append axioms (list "postulate multL-distrib : ∀ x y z → TermMultL x (TermPlusL y z) ≡ TermPlusL (TermMultL x y) (TermMultL x z)")))
  (set! axioms (append axioms (list "postulate multL-absorption : ∀ x y → TermMultL x (TermPlusL x y) ≡ x")))
  
  ;; Add Right axioms
  (set! axioms (append axioms (list "postulate plusR-comm : ∀ x y → TermPlusR x y ≡ TermPlusR y x")))
  (set! axioms (append axioms (list "postulate plusR-assoc : ∀ x y z → TermPlusR (TermPlusR x y) z ≡ TermPlusR x (TermPlusR y z)")))
  (set! axioms (append axioms (list "postulate plusR-idempotent : ∀ x → TermPlusR x x ≡ x")))
  (set! axioms (append axioms (list "postulate plusR-zero : ∀ x → TermPlusR (ConstR ZeroR) x ≡ x")))
  
  (set! axioms (append axioms (list "postulate multR-comm : ∀ x y → TermMultR x y ≡ TermMultR y x")))
  (set! axioms (append axioms (list "postulate multR-assoc : ∀ x y z → TermMultR (TermMultR x y) z ≡ TermMultR x (TermMultR y z)")))
  (set! axioms (append axioms (list "postulate multR-idempotent : ∀ x → TermMultR x x ≡ x")))
  (set! axioms (append axioms (list "postulate multR-one : ∀ x → TermMultR (ConstR OneR) x ≡ x")))
  (set! axioms (append axioms (list "postulate multR-distrib : ∀ x y z → TermMultR x (TermPlusR y z) ≡ TermPlusR (TermMultR x y) (TermMultR x z)")))
  (set! axioms (append axioms (list "postulate multR-absorption : ∀ x y → TermMultR x (TermPlusR x y) ≡ x")))
  
  ;; Add Bulk axioms
  (set! axioms (append axioms (list "postulate plusB-comm : ∀ x y → TermPlusB x y ≡ TermPlusB y x")))
  (set! axioms (append axioms (list "postulate plusB-assoc : ∀ x y z → TermPlusB (TermPlusB x y) z ≡ TermPlusB x (TermPlusB y z)")))
  (set! axioms (append axioms (list "postulate plusB-zero : ∀ x → TermPlusB (ConstB ZeroB) x ≡ x")))
  (set! axioms (append axioms (list "postulate plusB-annihilating : ∀ x → TermPlusB x (ConstB ZeroB) ≡ x")))
  
  (set! axioms (append axioms (list "postulate multB-comm : ∀ x y → TermMultB x y ≡ TermMultB y x")))
  (set! axioms (append axioms (list "postulate multB-assoc : ∀ x y z → TermMultB (TermMultB x y) z ≡ TermMultB x (TermMultB y z)")))
  (set! axioms (append axioms (list "postulate multB-one : ∀ x → TermMultB (ConstB OneB) x ≡ x")))
  (set! axioms (append axioms (list "postulate multB-distrib : ∀ x y z → TermMultB x (TermPlusB y z) ≡ TermPlusB (TermMultB x y) (TermMultB x z)")))
  
  ;; Add observer axioms
  (set! axioms (append axioms (list "postulate observer-retraction-L : ∀ x → TermProjectL (TermInjectL x) ≡ x")))
  (set! axioms (append axioms (list "postulate observer-retraction-R : ∀ x → TermProjectR (TermInjectR x) ≡ x")))
  
  ;; Add residual invisibility axiom
  (set! axioms (append axioms (list "postulate residual-invisibility : ∀ t → let rho = TermPlusB (TermInjectL (TermProjectL t)) (TermInjectR (TermProjectR t)) in let residual = TermPlusB t rho in TermProjectL residual ≡ ConstL ZeroL × TermProjectR residual ≡ ConstR ZeroR")))
  
  ;; Add basepoint normalization
  (set! axioms (append axioms (list "postulate basepoint-normalization : TermMultB (ConstB Phi) (ConstB BarPhi) ≡ ConstB OneB")))
  
  ;; Add Unit sort axioms
  (set! axioms (append axioms (list "postulate unit-comm : ∀ x y → TermPlusU x y ≡ TermPlusU y x")))
  (set! axioms (append axioms (list "postulate unit-assoc : ∀ x y z → TermPlusU (TermPlusU x y) z ≡ TermPlusU x (TermPlusU y z)")))
  (set! axioms (append axioms (list "postulate unit-zero : ∀ x → TermPlusU (ConstI ZeroU) x ≡ x")))
  (set! axioms (append axioms (list "postulate unit-mult-comm : ∀ x y → TermMultU x y ≡ TermMultU y x")))
  (set! axioms (append axioms (list "postulate unit-mult-assoc : ∀ x y z → TermMultU (TermMultU x y) z ≡ TermMultU x (TermMultU y z)")))
  (set! axioms (append axioms (list "postulate unit-mult-one : ∀ x → TermMultU (ConstI OneU) x ≡ x")))
  (set! axioms (append axioms (list "postulate unit-mult-distrib : ∀ x y z → TermMultU x (TermPlusU y z) ≡ TermPlusU (TermMultU x y) (TermMultU x z)")))
  
  (string-join axioms "\n"))

;; Generate Agda observers module
(define (generate-agda-observers-module lib-dir)
  (define observers-file (build-path lib-dir "Observers.agda"))
  
  (define observer-functions (list
                             (process-agda-template "agda-function"
                                                    (hash 'name "project-L"
                                                          'type "Term → Term"
                                                          'body "λ t → ConstL ZeroL"))
                             (process-agda-template "agda-function"
                                                    (hash 'name "project-R"
                                                          'type "Term → Term"
                                                          'body "λ t → ConstR ZeroR"))
                             (process-agda-template "agda-function"
                                                    (hash 'name "inject-L"
                                                          'type "Term → Term"
                                                          'body "λ t → ConstB ZeroB"))
                             (process-agda-template "agda-function"
                                                    (hash 'name "inject-R"
                                                          'type "Term → Term"
                                                          'body "λ t → ConstB ZeroB"))
                             (process-agda-template "agda-function"
                                                    (hash 'name "reconstitute"
                                                          'type "Term → Term → Term"
                                                          'body "λ l r → TermPlusB (TermInjectL l) (TermInjectR r)"))
                             (process-agda-template "agda-function"
                                                    (hash 'name "residual"
                                                          'type "Term → Term"
                                                          'body "λ t → TermPlusB t (TermPlusB (TermInjectL (TermProjectL t)) (TermInjectR (TermProjectR t)))"))))
  
  (define content (string-join observer-functions "\n\n"))
  (display-to-file content observers-file #:exists 'replace))

;; Generate Agda kernels module
(define (generate-agda-kernels-module lib-dir)
  (define kernels-file (build-path lib-dir "Kernels.agda"))
  
  (define kernel-functions (list
                          (process-agda-template "agda-function"
                                                 (hash 'name "kernel-compose"
                                                       'type "Kernel → Kernel → Kernel"
                                                       'body "λ k1 k2 → k1"))
                          (process-agda-template "agda-function"
                                                 (hash 'name "kernel-apply"
                                                       'type "Kernel → Term → Term"
                                                       'body "λ k t → t"))
                          (process-agda-template "agda-function"
                                                 (hash 'name "kernel-identity"
                                                       'type "Kernel"
                                                       'body "λ t → t"))))
  
  (define content (string-join kernel-functions "\n\n"))
  (display-to-file content kernels-file #:exists 'replace))

;; Generate Agda main library
(define (generate-agda-main-library output-dir)
  (define main-file (build-path output-dir "CLEAN.agda"))
  
  ;; Read generated modules
  (define lib-dir (build-path output-dir "lib"))
  (define core-content (file->string (build-path lib-dir "Core.agda")))
  (define observers-content (file->string (build-path lib-dir "Observers.agda")))
  (define kernels-content (file->string (build-path lib-dir "Kernels.agda")))
  
  ;; Generate main library
  (define main-content (string-join (list
                                    "module CLEAN where"
                                    ""
                                    "open import Core"
                                    "open import Observers"
                                    "open import Kernels"
                                    ""
                                    "-- CLEAN v10 Agda Library - Generated with New Architecture"
                                    ""
                                    "-- Convenience Definitions"
                                    "CLEAN-Sort = Sort"
                                    "CLEAN-Operation = Operation"
                                    "CLEAN-Constant = Constant"
                                    "CLEAN-Term = Term"
                                    ""
                                    "-- Core operations"
                                    "CLEAN-PlusL = TermPlusL"
                                    "CLEAN-MultL = TermMultL"
                                    "CLEAN-PlusR = TermPlusR"
                                    "CLEAN-MultR = TermMultR"
                                    "CLEAN-PlusB = TermPlusB"
                                    "CLEAN-MultB = TermMultB"
                                    "CLEAN-PlusU = TermPlusU"
                                    "CLEAN-MultU = TermMultU"
                                    ""
                                    "-- Observer functions"
                                    "CLEAN-ProjectL = project-L"
                                    "CLEAN-ProjectR = project-R"
                                    "CLEAN-InjectL = inject-L"
                                    "CLEAN-InjectR = inject-R"
                                    "CLEAN-Reconstitute = reconstitute"
                                    "CLEAN-Residual = residual"
                                    ""
                                    "-- Kernel functions"
                                    "CLEAN-KernelCompose = kernel-compose"
                                    "CLEAN-KernelApply = kernel-apply"
                                    "CLEAN-IdentityKernel = kernel-identity")
                                   "\n"))
  
  (display-to-file main-content main-file #:exists 'replace))

;; ============================================================================
;; LEAN GENERATOR USING NEW ARCHITECTURE
;; ============================================================================

;; Lean template system
(define-struct lean-template
  (name content parameters))

;; Lean template registry
(define lean-template-registry (make-hash))

;; Register Lean template
(define (register-lean-template name content parameters)
  (hash-set! lean-template-registry name 
             (lean-template name content parameters)))

;; Load Lean templates
(define (load-lean-templates)
  ;; Core module template
  (register-lean-template "lean-core-module"
                         "import ~a\n\n~a"
                         '(imports content))
  
  ;; Sort definition template
  (register-lean-template "lean-sort-definition"
                         "inductive Sort : Type\n~a"
                         '(constructors))
  
  ;; Operation definition template
  (register-lean-template "lean-operation-definition"
                         "inductive Operation : Type\n~a"
                         '(constructors))
  
  ;; Constant definition template
  (register-lean-template "lean-constant-definition"
                         "inductive Constant : Type\n~a"
                         '(constructors))
  
  ;; Term definition template
  (register-lean-template "lean-term-definition"
                         "inductive Term : Type\n~a"
                         '(constructors))
  
  ;; Axiom template
  (register-lean-template "lean-axiom"
                         "axiom ~a : ~a"
                         '(name statement))
  
  ;; Function template
  (register-lean-template "lean-function"
                         "def ~a : ~a :=\n  ~a"
                         '(name type body))

;; Process Lean template with parameters
(define (process-lean-template template-name parameters)
  (define template (hash-ref lean-template-registry template-name #f))
  (if template
      (let ([content (lean-template-content template)]
            [param-list (lean-template-parameters template)])
        (apply format content (map (λ (param) (hash-ref parameters param #f)) param-list)))
      (error (format "Lean template ~a not found" template-name))))

;; Main Lean generator using new architecture
(define (generate-lean-library-new-architecture output-dir)
  (define lib-dir (build-path output-dir "lib"))
  (make-directory* lib-dir)
  
  ;; Load Lean templates
  (load-lean-templates)
  
  ;; Get signature information
  (define sig (current-signature))
  (define sorts (signature-sorts sig))
  (define operations (signature-operations sig))
  (define constants (signature-constants sig))
  
  ;; Generate all modules
  (generate-lean-core-module lib-dir sorts operations constants)
  (generate-lean-observers-module lib-dir)
  (generate-lean-kernels-module lib-dir)
  (generate-lean-main-library output-dir)
  
  (displayln "✅ Lean library generated with new architecture!"))

;; Generate Lean core module
(define (generate-lean-core-module lib-dir sorts operations constants)
  (define core-file (build-path lib-dir "Core.lean"))
  
  ;; Format imports
  (define imports "import Mathlib.Data.Nat.Basic\nimport Mathlib.Data.String.Basic")
  
  ;; Generate sorts
  (define sort-constructors (map (λ (sort) (format "| ~a : Sort" sort)) sorts))
  (define sorts-content (process-lean-template "lean-sort-definition" 
                                               (hash 'constructors (string-join sort-constructors "\n"))))
  
  ;; Generate operations
  (define op-constructors (map format-lean-operation-constructor operations))
  (define operations-content (process-lean-template "lean-operation-definition"
                                                    (hash 'constructors (string-join op-constructors "\n"))))
  
  ;; Generate constants
  (define const-constructors (map format-lean-constant-constructor constants))
  (define constants-content (process-lean-template "lean-constant-definition"
                                                    (hash 'constructors (string-join const-constructors "\n"))))
  
  ;; Generate terms
  (define term-constructors (generate-lean-term-constructors sorts operations constants))
  (define terms-content (process-lean-template "lean-term-definition"
                                                (hash 'constructors (string-join term-constructors "\n"))))
  
  ;; Generate axioms
  (define axioms-content (generate-lean-axioms-content))
  
  ;; Combine all content
  (define content (string-join (list sorts-content operations-content constants-content 
                                     terms-content axioms-content) "\n\n"))
  
  ;; Generate final core module
  (define core-content (process-lean-template "lean-core-module"
                                              (hash 'imports imports
                                                    'content content)))
  
  (display-to-file core-content core-file #:exists 'replace))

;; Format Lean operation constructor
(define (format-lean-operation-constructor op)
  (define name (car op))
  (define type (cdr op))
  ;; Convert Unicode symbols to ASCII equivalents
  (define clean-name (string-replace (string-replace (string-replace (string-replace (symbol->string name) "⊕" "Plus") "⊗" "Mult") "ι" "Inject") "ν" "Project"))
  ;; Skip empty names
  (if (equal? clean-name "")
      ""
      (format "| ~a : Operation" clean-name)))

;; Format Lean constant constructor
(define (format-lean-constant-constructor const)
  (define name (car const))
  (define type (cdr const))
  ;; Convert Unicode symbols to ASCII equivalents
  (define clean-name (string-replace (string-replace (string-replace (symbol->string name) "⊕" "Plus") "⊗" "Mult") "ι" "Inject"))
  (format "| ~a : Constant" clean-name))

;; Generate Lean term constructors
(define (generate-lean-term-constructors sorts operations constants)
  (define constructors '())
  
  ;; Add constructors for each sort
  (for ([sort sorts])
    (set! constructors (append constructors (list (format "| Const~a : Constant → Term" sort)))))
  
  ;; Add operation constructors
  (for ([op operations])
    (define name (car op))
    (define clean-name (string-replace (string-replace (string-replace (string-replace (symbol->string name) "⊕" "Plus") "⊗" "Mult") "ι" "Inject") "ν" "Project"))
    (when (not (equal? clean-name ""))
      (set! constructors (append constructors (list (format "| Term~a : Term" clean-name))))))
  
  ;; Add Unit sort constructors
  (set! constructors (append constructors (list "| TermPlusU : Term → Term → Term")))
  (set! constructors (append constructors (list "| TermMultU : Term → Term → Term")))
  
  constructors)

;; Generate Lean axioms content
(define (generate-lean-axioms-content)
  (define axioms '())
  
  ;; Add basic semiring axioms
  (set! axioms (append axioms (list "axiom plusL_comm : ∀ x y : Term, TermPlusL x y = TermPlusL y x")))
  (set! axioms (append axioms (list "axiom plusL_assoc : ∀ x y z : Term, TermPlusL (TermPlusL x y) z = TermPlusL x (TermPlusL y z)")))
  (set! axioms (append axioms (list "axiom plusL_idempotent : ∀ x : Term, TermPlusL x x = x")))
  (set! axioms (append axioms (list "axiom plusL_zero : ∀ x : Term, TermPlusL (ConstL ZeroL) x = x")))
  
  (set! axioms (append axioms (list "axiom multL_comm : ∀ x y : Term, TermMultL x y = TermMultL y x")))
  (set! axioms (append axioms (list "axiom multL_assoc : ∀ x y z : Term, TermMultL (TermMultL x y) z = TermMultL x (TermMultL y z)")))
  (set! axioms (append axioms (list "axiom multL_idempotent : ∀ x : Term, TermMultL x x = x")))
  (set! axioms (append axioms (list "axiom multL_one : ∀ x : Term, TermMultL (ConstL OneL) x = x")))
  (set! axioms (append axioms (list "axiom multL_distrib : ∀ x y z : Term, TermMultL x (TermPlusL y z) = TermPlusL (TermMultL x y) (TermMultL x z)")))
  (set! axioms (append axioms (list "axiom multL_absorption : ∀ x y : Term, TermMultL x (TermPlusL x y) = x")))
  
  ;; Add Right axioms
  (set! axioms (append axioms (list "axiom plusR_comm : ∀ x y : Term, TermPlusR x y = TermPlusR y x")))
  (set! axioms (append axioms (list "axiom plusR_assoc : ∀ x y z : Term, TermPlusR (TermPlusR x y) z = TermPlusR x (TermPlusR y z)")))
  (set! axioms (append axioms (list "axiom plusR_idempotent : ∀ x : Term, TermPlusR x x = x")))
  (set! axioms (append axioms (list "axiom plusR_zero : ∀ x : Term, TermPlusR (ConstR ZeroR) x = x")))
  
  (set! axioms (append axioms (list "axiom multR_comm : ∀ x y : Term, TermMultR x y = TermMultR y x")))
  (set! axioms (append axioms (list "axiom multR_assoc : ∀ x y z : Term, TermMultR (TermMultR x y) z = TermMultR x (TermMultR y z)")))
  (set! axioms (append axioms (list "axiom multR_idempotent : ∀ x : Term, TermMultR x x = x")))
  (set! axioms (append axioms (list "axiom multR_one : ∀ x : Term, TermMultR (ConstR OneR) x = x")))
  (set! axioms (append axioms (list "axiom multR_distrib : ∀ x y z : Term, TermMultR x (TermPlusR y z) = TermPlusR (TermMultR x y) (TermMultR x z)")))
  (set! axioms (append axioms (list "axiom multR_absorption : ∀ x y : Term, TermMultR x (TermPlusR x y) = x")))
  
  ;; Add Bulk axioms
  (set! axioms (append axioms (list "axiom plusB_comm : ∀ x y : Term, TermPlusB x y = TermPlusB y x")))
  (set! axioms (append axioms (list "axiom plusB_assoc : ∀ x y z : Term, TermPlusB (TermPlusB x y) z = TermPlusB x (TermPlusB y z)")))
  (set! axioms (append axioms (list "axiom plusB_zero : ∀ x : Term, TermPlusB (ConstB ZeroB) x = x")))
  (set! axioms (append axioms (list "axiom plusB_annihilating : ∀ x : Term, TermPlusB x (ConstB ZeroB) = x")))
  
  (set! axioms (append axioms (list "axiom multB_comm : ∀ x y : Term, TermMultB x y = TermMultB y x")))
  (set! axioms (append axioms (list "axiom multB_assoc : ∀ x y z : Term, TermMultB (TermMultB x y) z = TermMultB x (TermMultB y z)")))
  (set! axioms (append axioms (list "axiom multB_one : ∀ x : Term, TermMultB (ConstB OneB) x = x")))
  (set! axioms (append axioms (list "axiom multB_distrib : ∀ x y z : Term, TermMultB x (TermPlusB y z) = TermPlusB (TermMultB x y) (TermMultB x z)")))
  
  ;; Add observer axioms
  (set! axioms (append axioms (list "axiom observer_retraction_L : ∀ x : Term, TermProjectL (TermInjectL x) = x")))
  (set! axioms (append axioms (list "axiom observer_retraction_R : ∀ x : Term, TermProjectR (TermInjectR x) = x")))
  
  ;; Add residual invisibility axiom
  (set! axioms (append axioms (list "axiom residual_invisibility : ∀ t : Term, let rho := TermPlusB (TermInjectL (TermProjectL t)) (TermInjectR (TermProjectR t)) in let residual := TermPlusB t rho in TermProjectL residual = ConstL ZeroL ∧ TermProjectR residual = ConstR ZeroR")))
  
  ;; Add basepoint normalization
  (set! axioms (append axioms (list "axiom basepoint_normalization : TermMultB (ConstB Phi) (ConstB BarPhi) = ConstB OneB")))
  
  ;; Add Unit sort axioms
  (set! axioms (append axioms (list "axiom unit_comm : ∀ x y : Term, TermPlusU x y = TermPlusU y x")))
  (set! axioms (append axioms (list "axiom unit_assoc : ∀ x y z : Term, TermPlusU (TermPlusU x y) z = TermPlusU x (TermPlusU y z)")))
  (set! axioms (append axioms (list "axiom unit_zero : ∀ x : Term, TermPlusU (ConstI ZeroU) x = x")))
  (set! axioms (append axioms (list "axiom unit_mult_comm : ∀ x y : Term, TermMultU x y = TermMultU y x")))
  (set! axioms (append axioms (list "axiom unit_mult_assoc : ∀ x y z : Term, TermMultU (TermMultU x y) z = TermMultU x (TermMultU y z)")))
  (set! axioms (append axioms (list "axiom unit_mult_one : ∀ x : Term, TermMultU (ConstI OneU) x = x")))
  (set! axioms (append axioms (list "axiom unit_mult_distrib : ∀ x y z : Term, TermMultU x (TermPlusU y z) = TermPlusU (TermMultU x y) (TermMultU x z)")))
  
  (string-join axioms "\n"))

;; Generate Lean observers module
(define (generate-lean-observers-module lib-dir)
  (define observers-file (build-path lib-dir "Observers.lean"))
  
  (define observer-functions (list
                             (process-lean-template "lean-function"
                                                    (hash 'name "project_L"
                                                          'type "Term → Term"
                                                          'body "λ t => ConstL ZeroL"))
                             (process-lean-template "lean-function"
                                                    (hash 'name "project_R"
                                                          'type "Term → Term"
                                                          'body "λ t => ConstR ZeroR"))
                             (process-lean-template "lean-function"
                                                    (hash 'name "inject_L"
                                                          'type "Term → Term"
                                                          'body "λ t => ConstB ZeroB"))
                             (process-lean-template "lean-function"
                                                    (hash 'name "inject_R"
                                                          'type "Term → Term"
                                                          'body "λ t => ConstB ZeroB"))
                             (process-lean-template "lean-function"
                                                    (hash 'name "reconstitute"
                                                          'type "Term → Term → Term"
                                                          'body "λ l r => TermPlusB (TermInjectL l) (TermInjectR r)"))
                             (process-lean-template "lean-function"
                                                    (hash 'name "residual"
                                                          'type "Term → Term"
                                                          'body "λ t => TermPlusB t (TermPlusB (TermInjectL (TermProjectL t)) (TermInjectR (TermProjectR t)))"))))
  
  (define content (string-join observer-functions "\n\n"))
  (display-to-file content observers-file #:exists 'replace))

;; Generate Lean kernels module
(define (generate-lean-kernels-module lib-dir)
  (define kernels-file (build-path lib-dir "Kernels.lean"))
  
  (define kernel-functions (list
                          (process-lean-template "lean-function"
                                                 (hash 'name "kernel_compose"
                                                       'type "Kernel → Kernel → Kernel"
                                                       'body "λ k1 k2 => k1"))
                          (process-lean-template "lean-function"
                                                 (hash 'name "kernel_apply"
                                                       'type "Kernel → Term → Term"
                                                       'body "λ k t => t"))
                          (process-lean-template "lean-function"
                                                 (hash 'name "kernel_identity"
                                                       'type "Kernel"
                                                       'body "λ t => t"))))
  
  (define content (string-join kernel-functions "\n\n"))
  (display-to-file content kernels-file #:exists 'replace))

;; Generate Lean main library
(define (generate-lean-main-library output-dir)
  (define main-file (build-path output-dir "CLEAN.lean"))
  
  ;; Read generated modules
  (define lib-dir (build-path output-dir "lib"))
  (define core-content (file->string (build-path lib-dir "Core.lean")))
  (define observers-content (file->string (build-path lib-dir "Observers.lean")))
  (define kernels-content (file->string (build-path lib-dir "Kernels.lean")))
  
  ;; Generate main library
  (define main-content (string-join (list
                                    "import Core"
                                    "import Observers"
                                    "import Kernels"
                                    ""
                                    "-- CLEAN v10 Lean Library - Generated with New Architecture"
                                    ""
                                    "-- Convenience Definitions"
                                    "def CLEAN_Sort : Type := Sort"
                                    "def CLEAN_Operation : Type := Operation"
                                    "def CLEAN_Constant : Type := Constant"
                                    "def CLEAN_Term : Type := Term"
                                    ""
                                    "-- Core operations"
                                    "def CLEAN_PlusL : Term → Term → Term := TermPlusL"
                                    "def CLEAN_MultL : Term → Term → Term := TermMultL"
                                    "def CLEAN_PlusR : Term → Term → Term := TermPlusR"
                                    "def CLEAN_MultR : Term → Term → Term := TermMultR"
                                    "def CLEAN_PlusB : Term → Term → Term := TermPlusB"
                                    "def CLEAN_MultB : Term → Term → Term := TermMultB"
                                    "def CLEAN_PlusU : Term → Term → Term := TermPlusU"
                                    "def CLEAN_MultU : Term → Term → Term := TermMultU"
                                    ""
                                    "-- Observer functions"
                                    "def CLEAN_ProjectL : Term → Term := project_L"
                                    "def CLEAN_ProjectR : Term → Term := project_R"
                                    "def CLEAN_InjectL : Term → Term := inject_L"
                                    "def CLEAN_InjectR : Term → Term := inject_R"
                                    "def CLEAN_Reconstitute : Term → Term → Term := reconstitute"
                                    "def CLEAN_Residual : Term → Term := residual"
                                    ""
                                    "-- Kernel functions"
                                    "def CLEAN_KernelCompose : Kernel → Kernel → Kernel := kernel_compose"
                                    "def CLEAN_KernelApply : Kernel → Term → Term := kernel_apply"
                                    "def CLEAN_IdentityKernel : Kernel := kernel_identity")
                                   "\n"))
  
  (display-to-file main-content main-file #:exists 'replace))

;; ============================================================================
;; MAIN EXECUTION
;; ============================================================================

(module+ main
  (displayln "Phase 3: Agda and Lean Generators with New Architecture")
  (displayln "")
  
  (displayln "Generating Agda library...")
  (generate-agda-library-new-architecture "agda-new-architecture-output")
  (displayln "")
  
  (displayln "Generating Lean library...")
  (generate-lean-library-new-architecture "lean-new-architecture-output")
  (displayln "")
  
  (displayln "Generated files:")
  (displayln "  - agda-new-architecture-output/lib/Core.agda")
  (displayln "  - agda-new-architecture-output/lib/Observers.agda")
  (displayln "  - agda-new-architecture-output/lib/Kernels.agda")
  (displayln "  - agda-new-architecture-output/CLEAN.agda")
  (displayln "  - lean-new-architecture-output/lib/Core.lean")
  (displayln "  - lean-new-architecture-output/lib/Observers.lean")
  (displayln "  - lean-new-architecture-output/lib/Kernels.lean")
  (displayln "  - lean-new-architecture-output/CLEAN.lean"))
