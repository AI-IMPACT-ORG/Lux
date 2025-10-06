#lang racket

;; @logic/gen Language Reader
;; Provides #lang logic/gen surface syntax that expands to Core/CLASS calls

(require syntax/parse/define
         syntax/parse/lib/function-header
         racket/contract
         racket/match)

(provide (all-defined-out))

;; ============================================================================
;; GENERATOR DATA MODEL
;; ============================================================================

;; Generator struct: function with metadata
(struct gen (apply meta) #:transparent
  #:contract (struct/c gen (-> any/c any/c) hash?))

;; Generator metadata
(define (make-gen-meta tag laws . rest)
  (apply hash 'tag tag 'laws laws rest))

;; Identity generator
(define (gen-id)
  (gen identity (make-gen-meta 'identity '(associativity identity))))

;; Generator composition
(define (gen-compose g1 g2)
  (gen (compose (gen-apply g2) (gen-apply g1))
       (hash-union (make-gen-meta g1) (make-gen-meta g2))))

;; Generator application
(define (gen-apply g x)
  ((gen-apply g) x))

;; ============================================================================
;; SURFACE FORMS - KERNEL GENERATORS
;; ============================================================================

(define-syntax-parse-rule (define-kernel name:id expr:expr)
  #:with kernel-name (format-id #'name "~a-kernel" #'name)
  #'(begin
      (define kernel-name (gen expr (make-gen-meta 'kernel '(composition))))
      (define name kernel-name)))

(define-syntax-parse-rule (gen-compose g1:expr g2:expr)
  #'(gen-compose g1 g2))

(define-syntax-parse-rule (greens-sum K:expr #:N N:expr)
  #'(greens-sum-generator K N))

(define-syntax-parse-rule (rg-block K:expr #:k k:expr)
  #'(rg-block-generator K k))

(define-syntax-parse-rule (transition T1:expr T2:expr)
  #'(transition-compose T1 T2))

;; ============================================================================
;; SURFACE FORMS - NORMAL FORM GENERATORS
;; ============================================================================

(define-syntax-parse-rule (NF t:expr)
  #'(normal-form t))

(define-syntax-parse-rule (NF/param t:expr 
                                  #:μL μL:expr 
                                  #:θL θL:expr 
                                  #:μR μR:expr 
                                  #:θR θR:expr)
  #'(normal-form-parametric t μL θL μR θR))

(define-syntax-parse-rule (flow #:μL fμL:expr 
                                #:θL fθL:expr 
                                #:μR fμR:expr 
                                #:θR fθR:expr)
  #'(make-flow fμL fθL fμR fθR))

(define-syntax-parse-rule (evolve-header t:expr flow:expr)
  #'(header-evolve t flow))

(define-syntax-parse-rule (transform-core t:expr f_core:expr)
  #'(core-transform t f_core))

;; ============================================================================
;; SURFACE FORMS - OBSERVER GENERATORS
;; ============================================================================

(define-syntax-parse-rule (project side:expr t:expr)
  #'(case side
      ['L (projector-L t)]
      ['R (projector-R t)]
      [else (error 'project "unknown side: ~a" side)]))

(define-syntax-parse-rule (reconstitute t:expr)
  #'(reconstitute t))

(define-syntax-parse-rule (residual t:expr)
  #'(residual t))

;; ============================================================================
;; SURFACE FORMS - CLASS GENERATORS
;; ============================================================================

(define-syntax-parse-rule (port domain:expr)
  #'(case domain
      ['boolean (make-boolean-port)]
      ['lambda (make-lambda-port)]
      ['info (make-infoflow-port)]
      ['qft (make-qft-port)]
      [else (error 'port "unknown domain: ~a" domain)]))

(define-syntax-parse-rule (psdm-apply port:expr t:expr)
  #'(domain-port-eval port t))

(define-syntax-parse-rule (psdm-defined? port:expr t:expr)
  #'((domain-port-totality-predicate port) t))

(define-syntax-parse-rule (histories J:expr)
  #'(feynman-histories J))

(define-syntax-parse-rule (sum-over-histories J:expr)
  #'(feynman-sum J))

;; ============================================================================
;; SURFACE FORMS - TRUTH LANGUAGE
;; ============================================================================

(define-syntax-parse-rule (check-invariant invariant:expr t:expr)
  #'(case invariant
      ['bulk=boundaries (bulk-equals-boundaries? t)]
      ['residual-invisible (test-residual-invisibility t)]
      [else (error 'check-invariant "unknown invariant: ~a" invariant)]))

(define-syntax-parse-rule (check-law law:expr K:expr)
  #'(case law
      ['rg-closure (test-rg-closure K)]
      [else (error 'check-law "unknown law: ~a" law)]))

(define-syntax-parse-rule (check-theorem theorem:expr . args:expr)
  #'(case theorem
      ['church-turing (church-turing-agree? . args)]
      ['eor-health (eor-health?)]
      ['logic-grh-gate (logic-grh-gate?)]
      [else (error 'check-theorem "unknown theorem: ~a" theorem)]))

;; ============================================================================
;; IMPLEMENTATION STUBS (to be connected to Core/CLASS)
;; ============================================================================

;; These will be replaced with actual Core/CLASS function calls
(define (greens-sum-generator K N)
  (error 'greens-sum-generator "implement using Core kernel-compose"))

(define (rg-block-generator K k)
  (error 'rg-block-generator "implement using Core rg-block"))

(define (transition-compose T1 T2)
  (error 'transition-compose "implement using Core transition-compose"))

(define (normal-form t)
  (error 'normal-form "implement using Core normal-form"))

(define (normal-form-parametric t μL θL μR θR)
  (error 'normal-form-parametric "implement using Core normal-form-parametric"))

(define (make-flow fμL fθL fμR fθR)
  (error 'make-flow "implement using Class moduli flows"))

(define (header-evolve t flow)
  (error 'header-evolve "implement using Class flow evolution"))

(define (core-transform t f_core)
  (error 'core-transform "implement with Core transformation"))

(define (projector-L t)
  (error 'projector-L "implement using Core observers"))

(define (projector-R t)
  (error 'projector-R "implement using Core observers"))

(define (reconstitute t)
  (error 'reconstitute "implement using Core reconstitute"))

(define (residual t)
  (error 'residual "implement using Core residual"))

(define (make-boolean-port)
  (error 'make-boolean-port "implement using Class domain ports"))

(define (make-lambda-port)
  (error 'make-lambda-port "implement using Class domain ports"))

(define (make-infoflow-port)
  (error 'make-infoflow-port "implement using Class domain ports"))

(define (make-qft-port)
  (error 'make-qft-port "implement using Class domain ports"))

(define (domain-port-eval port t)
  (error 'domain-port-eval "implement using Class domain ports"))

(define (domain-port-totality-predicate port)
  (error 'domain-port-totality-predicate "implement using Class domain ports"))

(define (feynman-histories J)
  (error 'feynman-histories "implement using Class Feynman"))

(define (feynman-sum J)
  (error 'feynman-sum "implement using Class Feynman"))

(define (bulk-equals-boundaries? t)
  (error 'bulk-equals-boundaries? "implement using Core observers"))

(define (test-residual-invisibility t)
  (error 'test-residual-invisibility "implement using Core observers"))

(define (test-rg-closure K)
  (error 'test-rg-closure "implement using Core RG"))

(define (church-turing-agree? prog input)
  (error 'church-turing-agree? "implement using Class truth theorems"))

(define (eor-health?)
  (error 'eor-health? "implement using Class truth theorems"))

(define (logic-grh-gate?)
  (error 'logic-grh-gate? "implement using Class truth theorems"))

