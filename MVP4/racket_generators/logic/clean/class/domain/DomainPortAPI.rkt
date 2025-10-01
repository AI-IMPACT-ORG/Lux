#lang racket

;; DomainPortAPI - Clean interface between core logic and domain applications
;; This creates a layered architecture (onion style) with proper domain boundaries

(require "../../core/signature.rkt"
         "../../core/kernel.rkt"
         "../../core/nf.rkt"
         "../../core/observers.rkt"
         "../../core/cumulants.rkt"
         "../../core/header.rkt"
         "../feynman.rkt"
         "../psdm.rkt")

(provide ; Core Domain Interface (Layer 1 - Innermost)
         ; Transition operations
         domain-transition
         domain-transition?
         domain-transition-carrier
         domain-transition-step-weight
         domain-transition-event-sequence
         
         ; Term operations
         make-domain-term
         domain-term?
         domain-term-name
         domain-term-header
         domain-term-core
         domain-term-left
         domain-term-right
         domain-term-metadata
         
         ; Kernel operations
         make-domain-kernel
         domain-kernel?
         domain-kernel-header
         domain-kernel-transition
         domain-kernel-compose
         domain-kernel-apply
         
         ; Header operations
         make-domain-header
         domain-header?
         domain-header-phase
         domain-header-scale
         domain-header-add
         domain-header-multiply
         domain-header-equal?
         
         ; Normal form operations
         domain-normal-form
         domain-normal-form?
         domain-nf-phase
         domain-nf-scale
         domain-nf-core
         
         ; Observer operations
         domain-observer-value
         domain-reconstitute
         domain-residual
         domain-bulk-equals-boundaries?
         
         ; Cumulant operations
         domain-clear-observables!
         domain-register-observable
         domain-kernel-generating-functional
         domain-kernel-cumulants
         
         ; Feynman operations
         domain-sum-over-histories
         domain-greens-sum
         domain-schwinger-dyson
         
         ; PSDM operations
         domain-make-psdm
         domain-psdm?
         domain-psdm-apply
         
         ; RG operations
         domain-rg-block
         domain-rg-flow
         domain-rg-critical-line?
         
         ; Property-based testing
         domain-random-header
         domain-run-property-tests
         
         ; Invariant testing
         domain-test-residual-invisibility
         domain-test-triality-involution
         domain-test-boundary-sum
         domain-test-rg-closure)

;; ===== LAYER 1: CORE DOMAIN INTERFACE =====
;; This layer provides a clean, stable interface to core CLEAN v10 functionality
;; Domain applications should only use these functions, never the core modules directly

;; Transition operations
(define domain-transition transition)
(define domain-transition? transition?)
(define domain-transition-carrier transition-carrier)
(define domain-transition-step-weight transition-step-weight)
(define domain-transition-event-sequence transition-event-sequence)

;; Term operations
(define (make-domain-term name #:header [header (header 0.0 0.0)] #:core [core '()] 
                         #:left [left #f] #:right [right #f] #:metadata [metadata #f])
  (make-term name #:header header #:core core #:left left #:right right #:metadata metadata))

(define domain-term? term?)
(define domain-term-name term-name)
(define domain-term-header term-header)
(define domain-term-core term-core)
(define domain-term-left term-left)
(define domain-term-right term-right)
(define domain-term-metadata term-metadata)

;; Kernel operations
(define (make-domain-kernel header transition)
  (kernel header transition))

(define domain-kernel? kernel?)
(define domain-kernel-header kernel-header)
(define domain-kernel-transition kernel-transition)
(define domain-kernel-compose kernel-compose)
(define domain-kernel-apply kernel-apply)

;; Header operations
(define (make-domain-header phase scale)
  (header phase scale))

(define domain-header? header?)
(define domain-header-phase header-phase)
(define domain-header-scale header-scale)
(define domain-header-add header-add)
(define domain-header-multiply header-multiply)
(define domain-header-equal? header-equal?)

;; Normal form operations
(define domain-normal-form normal-form)
(define domain-normal-form? nf?)
(define domain-nf-phase nf-phase)
(define domain-nf-scale nf-scale)
(define domain-nf-core nf-core)

;; Observer operations
(define domain-observer-value observer-value)
(define domain-reconstitute reconstitute)
(define domain-residual residual)
(define domain-bulk-equals-boundaries? bulk-equals-boundaries?)

;; Cumulant operations
(define domain-clear-observables! clear-observables!)
(define domain-register-observable register-observable)
(define domain-kernel-generating-functional kernel-generating-functional)
(define domain-kernel-cumulants kernel-cumulants)

;; Feynman operations
(define domain-sum-over-histories sum-over-histories)
(define domain-greens-sum greens-sum)
(define domain-schwinger-dyson schwinger-dyson)

;; PSDM operations
(define domain-make-psdm make-psdm-legacy)
(define domain-psdm? psdm-legacy?)
(define domain-psdm-apply psdm-apply)

;; RG operations
(define domain-rg-block rg-block)
(define domain-rg-flow rg-flow)
(define domain-rg-critical-line? rg-critical-line?)

;; Property-based testing
(define domain-random-header random-header)
(define domain-run-property-tests run-property-tests)

;; Invariant testing
(define domain-test-residual-invisibility test-residual-invisibility)
(define domain-test-triality-involution test-triality-involution)
(define domain-test-boundary-sum test-boundary-sum)
(define domain-test-rg-closure test-rg-closure)
