#lang racket

;; Minimal API that only provides functions that actually exist
(require "clean/core/signature.rkt"
         "clean/core/kernel.rkt"
         "clean/core/nf.rkt"
         "clean/core/observers.rkt"
         "clean/core/cumulants.rkt"
         "clean/core/header.rkt"
         "clean/class/feynman.rkt"
         "clean/class/psdm.rkt"
         "clean/class/domain/unified-port.rkt"
         "clean/class/domain/institution-port.rkt")

(provide ; Core functions that actually exist
         signature?
         signature-sorts
         signature-operations
         signature-constants
         current-signature
         set-current-signature!
         default-signature
         make-term
         term?
         term-name
         term-header
         term-core
         term-left
         term-right
         term-metadata
         set-quotient-mask!
         current-quotient-mask
         set-r-matrix!
         current-r-matrix
         ; Kernel functions
         kernel?
         kernel-header
         kernel-transition
         kernel-compose
         kernel-header-add
         kernel-header-product
         kernel-header-zero
         kernel-apply
         identity-kernel
         ; Header functions
         header?
         header-phase
         header-scale
         header-add
         header-multiply
         header-negate
         header-inverse
         header-norm
         header-distance
         header-zero
         header-equal?
         ; Transition functions
         transition?
         transition-compose
         ; Normal form functions
         nf?
         nf-phase
         nf-scale
         nf-core
         normal-form
         ; Observer functions
         observer-value
         reconstitute
         residual
         bulk-equals-boundaries?
         ; Cumulant functions
         clear-observables!
         register-observable
         kernel-generating-functional
         kernel-cumulants
         value-g
         value-G
         value-beta-mu
         value-beta-theta
         value-a
         value-c
         ; Feynman functions
         sum-over-histories
         greens-sum
         schwinger-dyson
         ; PSDM functions
         psdm-legacy?
         psdm-extend
         psdm-define
         psdm-lookup
        define-psdm!
        psdm-apply
        psdm-defined?
         make-psdm-legacy
         ; Domain port functions
         make-domain-port
         domain-port-eval
         domain-port-kernel
         domain-port-carrier
         domain-port-totality-predicate
         domain-port-q-vector
         domain-port?
         make-turing-port
         make-lambda-port
         make-path-port
         make-infoflow-port
         make-boolean-port
         make-qft-port
         ; Institution functions
         institution?
         make-institution
         inst-signature
         inst-models
         inst-sentences
         inst-satisfaction
         ; RG functions
         rg-block
         rg-flow
         rg-critical-line?
         ; Property-based testing
         random-header
         run-property-tests
         ; Invariant testing
         test-residual-invisibility
         test-triality-involution
         test-boundary-sum
         test-rg-closure)
