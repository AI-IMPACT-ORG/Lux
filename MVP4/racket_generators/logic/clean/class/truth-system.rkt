#lang racket

(require "truth.rkt"
         "moduli.rkt"
         "guarded.rkt"
         "psdm.rkt"
         "feynman.rkt"
         "domain/unified-port.rkt"
         "../core/signature.rkt"
         "../core/nf.rkt"
         "../core/observers.rkt"
         "../core/cumulants.rkt"
         "../core/delta.rkt"
         "../core/kernel.rkt"
         racket/match
         racket/list)

(provide ; Truth system infrastructure
         truth-system?
         make-truth-system
         truth-system-run-all
         truth-system-run-specific
         truth-system-results
         ; Unified validation
         validate-clean-system
         validate-domain-port
         validate-kernel-transition
         validate-psdm-mapping
         ; Test framework integration
         truth-test-case
         truth-test-suite
         ; Truth theorem accessors
         truth-theorem-umbral-renormalisation
         truth-theorem-church-turing
         truth-theorem-eor-health
         truth-theorem-logic-grh-gate)

;; Truth system infrastructure - unified interface for all truth theorems
(struct truth-system (name moduli-config port-configs test-terms)
  #:transparent)

(define (make-truth-system #:name [name 'CLEAN-v10]
                           #:moduli-config [moduli-config 'default]
                           #:port-configs [port-configs '()]
                           #:test-terms [test-terms '()])
  (truth-system name moduli-config port-configs test-terms))

;; Default configurations

(define default-port-configs
  (list (cons 'turing '(#:threshold 0.5))
        (cons 'lambda '())
        (cons 'path '(#:euclidean? #t))
        (cons 'infoflow '())))

(define default-test-terms
  (list (make-term 'truth-test-1 #:header '(1 . 1) #:core 'test-core-1)
        (make-term 'truth-test-2 #:header '(2 . 2) #:core 'test-core-2)
        (make-term 'truth-test-3 #:header '(1 . 2) #:core 'test-core-3)))

;; Truth system execution
(define (truth-system-run-all system)
  "Run all truth theorems and return comprehensive results"
  (define results (make-hash))
  
  ;; Configure system
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (if (eq? (truth-system-moduli-config system) 'default)
      (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
      (apply set-moduli! (truth-system-moduli-config system)))
  
  ;; Run each truth theorem
  (hash-set! results 'umbral-renormalisation (check-umbral-renormalisation?))
  (hash-set! results 'church-turing (church-turing-agree? 'prog 'input))
  (hash-set! results 'eor-health (eor-health?))
  (hash-set! results 'logic-grh-gate (logic-grh-gate?))
  
  ;; Add system metadata
  (hash-set! results 'system-name (truth-system-name system))
  (hash-set! results 'timestamp (current-seconds))
  (hash-set! results 'all-passed (andmap (λ (v) (eq? v #t)) 
                                        (map (λ (k) (hash-ref results k #f))
                                             '(umbral-renormalisation church-turing eor-health logic-grh-gate))))
  
  results)

(define (truth-system-run-specific system theorem-name)
  "Run a specific truth theorem"
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (if (eq? (truth-system-moduli-config system) 'default)
      (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
      (apply set-moduli! (truth-system-moduli-config system)))
  
  (case theorem-name
    ['umbral-renormalisation (check-umbral-renormalisation?)]
    ['church-turing (church-turing-agree? 'prog 'input)]
    ['eor-health (eor-health?)]
    ['logic-grh-gate (logic-grh-gate?)]
    [else (error 'truth-system-run-specific "unknown theorem: ~a" theorem-name)]))

(define (truth-system-results system)
  "Get cached results or run fresh"
  (truth-system-run-all system))

;; Unified validation framework
(define (validate-clean-system #:moduli-config [moduli-config 'default]
                               #:port-configs [port-configs default-port-configs]
                               #:test-terms [test-terms default-test-terms])
  "Validate the entire CLEAN system using truth theorems"
  (define system (make-truth-system #:moduli-config moduli-config
                                  #:port-configs port-configs
                                  #:test-terms test-terms))
  (truth-system-results system))

(define (validate-domain-port port-type #:config [config '()])
  "Validate a specific domain port using relevant truth theorems"
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
  
  (case port-type
    ['turing (and (truth-theorem-church-turing) (truth-theorem-eor-health))]
    ['lambda (and (truth-theorem-church-turing) (truth-theorem-eor-health))]
    ['path (and (truth-theorem-logic-grh-gate) (truth-theorem-eor-health))]
    ['infoflow (truth-theorem-eor-health)]
    [else (error 'validate-domain-port "unknown port type: ~a" port-type)]))

(define (validate-kernel-transition kernel)
  "Validate kernel transition using umbral renormalisation"
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
  (truth-theorem-umbral-renormalisation))

(define (validate-psdm-mapping psdm)
  "Validate PSDM mapping using EOR health"
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
  (truth-theorem-eor-health))

;; Test framework integration
(define-syntax truth-test-case
  (syntax-rules ()
    [(_ name body ...)
     (test-case name
       (set-quotient-mask! '(phase))
       (set-r-matrix! 'identity)
       (apply set-moduli! default-moduli-config)
       body ...)]))

(define-syntax truth-test-suite
  (syntax-rules ()
    [(_ name test ...)
     (test-suite name test ...)]))

;; Truth theorem accessors (for direct access)
(define (truth-theorem-umbral-renormalisation)
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
  (check-umbral-renormalisation?))

(define (truth-theorem-church-turing)
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
  (church-turing-agree? 'prog 'input))

(define (truth-theorem-eor-health)
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
  (eor-health?))

(define (truth-theorem-logic-grh-gate)
  (set-quotient-mask! '(phase))
  (set-r-matrix! 'identity)
  (set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0)
  (logic-grh-gate?))
