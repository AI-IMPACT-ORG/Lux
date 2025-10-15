#lang racket

(require "../../core/signature.rkt"
         "../../core/kernel.rkt"
         "../../core/nf.rkt"
         "../truth.rkt"
         "../truth-system.rkt")

(provide ; Institution structure
         institution?
         make-institution
         inst-signature
         inst-models
         inst-sentences
         inst-satisfaction
         ; Institution constructors for each domain
         make-turing-institution
         make-lambda-institution
         make-path-institution
         make-infoflow-institution
         ; Institution evaluation
         institution-satisfies?
         institution-model-of?
         institution-sentence-holds?
         ; Truth theorem access
         institution-truth-theorems
         institution-verify-truths
         ; Explicit institutional components
         institution-carrier
         institution-q-vector
         institution-kernel
         institution-totality-predicate
         institution-transition-function
         institution-regulator-predicate)

;; Institution structure - explicit institutional components
(struct institution (signature models sentences satisfaction)
  #:transparent)

;; Institution signature components
(struct inst-signature (carrier q-vector sorts operations constants)
  #:transparent)

;; Institution models (domain ports as models)
(struct inst-models (kernel transition-function totality-predicate regulator-predicate)
  #:transparent)

;; Institution sentences (truth theorems)
(struct inst-sentences (truth-theorems verification-functions)
  #:transparent)

;; Institution satisfaction relation
(struct inst-satisfaction (evaluation-function satisfaction-predicate)
  #:transparent)

;; Institution constructor
(define (make-institution signature models sentences satisfaction)
  (institution signature models sentences satisfaction))

;; Institution evaluation - explicit satisfaction checking
(define (institution-satisfies? institution term sentence)
  "Check if a term satisfies a sentence in the institution"
  (unless (institution? institution)
    (error 'institution-satisfies? "expected institution, got ~a" institution))
  (unless (term? term)
    (error 'institution-satisfies? "expected term, got ~a" term))
  
  (define satisfaction-fn (inst-satisfaction-satisfaction-predicate 
                           (inst-satisfaction institution)))
  (satisfaction-fn term sentence))

(define (institution-model-of? institution term)
  "Check if a term is a model in the institution"
  (unless (institution? institution)
    (error 'institution-model-of? "expected institution, got ~a" institution))
  
  (define totality-pred (inst-models-totality-predicate 
                        (inst-models institution)))
  (totality-pred term))

(define (institution-sentence-holds? institution sentence)
  "Check if a sentence holds in the institution"
  (unless (institution? institution)
    (error 'institution-sentence-holds? "expected institution, got ~a" institution))
  
  (define verification-fns (inst-sentences-verification-functions 
                           (inst-sentences institution)))
  (if (hash-has-key? verification-fns sentence)
      ((hash-ref verification-fns sentence))
      #f))

;; Accessor functions for institutional components
(define (institution-carrier institution)
  (inst-signature-carrier (institution-signature institution)))

(define (institution-q-vector institution)
  (inst-signature-q-vector (institution-signature institution)))

(define (institution-kernel institution)
  (inst-models-kernel (institution-models institution)))

(define (institution-totality-predicate institution)
  (inst-models-totality-predicate (institution-models institution)))

(define (institution-transition-function institution)
  (inst-models-transition-function (institution-models institution)))

(define (institution-regulator-predicate institution)
  (inst-models-regulator-predicate (institution-models institution)))

;; Truth theorem access
(define (institution-truth-theorems institution)
  (inst-sentences-truth-theorems (institution-sentences institution)))

(define (institution-verify-truths institution)
  "Verify all truth theorems for the institution"
  (unless (institution? institution)
    (error 'institution-verify-truths "expected institution, got ~a" institution))
  
  (define verification-fns (inst-sentences-verification-functions 
                           (inst-sentences institution)))
  (for/hash ([truth-name (hash-keys verification-fns)])
    (values truth-name ((hash-ref verification-fns truth-name)))))

;; Institution constructors for each domain - explicit institutional structure

;; Turing Institution: q=(1,0,0) - Classical computation, deterministic models
(define (make-turing-institution #:threshold [threshold 0.5])
  (define carrier 'turing)
  (define q-vector '(1 0 0))
  (define sorts '(term boolean))
  (define operations '(eval threshold))
  (define constants '(true false))
  
  (define signature (inst-signature carrier q-vector sorts operations constants))
  
  (define turing-kernel (kernel kernel-header-zero 
                        (transition 'turing 
                                   (λ (term) term)  ; Pure renaming
                                   '())))
  (define transition-fn (λ (term) term))
  (define totality-pred (λ (term) #t))  ; Always defined for deterministic computation
  (define regulator-pred (λ (term) 
                          (and (term? term)
                               (not (eq? (term-metadata term) 'non-halting))
                               (not (eq? (term-metadata term) 'infinite-loop)))))
  
  (define models (inst-models turing-kernel transition-fn totality-pred regulator-pred))
  
  ;; Truth theorems for Turing institution
  (define truth-theorems '(umbral-renormalisation church-turing eor-health))
  (define verification-fns (hash 'umbral-renormalisation check-umbral-renormalisation?
                                 'church-turing (λ () (church-turing-agree? 'prog 'input))
                                 'eor-health eor-health?))
  
  (define sentences (inst-sentences truth-theorems verification-fns))
  
  (define eval-fn (λ (term) (kernel-apply kernel term)))
  (define satisfaction-pred (λ (term sentence) 
                             (case sentence
                               ['halting (regulator-pred term)]
                               ['defined (totality-pred term)]
                               [else #f])))
  
  (define satisfaction (inst-satisfaction eval-fn satisfaction-pred))
  
  (make-institution signature models sentences satisfaction))

;; Lambda Institution: q=(0,1,0) - Quantum computation, probabilistic models
(define (make-lambda-institution)
  (define carrier 'lambda)
  (define q-vector '(0 1 0))
  (define sorts '(term lambda-value))
  (define operations '(normalize apply))
  (define constants '(lambda-identity))
  
  (define signature (inst-signature carrier q-vector sorts operations constants))
  
  (define lambda-kernel (kernel kernel-header-zero
                        (transition 'lambda
                                   (λ (term) term)  ; Pure renaming
                                   '())))
  (define transition-fn (λ (term) term))
  (define totality-pred (λ (term) (halts-within-regulator? term)))
  (define regulator-pred (λ (term) 
                          (and (term? term)
                               (not (eq? (term-metadata term) 'non-halting))
                               (not (eq? (term-metadata term) 'infinite-loop)))))
  
  (define models (inst-models lambda-kernel transition-fn totality-pred regulator-pred))
  
  ;; Truth theorems for Lambda institution
  (define truth-theorems '(umbral-renormalisation church-turing eor-health))
  (define verification-fns (hash 'umbral-renormalisation check-umbral-renormalisation?
                                 'church-turing (λ () (church-turing-agree? 'prog 'input))
                                 'eor-health eor-health?))
  
  (define sentences (inst-sentences truth-theorems verification-fns))
  
  (define eval-fn (λ (term) (kernel-apply kernel term)))
  (define satisfaction-pred (λ (term sentence) 
                             (case sentence
                               ['normalizing (regulator-pred term)]
                               ['defined (totality-pred term)]
                               [else #f])))
  
  (define satisfaction (inst-satisfaction eval-fn satisfaction-pred))
  
  (make-institution signature models sentences satisfaction))

;; Path Institution: q=(0,0,1) - Stochastic computation, Feynman paths
(define (make-path-institution #:euclidean? [euclidean? #t])
  (define carrier (if euclidean? 'euclidean 'minkowski))
  (define q-vector '(0 0 1))
  (define sorts '(term path-value))
  (define operations '(integrate weight))
  (define constants '(path-identity))
  
  (define signature (inst-signature carrier q-vector sorts operations constants))
  
  (define path-kernel (kernel kernel-header-zero
                        (transition carrier
                                   (λ (term) term)  ; Pure renaming
                                   '())))
  (define transition-fn (λ (term) term))
  (define totality-pred (λ (term) (converges-within-regulator? term)))
  (define regulator-pred (λ (term) 
                          (and (term? term)
                               (not (eq? (term-metadata term) 'non-converging))
                               (not (eq? (term-metadata term) 'divergent)))))
  
  (define models (inst-models path-kernel transition-fn totality-pred regulator-pred))
  
  ;; Truth theorems for Path institution
  (define truth-theorems '(umbral-renormalisation eor-health logic-grh-gate))
  (define verification-fns (hash 'umbral-renormalisation check-umbral-renormalisation?
                                 'eor-health eor-health?
                                 'logic-grh-gate logic-grh-gate?))
  
  (define sentences (inst-sentences truth-theorems verification-fns))
  
  (define eval-fn (λ (term) (kernel-apply kernel term)))
  (define satisfaction-pred (λ (term sentence) 
                             (case sentence
                               ['converging (regulator-pred term)]
                               ['defined (totality-pred term)]
                               [else #f])))
  
  (define satisfaction (inst-satisfaction eval-fn satisfaction-pred))
  
  (make-institution signature models sentences satisfaction))

;; Infoflow Institution: Information measures, Fisher metric
(define (make-infoflow-institution)
  (define carrier 'infoflow)
  (define q-vector '(0 0 0))
  (define sorts '(term flow-value))
  (define operations '(format measure))
  (define constants '(flow-identity))
  
  (define signature (inst-signature carrier q-vector sorts operations constants))
  
  (define infoflow-kernel (kernel kernel-header-zero
                        (transition 'infoflow
                                   (λ (term) term)  ; Pure renaming
                                   '())))
  (define transition-fn (λ (term) term))
  (define totality-pred (λ (term) (flows-within-regulator? term)))
  (define regulator-pred (λ (term) 
                          (and (term? term)
                               (not (eq? (term-metadata term) 'non-flowing))
                               (not (eq? (term-metadata term) 'blocked)))))
  
  (define models (inst-models infoflow-kernel transition-fn totality-pred regulator-pred))
  
  ;; Truth theorems for Infoflow institution
  (define truth-theorems '(eor-health))
  (define verification-fns (hash 'eor-health eor-health?))
  
  (define sentences (inst-sentences truth-theorems verification-fns))
  
  (define eval-fn (λ (term) (kernel-apply kernel term)))
  (define satisfaction-pred (λ (term sentence) 
                             (case sentence
                               ['flowing (regulator-pred term)]
                               ['defined (totality-pred term)]
                               [else #f])))
  
  (define satisfaction (inst-satisfaction eval-fn satisfaction-pred))
  
  (make-institution signature models sentences satisfaction))

;; Helper function for regulator predicates
(define (halts-within-regulator? term)
  (and (term? term)
       (not (eq? (term-metadata term) 'non-halting))
       (not (eq? (term-metadata term) 'infinite-loop))))

(define (converges-within-regulator? term)
  (and (term? term)
       (not (eq? (term-metadata term) 'non-converging))
       (not (eq? (term-metadata term) 'divergent))))

(define (flows-within-regulator? term)
  (and (term? term)
       (not (eq? (term-metadata term) 'non-flowing))
       (not (eq? (term-metadata term) 'blocked))))
