#lang typed/racket
;; Logic Index - Clean Organization of Multiple Logics
;; This module provides a clean interface for managing different logical systems
;; Following the semiring-based architecture

(require "../M123_d/m2d.semiring.rkt")

(provide ;; Logic registry
         LogicRegistry LogicRegistry? LogicRegistry-logics
         make-logic-registry register-logic get-logic
         
         ;; Predefined logic configurations
         logic/boolean-top logic/boolean-maybe
         logic/kleene-local logic/kleene-global
         logic/tropical-cost logic/tropical-optimization
         
         ;; Logic composition
         compose-logics combine-observers
         
         ;; Logic validation
         validate-logic logic-compatible?)

;; ============================================================================
;; LOGIC REGISTRY
;; ============================================================================

;; Registry for managing multiple logical systems
(struct LogicRegistry ([logics : (HashTable Symbol Logic)]
                       [size : Natural]) #:transparent)

(: make-logic-registry (-> LogicRegistry))
(define (make-logic-registry)
  (LogicRegistry (hash) 0))

(: register-logic (-> LogicRegistry Symbol Logic LogicRegistry))
(define (register-logic registry name logic)
  (define current-logics (LogicRegistry-logics registry))
  (define current-size (LogicRegistry-size registry))
  (define new-logics (hash-set current-logics name logic))
  (LogicRegistry new-logics (if (hash-has-key? current-logics name) 
                                current-size 
                                (+ current-size 1))))

(: get-logic (-> LogicRegistry Symbol (U Logic #f)))
(define (get-logic registry name)
  (hash-ref (LogicRegistry-logics registry) name #f))

;; Fast lookup for common logics
(: get-logic-fast (-> LogicRegistry Symbol (U Logic #f)))
(define (get-logic-fast registry name)
  ;; Use direct hash lookup for better performance
  (hash-ref (LogicRegistry-logics registry) name #f))

;; ============================================================================
;; PREDEFINED LOGIC CONFIGURATIONS
;; ============================================================================

;; Boolean logic with top-lift and both observers
;; For complete evaluation with both local and global truth
(: logic/boolean-top Logic)
(define logic/boolean-top
  (make-logic 'boolean-top
               BoolRig
               (hash 'local q-local
                     'global q-global)))

;; Boolean logic with maybe-lift and local observer only
;; For partial evaluation where global truth may be unknown
(: logic/boolean-maybe Logic)
(define logic/boolean-maybe
  (make-logic 'boolean-maybe
               BoolRig
               (hash 'local q-local)))

;; Kleene logic with local observer
;; For three-valued logic with local tolerance
(: logic/kleene-local Logic)
(define logic/kleene-local
  (make-logic 'kleene-local
               KleeneRig
               (hash 'local q-local)))

;; Kleene logic with global observer
;; For three-valued logic with global exactness
(: logic/kleene-global Logic)
(define logic/kleene-global
  (make-logic 'kleene-global
               KleeneRig
               (hash 'global q-global)))

;; Tropical logic for cost-based evaluation
;; Uses min for disjunction, + for conjunction
(: logic/tropical-cost Logic)
(define logic/tropical-cost
  (make-logic 'tropical-cost
               TropicalRig
               (hash 'cost (lambda ([s : Any]) 
                             (if (real? s) (< s +inf.0) #f)))))

;; Tropical logic for optimization
;; Uses min for optimization problems
(: logic/tropical-optimization Logic)
(define logic/tropical-optimization
  (make-logic 'tropical-optimization
               TropicalRig
               (hash 'optimal (lambda ([s : Any]) 
                                (if (real? s) (< s +inf.0) #f)))))

;; ============================================================================
;; LOGIC COMPOSITION
;; ============================================================================

;; Compose multiple logics into a single system
;; This allows for hybrid evaluation strategies
(: compose-logics (-> (Listof Logic) Logic))
(define (compose-logics logics)
  (if (null? logics)
      (error "Cannot compose empty list of logics")
      (let* ([first-logic (car logics)]
             [combined-observers (foldl combine-observers 
                                        (Logic-observers first-logic)
                                        (map Logic-observers (cdr logics)))])
        (make-logic 'composed
                     (Logic-S first-logic)  ; Use semiring from first logic
                     combined-observers))))

;; Combine observer tables from multiple logics
(: combine-observers (-> (HashTable Symbol (-> Any Boolean))
                         (HashTable Symbol (-> Any Boolean))
                         (HashTable Symbol (-> Any Boolean))))
(define (combine-observers obs1 obs2)
  (for/fold ([result : (HashTable Symbol (-> Any Boolean)) obs1])
            ([(name observer) obs2])
    (hash-set result name observer)))

;; ============================================================================
;; LOGIC VALIDATION
;; ============================================================================

;; Validate that a logic is well-formed
(: validate-logic (-> Logic Boolean))
(define (validate-logic logic)
  (and (not (null? (hash-keys (Logic-observers logic))))
       (semiring-valid? (Logic-S logic))))

;; Check if semiring is valid (satisfies semiring laws)
(: semiring-valid? (-> Semiring Boolean))
(define (semiring-valid? S)
  ;; Basic validation: check that operations are functions
  ;; In a full implementation, we would verify semiring laws
  (and (procedure? (Semiring-add S))
       (procedure? (Semiring-mul S))
       #t))

;; Check if two logics are compatible for composition
(: logic-compatible? (-> Logic Logic Boolean))
(define (logic-compatible? L1 L2)
  ;; Two logics are compatible if they use the same semiring
  (eq? (Logic-S L1) (Logic-S L2)))

;; ============================================================================
;; DEFAULT REGISTRY
;; ============================================================================

;; Create default registry with all predefined logics
(: default-logic-registry LogicRegistry)
(define default-logic-registry
  (let ([registry (make-logic-registry)])
    (foldl (lambda ([logic : Logic] [reg : LogicRegistry])
             (register-logic reg (Logic-name logic) logic))
           registry
           (list logic/boolean-top logic/boolean-maybe
                 logic/kleene-local logic/kleene-global
                 logic/tropical-cost logic/tropical-optimization))))
