#lang typed/racket
;; Optimized Semiring-based PGC Evaluation - Performance Enhancements

;; This module provides optimized versions of the semiring operations
;; while maintaining full backward compatibility

(require "m3d.graph.rkt" "m2d.pgc-core.rkt")
(provide ;; Optimized semiring operations
         SemiringOps SemiringOps? SemiringOps-add SemiringOps-mul SemiringOps-zero SemiringOps-one
         make-semiring-ops memoized-add memoized-mul
         
         ;; Memoized evaluation
         pgc-eval-memoized
         
         ;; Optimized observers
         q-local-fast q-global-fast
         
         ;; Optimized logic registry
         LogicRegistry LogicRegistry? LogicRegistry-logics LogicRegistry-size
         make-logic-registry register-logic get-logic-fast
         
         ;; Backward compatibility
         Semiring Semiring? Logic Logic? Logic-name
         logic/boolean-top logic/boolean-maybe
         BoolRig KleeneRig TropicalRig ExpLogRig
         logic/log-exp
         pgc-eval satisfies^ guarded-negation)

;; ============================================================================
;; OPTIMIZED SEMIRING OPERATIONS
;; ============================================================================

;; Pre-computed semiring operations for performance
(struct SemiringOps ([add : (-> Any Any Any)]
                     [mul : (-> Any Any Any)]
                     [zero : Any]
                     [one : Any]
                     [add-memo : (HashTable (Pairof Any Any) Any)]
                     [mul-memo : (HashTable (Pairof Any Any) Any)])
  #:transparent)

(: make-semiring-ops (-> Semiring SemiringOps))
(define (make-semiring-ops S)
  (SemiringOps (Semiring-add S)
               (Semiring-mul S)
               (Semiring-zero S)
               (Semiring-one S)
               (make-hash)  ; Empty memoization table for add
               (make-hash))) ; Empty memoization table for mul

;; Memoized semiring operations
(: memoized-add (-> SemiringOps Any Any Any))
(define (memoized-add ops a b)
  (define key (cons a b))
  (define memo-table (SemiringOps-add-memo ops))
  (cond
    [(hash-has-key? memo-table key)
     (hash-ref memo-table key)]
    [else
     (define result ((SemiringOps-add ops) a b))
     (hash-set! memo-table key result)
     result]))

(: memoized-mul (-> SemiringOps Any Any Any))
(define (memoized-mul ops a b)
  (define key (cons a b))
  (define memo-table (SemiringOps-mul-memo ops))
  (cond
    [(hash-has-key? memo-table key)
     (hash-ref memo-table key)]
    [else
     (define result ((SemiringOps-mul ops) a b))
     (hash-set! memo-table key result)
     result]))

(: logic-observer (-> Logic Symbol (-> Any Boolean) (-> Any Boolean)))
(define (logic-observer L key fallback)
  (define observers (Logic-observers L))
  (if (hash-has-key? observers key)
      (hash-ref observers key)
      fallback))

;; ============================================================================
;; OPTIMIZED PGC EVALUATION
;; ============================================================================

;; Memoized PGC evaluation with pre-computed semiring operations
(: pgc-eval-memoized (-> Logic SemiringOps TGraph GuardEnv PGC Any))
(define (pgc-eval-memoized L ops G γ φ)
  (define zero (SemiringOps-zero ops))
  (define one (SemiringOps-one ops))
  
  (match φ
    [(Top) one]
    [(MatchX X) one]  ; TODO: check X embeds into dom(γ)
    [(Exists i Y ψ) one]  ; TODO: check ∃m:Y→G with m∘i=ρ, then recurse
    [(Not ψ)
     (define value (pgc-eval-memoized L ops G γ ψ))
     (define local (logic-observer L 'local q-local-fast))
     (if (local value) zero one)]
    [(And a b) (memoized-mul ops (pgc-eval-memoized L ops G γ a) (pgc-eval-memoized L ops G γ b))]
    [(Or a b) (memoized-add ops (pgc-eval-memoized L ops G γ a) (pgc-eval-memoized L ops G γ b))]))

;; ============================================================================
;; OPTIMIZED OBSERVER FUNCTIONS
;; ============================================================================

;; Fast local truth observer with optimized pattern matching
(: q-local-fast (-> Any Boolean))
(define (q-local-fast s)
  (cond
    [(eq? s 'unknown) #f]
    [(eq? s #t) #t]
    [(eq? s #f) #f]
    [else #f]))

;; Fast global truth observer with optimized pattern matching
(: q-global-fast (-> Any Boolean))
(define (q-global-fast s)
  (cond
    [(eq? s 'unknown) #f]
    [(eq? s #t) #t]
    [(eq? s #f) #f]
    [else #f]))

;; ============================================================================
;; OPTIMIZED LOGIC REGISTRY
;; ============================================================================

;; Optimized logic registry with size tracking
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

(: get-logic-fast (-> LogicRegistry Symbol (U Logic #f)))
(define (get-logic-fast registry name)
  (hash-ref (LogicRegistry-logics registry) name #f))

;; ============================================================================
;; BACKWARD COMPATIBILITY
;; ============================================================================

;; Re-export original semiring functionality for compatibility
;; Self-contained optimized semiring implementation

;; Semiring structure (from original implementation)
(struct Semiring ([add : (-> Any Any Any)]
                  [mul : (-> Any Any Any)]
                  [zero : Any]
                  [one : Any])
  #:transparent)

;; Standard semirings
(define BoolRig (Semiring (lambda ([a : Any] [b : Any]) (or a b))
                          (lambda ([a : Any] [b : Any]) (and a b))
                          #f
                          #t))

(define KleeneRig (Semiring (lambda ([a : Any] [b : Any]) (or a b))
                            (lambda ([a : Any] [b : Any]) (and a b))
                            'unknown
                            #t))

(define TropicalRig (Semiring (lambda ([a : Any] [b : Any]) 
                                (if (and (real? a) (real? b)) (min a b) +inf.0))
                              (lambda ([a : Any] [b : Any]) 
                                (if (and (real? a) (real? b)) (+ a b) +inf.0))
                              +inf.0
                              0))

;; Logic structure
(struct Logic ([name : Symbol]
               [S : Semiring]
               [observers : (HashTable Symbol (-> Any Boolean))])
  #:transparent)

;; Logic accessor functions are automatically provided by the struct

;; Create a logic with semiring and observers
(: make-logic (-> Symbol Semiring (HashTable Symbol (-> Any Boolean)) Logic))
(define (make-logic name semiring observers)
  (Logic name semiring observers))

;; Observer functions are already defined above

;; Predefined logics
(: logic/boolean-top Logic)
(define logic/boolean-top
  (make-logic 'boolean-top
              BoolRig
              (hash 'local q-local-fast 'global q-global-fast)))

(: logic/boolean-maybe Logic)
(define logic/boolean-maybe
  (make-logic 'boolean-maybe
              BoolRig
              (hash 'local q-local-fast)))

(define (log-exp-sum a b)
  (cond
    [(and (real? a) (real? b))
     (define max-ab (max a b))
     (cond
       [(= max-ab -inf.0) -inf.0]
       [else
        (define sum (exp (- a max-ab)))
        (define sum2 (+ sum (exp (- b max-ab))))
        (+ max-ab (log sum2))])]
    [else -inf.0]))

(define (log-exp-prod a b)
  (cond
    [(and (real? a) (real? b)) (+ a b)]
    [else -inf.0]))

(define ExpLogRig (Semiring log-exp-sum log-exp-prod -inf.0 0.0))

(define (log-exp-observer value)
  (and (real? value) (not (= value -inf.0))))

(: logic/log-exp Logic)
(define logic/log-exp
  (make-logic 'log-exp
              ExpLogRig
              (hash 'local log-exp-observer 'global log-exp-observer)))

;; Original pgc-eval function for compatibility
(: pgc-eval (-> Logic TGraph GuardEnv PGC Any))
(define (pgc-eval L G γ φ)
  (define S (Logic-S L))
  (define add (Semiring-add S))
  (define mul (Semiring-mul S))
  (define zero (Semiring-zero S))
  (define one (Semiring-one S))
  
  (match φ
    [(Top) one]
    [(MatchX X) one]
    [(Exists i Y ψ) one]
    [(Not ψ)
     (define value (pgc-eval L G γ ψ))
     (define local (logic-observer L 'local q-local-fast))
     (if (local value) zero one)]
    [(And a b) (mul (pgc-eval L G γ a) (pgc-eval L G γ b))]
    [(Or a b) (add (pgc-eval L G γ a) (pgc-eval L G γ b))]))

;; The optimized version is available as pgc-eval-memoized

;; Parametric satisfaction relation
(: satisfies^ (-> Logic Symbol TGraph GuardEnv PGC Boolean))
(define (satisfies^ L rule G γ φ)
  (define observers (Logic-observers L))
  (define observer (hash-ref observers rule))
  (define result (pgc-eval L G γ φ))
  (observer result))

(: guarded-negation (-> Logic TGraph GuardEnv PGC Boolean))
(define (guarded-negation L G γ φ)
  (define local (logic-observer L 'local q-local-fast))
  (not (local (pgc-eval L G γ φ))))
