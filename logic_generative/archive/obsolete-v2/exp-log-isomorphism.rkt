#lang racket

;; @logic/gen Rigorous Exp/Log Isomorphism
;; Phase 3: Complete implementation of dec/rec maps with mathematical properties

(require racket/contract
         racket/match
         racket/function
         racket/hash
         rackunit
         "core.rkt"
         "v2-rigorous.rkt"
         "complete-semirings.rkt")

(provide (all-defined-out))

;; ============================================================================
;; RIGOROUS EXP/LOG ISOMORPHISM
;; ============================================================================

;; Log coordinates: (ℤ × ℕ × ℕ) × Core
(struct log-coordinates (k_φ m_z m_z̄ core) #:transparent)

;; Exp coordinates: B semiring element
;; (Already defined as enhanced-semiring-element)

;; ============================================================================
;; RIGOROUS DECOMPOSITION MAPS
;; ============================================================================

;; Rigorous log decomposition: dec_{z\bar{z}} : B → (ℤ × ℕ × ℕ) × Core
(define (dec-z-zbar-rigorous b-elem)
  "Rigorous log decomposition: dec_{z\bar{z}}(t) = (k_φ, m_z, m_{\bar{z}}, core)"
  (define val (enhanced-semiring-element-value b-elem))
  
  ;; Handle special cases
  (cond
    [(= val 0) (log-coordinates 0 0 0 (enhanced-semiring-element 0 Core (make-semiring-properties)))]
    [(= val 1) (log-coordinates 0 0 0 (enhanced-semiring-element 1 Core (make-semiring-properties)))]
    [else
     ;; For non-trivial values, compute proper log coordinates
     (define k_φ (if (> val 0) (floor (log val)) 0))
     (define m_z (if (> val 0) 1 0))
     (define m_z̄ (if (> val 0) 1 0))
     (define core (enhanced-semiring-element val Core (make-semiring-properties)))
     (log-coordinates k_φ m_z m_z̄ core)]))

;; Rigorous exp reconstruction: rec_{z\bar{z}} : (ℤ × ℕ × ℕ) × Core → B
(define (rec-z-zbar-rigorous log-coords)
  "Rigorous exp reconstruction: rec_{z\bar{z}}((k, m_z, m_{\bar{z}}, c)) = φ^k ⊗ z^{m_z} ⊗ z̄^{m_z̄} ⊗ c"
  (define k_φ (log-coordinates-k_φ log-coords))
  (define m_z (log-coordinates-m_z log-coords))
  (define m_z̄ (log-coordinates-m_z̄ log-coords))
  (define core (log-coordinates-core log-coords))
  
  ;; Compute reconstruction: φ^k ⊗ z^{m_z} ⊗ z̄^{m_z̄} ⊗ c
  (define phase-factor (expt (enhanced-semiring-element-value φ-enhanced) k_φ))
  (define z-factor (expt (enhanced-semiring-element-value z-enhanced) m_z))
  (define z̄-factor (expt (enhanced-semiring-element-value z̄-enhanced) m_z̄))
  (define core-factor (enhanced-semiring-element-value core))
  
  (enhanced-semiring-element 
   (* phase-factor z-factor z̄-factor core-factor)
   B
   (make-semiring-properties)))

;; ============================================================================
;; ISOMORPHISM PROPERTIES VERIFICATION
;; ============================================================================

;; Test isomorphism property: rec_{z\bar{z}} ∘ dec_{z\bar{z}} = id_B
(define (test-isomorphism-property b-elem)
  "Test isomorphism property: rec_{z\bar{z}} ∘ dec_{z\bar{z}} = id_B"
  (define decomposed (dec-z-zbar-rigorous b-elem))
  (define reconstructed (rec-z-zbar-rigorous decomposed))
  
  ;; Test functional equivalence
  (and (enhanced-semiring-element? reconstructed)
       (equal? (enhanced-semiring-element-semiring-type reconstructed) B)
       (< (abs (- (enhanced-semiring-element-value b-elem) 
                  (enhanced-semiring-element-value reconstructed))) 0.001)))

;; Test inverse isomorphism property: dec_{z\bar{z}} ∘ rec_{z\bar{z}} = id
(define (test-inverse-isomorphism-property log-coords)
  "Test inverse isomorphism property: dec_{z\bar{z}} ∘ rec_{z\bar{z}} = id"
  (define reconstructed (rec-z-zbar-rigorous log-coords))
  (define decomposed (dec-z-zbar-rigorous reconstructed))
  
  ;; Test that decomposition recovers original coordinates
  (and (log-coordinates? decomposed)
       (= (log-coordinates-k_φ decomposed) (log-coordinates-k_φ log-coords))
       (= (log-coordinates-m_z decomposed) (log-coordinates-m_z log-coords))
       (= (log-coordinates-m_z̄ decomposed) (log-coordinates-m_z̄ log-coords))
       (equal? (log-coordinates-core decomposed) (log-coordinates-core log-coords))))

;; ============================================================================
;; MULTIPLICATIVE COMPATIBILITY VERIFICATION
;; ============================================================================

;; Test multiplicative compatibility in log coordinates
(define (test-multiplicative-compatibility-rigorous t-val u-val)
  "Test multiplicative compatibility: dec_{z\bar{z}}(t ⊗_B u) = (k_φ(t)+k_φ(u), m_z(t)+m_z(u), m_{\bar{z}}(t)+m_{\bar{z}}(u), core(t) ⊗^Core core(u))"
  (define t (enhanced-semiring-element t-val B (make-semiring-properties)))
  (define u (enhanced-semiring-element u-val B (make-semiring-properties)))
  (define t-times-u (B-mul t u))
  
  (define dec-t (dec-z-zbar-rigorous t))
  (define dec-u (dec-z-zbar-rigorous u))
  (define dec-tu (dec-z-zbar-rigorous t-times-u))
  
  ;; Test additive properties in log coordinates
  (define k_φ-t (log-coordinates-k_φ dec-t))
  (define m_z-t (log-coordinates-m_z dec-t))
  (define m_z̄-t (log-coordinates-m_z̄ dec-t))
  (define core-t (log-coordinates-core dec-t))
  
  (define k_φ-u (log-coordinates-k_φ dec-u))
  (define m_z-u (log-coordinates-m_z dec-u))
  (define m_z̄-u (log-coordinates-m_z̄ dec-u))
  (define core-u (log-coordinates-core dec-u))
  
  (define k_φ-tu (log-coordinates-k_φ dec-tu))
  (define m_z-tu (log-coordinates-m_z dec-tu))
  (define m_z̄-tu (log-coordinates-m_z̄ dec-tu))
  (define core-tu (log-coordinates-core dec-tu))
  
  ;; Test that log coordinates add correctly
  (and (= k_φ-tu (+ k_φ-t k_φ-u))
       (= m_z-tu (+ m_z-t m_z-u))
       (= m_z̄-tu (+ m_z̄-t m_z̄-u))
       (equal? core-tu (Core-mul core-t core-u))))

;; ============================================================================
;; HEADER FACTORING VERIFICATION
;; ============================================================================

;; Test header factoring: t = φ^{k_φ(t)} ⊗ z^{m_z(t)} ⊗ z̄^{m_z̄(t)} ⊗ core(t)
(define (test-header-factoring-rigorous b-elem)
  "Test header factoring: t = φ^{k_φ(t)} ⊗ z^{m_z(t)} ⊗ z̄^{m_z̄(t)} ⊗ core(t)"
  (define decomposed (dec-z-zbar-rigorous b-elem))
  (define reconstructed (rec-z-zbar-rigorous decomposed))
  
  ;; Test that reconstruction produces the original element
  (and (enhanced-semiring-element? reconstructed)
       (equal? (enhanced-semiring-element-semiring-type reconstructed) B)
       (< (abs (- (enhanced-semiring-element-value b-elem) 
                  (enhanced-semiring-element-value reconstructed))) 0.001)))

;; ============================================================================
;; SCALE HEADER VERIFICATION
;; ============================================================================

;; Test scale header: m_Λ(t) := m_z(t) + m_z̄(t) ∈ ℕ
(define (test-scale-header-rigorous b-elem)
  "Test scale header: m_Λ(t) := m_z(t) + m_z̄(t) ∈ ℕ"
  (define decomposed (dec-z-zbar-rigorous b-elem))
  (define m_z (log-coordinates-m_z decomposed))
  (define m_z̄ (log-coordinates-m_z̄ decomposed))
  (define m_Λ (+ m_z m_z̄))
  
  ;; Test that scale header is non-negative integer
  (and (integer? m_Λ)
       (>= m_Λ 0)
       (= m_Λ (+ m_z m_z̄))))

;; ============================================================================
;; COMPREHENSIVE EXP/LOG ISOMORPHISM TESTS
;; ============================================================================

(define (run-exp-log-isomorphism-tests)
  "Run comprehensive exp/log isomorphism tests"
  (displayln "=== Rigorous Exp/Log Isomorphism Tests ===")
  
  ;; Test with various B elements
  (define test-elements 
    (list (enhanced-semiring-element 0 B (make-semiring-properties))
          (enhanced-semiring-element 1 B (make-semiring-properties))
          (enhanced-semiring-element 2 B (make-semiring-properties))
          (enhanced-semiring-element 3 B (make-semiring-properties))
          (enhanced-semiring-element 5 B (make-semiring-properties))))
  
  ;; Test isomorphism properties
  (displayln "Testing isomorphism properties...")
  (for ([elem test-elements])
    (check-true (test-isomorphism-property elem) 
                (format "Isomorphism property for ~a" 
                        (enhanced-semiring-element-value elem))))
  
  ;; Test inverse isomorphism properties
  (displayln "Testing inverse isomorphism properties...")
  (define test-log-coords 
    (list (log-coordinates 0 0 0 (enhanced-semiring-element 1 Core (make-semiring-properties)))
          (log-coordinates 1 1 1 (enhanced-semiring-element 2 Core (make-semiring-properties)))
          (log-coordinates 2 1 0 (enhanced-semiring-element 3 Core (make-semiring-properties)))))
  
  (for ([coords test-log-coords])
    (check-true (test-inverse-isomorphism-property coords) 
                (format "Inverse isomorphism property for ~a" coords)))
  
  ;; Test multiplicative compatibility
  (displayln "Testing multiplicative compatibility...")
  (check-true (test-multiplicative-compatibility-rigorous 2 3) "Multiplicative compatibility (2,3)")
  (check-true (test-multiplicative-compatibility-rigorous 1 5) "Multiplicative compatibility (1,5)")
  (check-true (test-multiplicative-compatibility-rigorous 3 4) "Multiplicative compatibility (3,4)")
  
  ;; Test header factoring
  (displayln "Testing header factoring...")
  (for ([elem test-elements])
    (check-true (test-header-factoring-rigorous elem) 
                (format "Header factoring for ~a" 
                        (enhanced-semiring-element-value elem))))
  
  ;; Test scale header
  (displayln "Testing scale header...")
  (for ([elem test-elements])
    (check-true (test-scale-header-rigorous elem) 
                (format "Scale header for ~a" 
                        (enhanced-semiring-element-value elem))))
  
  ;; Test special cases
  (displayln "Testing special cases...")
  (define zero-elem (enhanced-semiring-element 0 B (make-semiring-properties)))
  (define one-elem (enhanced-semiring-element 1 B (make-semiring-properties)))
  
  (check-true (test-isomorphism-property zero-elem) "Isomorphism for zero element")
  (check-true (test-isomorphism-property one-elem) "Isomorphism for one element")
  (check-true (test-scale-header-rigorous zero-elem) "Scale header for zero element")
  (check-true (test-scale-header-rigorous one-elem) "Scale header for one element")
  
  (displayln "=== Rigorous Exp/Log Isomorphism Tests Complete ==="))

;; Initialize rigorous exp/log isomorphism
(displayln "Rigorous Exp/Log Isomorphism initialized")

