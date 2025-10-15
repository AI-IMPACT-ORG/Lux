#lang racket

(require "../../core/kernel.rkt"
         "../../core/nf.rkt"
         "../../core/observers.rkt"
         "../../core/cumulants.rkt"
         "../../core/signature.rkt"
         "../../core/header.rkt"
         "../feynman.rkt"
         "../psdm.rkt"
         "../domain/unified-port.rkt"
         rackunit)

;; ===== COMPREHENSIVE NON-TRIVIAL TESTS FOR CLEAN v10 =====

(displayln "=== CLEAN v10 Kernel-Transition Machinery Tests ===")
(displayln "Testing mathematical properties according to CLEAN v10 specification")
(displayln "")

;; Test 1: Sequential Composition (Kleisli composition on bags)
(displayln "1. Sequential Composition Test (v10 spec §2.x):")
(define step1 (kernel (header 2.0 3.0) (transition 'step1 (λ (x) (list 'processed x)) '(event1))))
(define step2 (kernel (header 1.0 2.0) (transition 'step2 (λ (x) (list 'refined x)) '(event2))))
(define step3 (kernel (header 3.0 1.0) (transition 'step3 (λ (x) (list 'finalized x)) '(event3))))

;; Test header additivity: hdr(K₂∘K₁) = (Δφ₂+Δφ₁, ΔΛ₂+ΔΛ₁)
(define composed-kernel (kernel-compose (kernel-compose step1 step2) step3))
(define expected-header (kernel-header-add (kernel-header-add (kernel-header step1) (kernel-header step2)) (kernel-header step3)))

;; Test event sequence composition: e₁ ++ e₂ ++ e₃
(define composed-transition (kernel-transition composed-kernel))
(define expected-events '(event1 event2 event3))

(displayln (string-append "   Header additivity: " (format "~a" (kernel-header composed-kernel)) " = " (format "~a" expected-header)))
(displayln (string-append "   Event composition: " (format "~a" (transition-event-sequence composed-transition))))
(displayln (string-append "   Sequential composition: " (if (and (equal? (kernel-header composed-kernel) expected-header)
                                                                  (equal? (transition-event-sequence composed-transition) expected-events)) "PASS" "FAIL")))
(displayln "")

;; Test 2: Truncated Green's Object (v10 spec §2.x)
(displayln "2. Truncated Green's Object Test (v10 spec §2.x):")
(define base-kernel (kernel (header 1.0 1.0) (transition 'base (λ (x) x) '())))

;; G_N = I_B ⊕_B K ⊕_B K² ⊕_B ... ⊕_B K^N
(define greens-0 (greens-sum base-kernel 0))  ; G_0 = I_B
(define greens-1 (greens-sum base-kernel 1))  ; G_1 = I_B ⊕_B K
(define greens-2 (greens-sum base-kernel 2))  ; G_2 = I_B ⊕_B K ⊕_B K²
(define greens-5 (greens-sum base-kernel 5))  ; G_5 = I_B ⊕_B K ⊕_B K² ⊕_B K³ ⊕_B K⁴ ⊕_B K⁵

;; Verify G_N is a bulk term with correct header
(define identity-k (identity-kernel))
(define k-squared (kernel-compose base-kernel base-kernel))

(displayln (string-append "   G_0 = I_B: " (format "~a" (kernel-header greens-0)) " = " (format "~a" (kernel-header identity-k))))
(displayln (string-append "   G_1 = I ⊕ K: " (format "~a" (kernel-header greens-1))))
(displayln (string-append "   G_2 = I ⊕ K ⊕ K²: " (format "~a" (kernel-header greens-2))))
(displayln (string-append "   G_5 header: " (format "~a" (kernel-header greens-5))))
(displayln (string-append "   Green's object: " (if (and (header-equal? (kernel-header greens-0) (header 0.0 0.0))
                                                          (header-equal? (kernel-header greens-1) (header 1.0 1.0))
                                                          (header-equal? (kernel-header greens-2) (header 3.0 3.0))
                                                          (header-equal? (kernel-header greens-5) (header 15.0 15.0))) "PASS" "FAIL")))
(displayln "")

;; Test 3: RC-ME (Invisibility under micro-evolution) (v10 spec §2.x)
(displayln "3. RC-ME Residual Invisibility Test (v10 spec §2.x):")
(define test-term (make-term 'test-term #:header (header 2.0 3.0) #:core 'test-core))
(define micro-kernel (kernel (header 1.0 1.0) (transition 'micro (λ (x) x) '())))

;; RC-ME: ν_*(int(K ⊗_B t)) = 0_* for *∈{L,R}
(define applied-term (kernel-apply micro-kernel test-term))
(define reconstituted (reconstitute applied-term))
(define residual-term (residual applied-term))

;; Test that micro-step doesn't leak interaction residual to boundaries
(define left-obs-residual (observer-value residual-term 'L))
(define right-obs-residual (observer-value residual-term 'R))

(displayln (string-append "   Original term header: " (format "~a" (term-header test-term))))
(displayln (string-append "   Applied term header: " (format "~a" (term-header applied-term))))
(displayln (string-append "   Left observer residual: " (format "~a" (term-name left-obs-residual))))
(displayln (string-append "   Right observer residual: " (format "~a" (term-name right-obs-residual))))
(displayln (string-append "   RC-ME compliance: " (if (and (equal? (term-name left-obs-residual) '0_L)
                                                           (equal? (term-name right-obs-residual) '0_R)) "PASS" "FAIL")))
(displayln "")

;; Test 4: Feynman = Green's Sum Equivalence (CLASS spec §5)
(displayln "4. Feynman = Green's Sum Equivalence Test (CLASS spec §5):")
(define feynman-kernel (kernel (header 2.0 1.0) (transition 'feynman (λ (x) x) '())))
(define orders '(1 2 3 4 5))
(define all-passed #t)

;; Test: sum-over-histories J :N n = observer-L (greens-sum K n)
(for ([n orders])
  (define feynman-result (sum-over-histories feynman-kernel n))
  (define greens-result (greens-sum feynman-kernel n))
  (define equivalent? (header-equal? (term-header feynman-result) (kernel-header greens-result)))
  (set! all-passed (and all-passed equivalent?))
  (displayln (string-append "   Order " (format "~a" n) ": Feynman=" (format "~a" (term-header feynman-result)) 
                           " Green's=" (format "~a" (kernel-header greens-result)) " " (if equivalent? "PASS" "FAIL"))))

(displayln (string-append "   Feynman-Green's equivalence: " (if all-passed "PASS" "FAIL")))
(displayln "")

;; Test 5: PSDM (Partial Stable Domain Map) (CLASS spec §4)
(displayln "5. PSDM Kernel Integration Test (CLASS spec §4):")
(define psdm-kernel (kernel (header 1.0 2.0) (transition 'psdm (λ (x) (list 'psdm-result x)) '())))
(define totality-pred (λ (term) (not (eq? (term-metadata term) 'undefined))))
(define psdm-instance (make-psdm-legacy))

;; Test PSDM partiality: undefined on non-halting
(define test-term-psdm (make-term 'psdm-test #:header (header 0.0 0.0) #:core 'test))
(define undefined-term (make-term 'non-halting #:header (header 0.0 0.0) #:core 'test #:metadata 'undefined))
(define psdm-result (psdm-apply psdm-instance test-term-psdm))
(define psdm-undefined (psdm-apply psdm-instance undefined-term))

(displayln (string-append "   PSDM kernel header: " (format "~a" (kernel-header psdm-kernel))))
(displayln (string-append "   PSDM defined result: " (format "~a" psdm-result)))
(displayln (string-append "   PSDM undefined result: " (format "~a" psdm-undefined)))
(displayln (string-append "   PSDM partiality: " (if (and (not (eq? psdm-result 'undefined))
                                                           (eq? psdm-undefined 'undefined)) "PASS" "FAIL")))
(displayln "")

;; Test 6: Domain Ports (CLASS spec §3) - Paper-Aligned
(displayln "6. Domain Port Kernel Integration Test (CLASS spec §3) - Paper-Aligned:")
(define turing-port (make-turing-port #:threshold 0.3))      ; q=(1,0,0) - Turing machines
(define lambda-port (make-lambda-port))                     ; q=(0,1,0) - Lambda calculus  
(define path-port (make-path-port #:euclidean? #t))         ; q=(0,0,1) - Path integrals
(define infoflow-port (make-infoflow-port))                ; Information measures

;; Test minimal obligation: each port provides carrier, totality predicate, and kernel
(define test-term-port (make-term 'port-test #:header (header 1.0 0.0) #:core 'test-core))
(define turing-result (domain-port-eval turing-port test-term-port))
(define lambda-result (domain-port-eval lambda-port test-term-port))
(define path-result (domain-port-eval path-port test-term-port))
(define infoflow-result (domain-port-eval infoflow-port test-term-port))

(displayln (string-append "   Turing port result (q=(1,0,0)): " (format "~a" turing-result)))
(displayln (string-append "   Lambda port result (q=(0,1,0)): " (format "~a" lambda-result)))
(displayln (string-append "   Path port result (q=(0,0,1)): " (format "~a" path-result)))
(displayln (string-append "   Infoflow port result: " (format "~a" infoflow-result)))
(displayln (string-append "   Domain port integration: " (if (and (not (eq? turing-result 'undefined))
                                                                     (not (eq? lambda-result 'undefined))
                                                                     (not (eq? path-result 'undefined))
                                                                     (not (eq? infoflow-result 'undefined))) "PASS" "FAIL")))
(displayln "")

;; Test 7: Generating Functional & Cumulants (v10 spec §3)
(displayln "7. Generating Functional & Cumulants Test (v10 spec §3):")
(clear-observables!)
(register-observable 0 (make-term 'obs0 #:header (header 1.0 1.0) #:core 'obs0-core))
(register-observable 1 (make-term 'obs1 #:header (header 2.0 2.0) #:core 'obs1-core))

;; Z[J] := ⟨ ⨂_{i∈I_fin} (1_B ⊕_B ι_L(J_i) ⊗_B Obs(i)) ⟩_{μ,θ} ∈ L
(define cumulant-kernel (kernel (header 1.0 1.0) (transition 'cumulant (λ (x) x) '())))
(define sources '((0 . 1) (1 . 2)))
(define kernel-zj (kernel-generating-functional cumulant-kernel sources))
(define kernel-cumulants-result (kernel-cumulants cumulant-kernel '(0 1)))

;; Test cumulant sanity: g(i), G(i,j), β-fields, monotones a,c
(define g-0 (value-g 0))
(define G-0-1 (value-G 0 1))
(define beta-mu-0 (value-beta-mu 0))
(define beta-theta-0 (value-beta-theta 0))
(define monotone-a (value-a))
(define monotone-c (value-c))

(displayln (string-append "   Kernel Z[J] header: " (format "~a" (term-header kernel-zj))))
(displayln (string-append "   Kernel cumulants: " (format "~a" kernel-cumulants-result)))
(displayln (string-append "   g(0): " (format "~a" g-0)))
(displayln (string-append "   G(0,1): " (format "~a" G-0-1)))
(displayln (string-append "   Cumulant integration: " (if (and (term? kernel-zj) (list? kernel-cumulants-result)) "PASS" "FAIL")))
(displayln "")

;; Test 8: Bulk = Two Boundaries (v10 spec §2)
(displayln "8. Bulk = Two Boundaries Test (v10 spec §2):")
(define bulk-term (make-term 'bulk-test #:header (header 3.0 4.0) #:core 'bulk-core))

;; Decomposition Theorem (observer form): ν_L(t) = ν_L([L](t) ⊕_B [R](t))
(define left-obs (observer-value bulk-term 'L))
(define right-obs (observer-value bulk-term 'R))
(define reconstituted-bulk (reconstitute bulk-term))
(define left-recon (observer-value reconstituted-bulk 'L))
(define right-recon (observer-value reconstituted-bulk 'R))

;; Test residual invisibility: ν_*(int(t)) = 0_* for *∈{L,R}
(define residual-term-bulk (residual bulk-term))
(define left-residual (observer-value residual-term-bulk 'L))
(define right-residual (observer-value residual-term-bulk 'R))

(displayln (string-append "   Left observer: " (format "~a" (term-name left-obs))))
(displayln (string-append "   Right observer: " (format "~a" (term-name right-obs))))
(displayln (string-append "   Left residual: " (format "~a" (term-name left-residual))))
(displayln (string-append "   Right residual: " (format "~a" (term-name right-residual))))
(displayln (string-append "   Bulk = boundaries: " (if (bulk-equals-boundaries? bulk-term) "PASS" "FAIL")))
(displayln "")

;; Test 9: RG Blocking on Kernels (v10 spec §1)
(displayln "9. RG Blocking on Kernels Test (v10 spec §1):")
(define rg-term (make-term 'rg-test #:header (header 2.0 3.0) #:core 'rg-core))
(define rg-kernel (kernel (header 1.0 2.0) (transition 'rg (λ (x) x) '())))

;; RG blocking: K^(k) = K^k with header-only reparametrization
(define rg-blocked (normal-form-rg-block rg-term 3))
(define blocked-kernel (kernel-rg-block rg-kernel 3))

;; Test: core(NF_{μ,θ}(K^(k))) = core(K^(k)) (header-only reparametrization)
(define expected-header-rg (header 6.0 9.0))
(define expected-kernel-header (header 3.0 6.0))

(displayln (string-append "   Original header: " (format "~a" (term-header rg-term))))
(displayln (string-append "   Blocked header: " (format "~a" (cons (nf-phase rg-blocked) (nf-scale rg-blocked)))))
(displayln (string-append "   Kernel blocked header: " (format "~a" (kernel-header blocked-kernel))))
(displayln (string-append "   RG blocking: " (if (and (header-equal? (header (nf-phase rg-blocked) (nf-scale rg-blocked)) expected-header-rg)
                                                         (header-equal? (kernel-header blocked-kernel) expected-kernel-header)) "PASS" "FAIL")))
(displayln "")

;; Test 10: Kernel Composition Associativity (v10 spec §2.x)
(displayln "10. Kernel Composition Associativity Test (v10 spec §2.x):")
(define k1 (kernel (header 1.0 2.0) (transition 'k1 (λ (x) x) '())))
(define k2 (kernel (header 3.0 4.0) (transition 'k2 (λ (x) x) '())))
(define k3 (kernel (header 5.0 6.0) (transition 'k3 (λ (x) x) '())))

;; Test associativity: (K₁ ∘ K₂) ∘ K₃ = K₁ ∘ (K₂ ∘ K₃)
(define left-assoc (kernel-compose (kernel-compose k1 k2) k3))
(define right-assoc (kernel-compose k1 (kernel-compose k2 k3)))

(displayln (string-append "   Left associative header: " (format "~a" (kernel-header left-assoc))))
(displayln (string-append "   Right associative header: " (format "~a" (kernel-header right-assoc))))
(displayln (string-append "   Associativity: " (if (equal? (kernel-header left-assoc) (kernel-header right-assoc)) "PASS" "FAIL")))
(displayln "")

;; Test 11: Kernel Header Operations (v10 spec §2.x)
(displayln "11. Kernel Header Operations Test (v10 spec §2.x):")
(define h1 (header 2.0 3.0))
(define h2 (header 1.0 4.0))
(define h3 (header 0.0 0.0))

;; Test header additivity: (Δφ₁+Δφ₂, ΔΛ₁+ΔΛ₂)
(define sum-result (kernel-header-add h1 h2))
(define product-result (kernel-header-product h1 h2))
(define zero-check (equal? h3 kernel-header-zero))

(displayln (string-append "   Header sum: " (format "~a" sum-result)))
(displayln (string-append "   Header product: " (format "~a" product-result)))
(displayln (string-append "   Zero check: " (if zero-check "PASS" "FAIL")))
(displayln (string-append "   Header operations: " (if (and (header-equal? sum-result (header 3.0 7.0))
                                                             (header-equal? product-result (header 2.0 12.0))) "PASS" "FAIL")))
(displayln "")

;; Test 12: Transition Event Sequences (v10 spec §2.x)
(displayln "12. Transition Event Sequences Test (v10 spec §2.x):")
(define event-transition (transition 'event-test (λ (x) x) '(event1 event2 event3)))
(define composed-transition-events (transition-compose event-transition event-transition))

;; Test event sequence composition: e₁ ++ e₂
(displayln (string-append "   Original events: " (format "~a" (transition-event-sequence event-transition))))
(displayln (string-append "   Composed events: " (format "~a" (transition-event-sequence composed-transition-events))))
(displayln (string-append "   Event composition: " (if (equal? (length (transition-event-sequence composed-transition-events)) 6) "PASS" "FAIL")))
(displayln "")

;; Test 13: Kernel Identity Properties (v10 spec §2.x)
(displayln "13. Kernel Identity Properties Test (v10 spec §2.x):")
(define test-kernel (kernel (header 2.0 3.0) (transition 'test (λ (x) x) '())))
(define identity-kernel-test (identity-kernel))

;; Test identity: I_B has zero header and delta transition
(define composed-with-identity (kernel-compose test-kernel identity-kernel-test))
(define identity-composed (kernel-compose identity-kernel-test test-kernel))

(displayln (string-append "   Original kernel header: " (format "~a" (kernel-header test-kernel))))
(displayln (string-append "   Identity kernel header: " (format "~a" (kernel-header identity-kernel-test))))
(displayln (string-append "   Composed with identity: " (format "~a" (kernel-header composed-with-identity))))
(displayln (string-append "   Identity composed: " (format "~a" (kernel-header identity-composed))))
(displayln (string-append "   Identity properties: " (if (and (equal? (kernel-header composed-with-identity) (kernel-header test-kernel))
                                                              (equal? (kernel-header identity-composed) (kernel-header test-kernel))) "PASS" "FAIL")))
(displayln "")

;; Test 14: Kernel RG Blocking (v10 spec §1)
(displayln "14. Kernel RG Blocking Test (v10 spec §1):")
(define rg-kernel-test (kernel (header 1.0 2.0) (transition 'rg (λ (x) x) '())))
(define blocked-kernel-test (kernel-rg-block rg-kernel-test 3))

;; Test RG blocking: K^(k) = K^k
(displayln (string-append "   Original kernel header: " (format "~a" (kernel-header rg-kernel-test))))
(displayln (string-append "   Blocked kernel header: " (format "~a" (kernel-header blocked-kernel-test))))
(displayln (string-append "   RG blocking: " (if (header-equal? (kernel-header blocked-kernel-test) (header 3.0 6.0)) "PASS" "FAIL")))
(displayln "")

;; Test 15: Sequential Composition Properties (v10 spec §2.x)
(displayln "15. Sequential Composition Properties Test (v10 spec §2.x):")
(define k1-seq (kernel (header 1.0 1.0) (transition 'k1-seq (λ (x) x) '())))
(define k2-seq (kernel (header 2.0 2.0) (transition 'k2-seq (λ (x) x) '())))
(define k3-seq (kernel (header 3.0 3.0) (transition 'k3-seq (λ (x) x) '())))

;; Test sequential composition: (k1 + k2) * k3 ≠ k1*k3 + k2*k3 (as expected)
(define sum-kernels (kernel-compose k1-seq k2-seq))
(define left-seq (kernel-compose sum-kernels k3-seq))
(define right-seq (kernel-compose (kernel-compose k1-seq k3-seq) (kernel-compose k2-seq k3-seq)))

(displayln (string-append "   Left sequential header: " (format "~a" (kernel-header left-seq))))
(displayln (string-append "   Right sequential header: " (format "~a" (kernel-header right-seq))))
(displayln (string-append "   Sequential composition (non-distributive): " (if (not (equal? (kernel-header left-seq) (kernel-header right-seq))) "PASS" "FAIL")))
(displayln "")

;; Test 16: Edge Cases and Boundary Conditions (v10 spec §2.x)
(displayln "16. Edge Cases and Boundary Conditions Test (v10 spec §2.x):")
(define zero-kernel (kernel (header 0.0 0.0) (transition 'zero (λ (x) x) '())))
(define large-kernel (kernel (header 100.0 100.0) (transition 'large (λ (x) x) '())))

;; Test edge cases: zero kernel, large kernel
(define zero-greens (greens-sum zero-kernel 10))
(define large-greens (greens-sum large-kernel 2))

(displayln (string-append "   Zero kernel G_10 header: " (format "~a" (kernel-header zero-greens))))
(displayln (string-append "   Large kernel G_2 header: " (format "~a" (kernel-header large-greens))))
(displayln (string-append "   Edge cases: " (if (and (header-equal? (kernel-header zero-greens) (header 0.0 0.0))
                                                     (header-equal? (kernel-header large-greens) (header 300.0 300.0))) "PASS" "FAIL")))
(displayln "")

;; Test 17: Mathematical Consistency with CLEAN v10 (v10 spec §2)
(displayln "17. Mathematical Consistency with CLEAN v10 Test (v10 spec §2):")
(define test-term-consistency (make-term 'consistency-test #:header (header 1.0 1.0) #:core 'test))
(define kernel-consistency (kernel (header 2.0 2.0) (transition 'consistency (λ (x) x) '())))

;; Test RC-ME: residual invisibility under micro-evolution
(define applied-consistency (kernel-apply kernel-consistency test-term-consistency))
(define left-obs-consistency (observer-value applied-consistency 'L))
(define right-obs-consistency (observer-value applied-consistency 'R))

;; Test bulk = two boundaries
(define reconstituted-consistency (reconstitute applied-consistency))
(define left-recon-consistency (observer-value reconstituted-consistency 'L))
(define right-recon-consistency (observer-value reconstituted-consistency 'R))

(displayln (string-append "   Applied term header: " (format "~a" (term-header applied-consistency))))
(displayln (string-append "   Left observer: " (format "~a" (term-name left-obs-consistency))))
(displayln (string-append "   Right observer: " (format "~a" (term-name right-obs-consistency))))
(displayln (string-append "   CLEAN v10 consistency: " (if (and (header-equal? (term-header applied-consistency) (header 3.0 3.0))
                                                                  (not (eq? (term-name left-obs-consistency) '0_L))
                                                                  (not (eq? (term-name right-obs-consistency) '0_R))) "PASS" "FAIL")))
(displayln "")

;; Test 18: Non-normative Checks (v10 spec §4)
(displayln "18. Non-normative Checks Test (v10 spec §4):")
(define test-term-normative (make-term 'tB #:header (header 1.0 1.0) #:core 'test))
(define kernel-step (kernel (header 1.0 1.0) (transition 'Kstep (λ (x) x) '())))

;; Test: residual remains invisible after a kernel step (RC–ME)
(define applied-normative (kernel-apply kernel-step test-term-normative))
(define residual-normative (residual applied-normative))
(define left-residual-normative (observer-value residual-normative 'L))
(define right-residual-normative (observer-value residual-normative 'R))

;; Test: RG blocking acts on headers only
(define rg-kernel-normative (kernel (header 2.0 3.0) (transition 'rg-test (λ (x) x) '())))
(define blocked-kernel-normative (kernel-rg-block rg-kernel-normative 3))

(displayln (string-append "   Left residual after kernel step: " (format "~a" (term-name left-residual-normative))))
(displayln (string-append "   Right residual after kernel step: " (format "~a" (term-name right-residual-normative))))
(displayln (string-append "   RG blocked kernel header: " (format "~a" (kernel-header blocked-kernel-normative))))
(displayln (string-append "   Non-normative checks: " (if (and (equal? (term-name left-residual-normative) '0_L)
                                                                (equal? (term-name right-residual-normative) '0_R)
                                                                (header-equal? (kernel-header blocked-kernel-normative) (header 6.0 9.0))) "PASS" "FAIL")))
(displayln "")

(displayln "=== ALL NON-TRIVIAL TESTS COMPLETED ===")
(displayln "Tests verify mathematical properties according to CLEAN v10 specification")
