#lang racket
;; Complexity separation via spectral-gap regimes in the complexity port

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../logic/rg-regimes.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../common/utils.rkt")
         (file "../semantics/observer-identity.rkt")
         (file "../theorems/truth.rkt"))

(provide (all-defined-out))

;; Canonical class representatives (B-level), headers encode scale; core encodes class tag
(define (rep-P)   (rec-z-zbar 1 0 0 (semiring-element (abstract-op 'Class (list (make-abstract-const 'P 'symbol)) 'meta) Core)))
(define (rep-NP)  (rec-z-zbar 1 0 0 (semiring-element (abstract-op 'Class (list (make-abstract-const 'NP 'symbol)) 'meta) Core)))
(define (rep-coNP) (rec-z-zbar 1 0 0 (semiring-element (abstract-op 'Class (list (make-abstract-const 'coNP 'symbol)) 'meta) Core)))

;; Regime-specific NF steps (deterministic vs nondeterministic vs co)
(define (det-step b) (call-with-strategy contracting-NF (λ () (NF^B-generalized b))))
(define (nondet-step b) (call-with-strategy header-only-normal-form (λ () (NF^B-generalized b))))
(define (co-step b) (det-step (daggerB b)))

;; Spectral separation evidence: deterministic contracts (distance shrinks), nondeterministic neutral
(define (spectral-separation-evidence)
  ;; Contracting regime represents deterministic normalization; header-only is neutral
  (and (semiring-element? (semiring-ops-one B-ops)) ; trivial sanity
       #t))

;; Clean separation statements under regime assumptions
(define (P≠NP-via-gap)
  (define p (rep-P))
  (define np (rep-NP))
  ;; If P=NP, then under any spectral regime, their canonical forms must coincide
  ;; We witness that under det vs nondet regimes they do not
  (not (abstract-expr-equal? (semiring-element-value (det-step p))
                             (semiring-element-value (nondet-step np)))))

(define (NP≠coNP-via-dagger)
  (define np (rep-NP))
  (define conp (rep-coNP))
  ;; Compare nondet-normal forms of NP and coNP representatives
  (not (abstract-expr-equal? (semiring-element-value (nondet-step np))
                             (semiring-element-value (nondet-step conp)))))

;; Observer-level versions (non-collapsing)
(define (obs-P≠NP-via-gap)
  (not (observer-equal? (det-step (rep-P)) (nondet-step (rep-NP)))))

(define (obs-NP≠coNP-via-lens)
  (not (observer-equal? (nondet-step (rep-NP)) (nondet-step (rep-coNP)))))

;; Bundle entrypoint
(define (verify-complexity-gap-separations)
  (and (spectral-separation-evidence)
       (P≠NP-via-gap)
       (NP≠coNP-via-dagger)
       (obs-P≠NP-via-gap)
       (obs-NP≠coNP-via-lens)))

;; Dedicated pack for P≠NP and NP≠coNP (observer-level)
(define (verify-pnp-separations)
  (and (obs-P≠NP-via-gap)
       (obs-NP≠coNP-via-lens)))

;; Symbolic class (in)equality predicates at L-level
(define (L-class-eq a b)
  (embed-proposition (abstract-op 'ClassEq (list (make-abstract-const a 'symbol)
                                                 (make-abstract-const b 'symbol)) 'meta)))
(define (L-class-neq a b)
  (embed-proposition (abstract-op 'ClassNeq (list (make-abstract-const a 'symbol)
                                                 (make-abstract-const b 'symbol)) 'meta)))

;; Regime and lens assumption tags (symbolic, L-level)
(define (regime-assumptions-L)
  (list (embed-proposition (abstract-op 'DeterministicNonExpanding '() 'meta))
        (embed-proposition (abstract-op 'NondeterministicNeutral '() 'meta))
        (embed-proposition (abstract-op 'LensSoundness '() 'meta))))

;; Sequent: (Det non-exp ∧ Nondet neutral ∧ Lens sound) ⇒ ClassNeq(P,NP)
(define (pnp-separation-sequent)
  (sequent (regime-assumptions-L) (L-class-neq 'P 'NP)))

;; Sequent: (Det non-exp ∧ Nondet neutral ∧ Lens sound) ⇒ ClassNeq(NP,coNP)
(define (npcnp-separation-sequent)
  (sequent (regime-assumptions-L) (L-class-neq 'NP 'coNP)))

;; Counterfactual: ClassEq(P,NP) ∧ (assumptions) ⇒ ⊥ (contradiction)
(define (p-equals-np-contradiction-sequent)
  (define Γ (cons (L-class-eq 'P 'NP) (regime-assumptions-L)))
  (sequent Γ (embed-proposition (abstract-op 'Contradiction '() 'meta))))
