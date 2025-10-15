#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/auxiliary-transporters.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../common/utils.rkt")
         (file "../logic/rg-regimes.rkt"))

(provide (all-defined-out))

;; Dagger (involution) at B-level: use starB (swap headers)
(define (daggerB b) (starB b))

;; RG fixed-point: NF^B-generalized(b) = b
(define (rg-fixed-point? b)
  (abstract-semiring-equal? (NF^B-generalized b) b))

;; Reversible truth at B: RG-fixed and dagger-invariant
(define (reversible-truth? b)
  (and (rg-fixed-point? b)
       (abstract-semiring-equal? (daggerB b) b)))

;; Global→Local truth demonstration on canonical bulk-one
(define (global-local-truth-demo)
  (define b1 B-one)
  (and (reversible-truth? b1)
       (equal? (ν_L b1) (semiring-ops-one L-ops))
       (equal? (ν_R b1) (semiring-ops-one R-ops))))

;; Truth pack: canonical composition and transport preservation for local truths
(require (file "../logic/guarded-negation.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt"))

(define (truth-conjunction-canonical)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define Q (embed-proposition (make-abstract-const 'Q 'symbol)))
  (define sP (sequent '() P))
  (define sQ (sequent '() Q))
  (define sAnd (sequent '() (gn-and P Q)))
  (gn-iff sAnd (gn-and sP sQ)))

(define (truth-transport-preservation)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (define s (sequent '() P))
  (abstract-semiring-equal? (ν_L (ι_L s)) s))

(define (truth-imp-reflexive)
  (define P (embed-proposition (make-abstract-const 'P 'symbol)))
  (sequent '() (gn-implies P P)))

;; Marginal (c=1) truths along a modal/quote-like diagonal (Gödel-style axis)
;; Build a core-only B element carrying a Prov(var s) payload
(define (make-godel-core s)
  (define v (abstract-op 'var (list (make-abstract-const s 'symbol)) 'boolean))
  (define p (abstract-op 'Prov (list v) 'boolean))
  (rec-z-zbar 0 0 0 (semiring-element p Core)))

(define (c1-invariance? b1 b2)
  (define dx (b-distance b1 b2))
  (define dH (call-with-strategy header-only-normal-form
                 (λ () (b-distance (NF^B-generalized b1) (NF^B-generalized b2)))))
  (define dI (call-with-strategy identity-normal-form
                 (λ () (b-distance (NF^B-generalized b1) (NF^B-generalized b2)))))
  (and (abstract-expr-equal? dH dx)
       (abstract-expr-equal? dI dx)))

(define (marginal-axis-demo)
  (define gP (make-godel-core 'P))
  (define gQ (make-godel-core 'Q))
  (c1-invariance? gP gQ))

(define (marginal-truth-demo)
  (define gP (make-godel-core 'P))
  (and (reversible-truth? gP)
       (marginal-axis-demo)))

(define (marginal-report)
  (displayln "--- marginal report ---")
  (displayln (string-append "c=1 along Gödel axis: " (if (marginal-axis-demo) "ok" "fail")))
  (displayln (string-append "reversible sample: " (if (marginal-truth-demo) "ok" "fail")))
  #t)
