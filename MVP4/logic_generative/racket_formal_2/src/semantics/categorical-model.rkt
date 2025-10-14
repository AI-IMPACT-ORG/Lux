#lang racket
;; Categorical + metric enrichment semantics (dagger SMC + Lawvere metric) and lens Lipschitz claims

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/internalize.rkt")
         (file "../logic/inference.rkt")
         (file "../logic/sequent-checker.rkt"))

(provide (all-defined-out))

;; Boolean/meta constructors for categorical/metric props
(define (b-dagger-smc) (abstract-op 'DaggerSMC '() 'meta))
(define (b-lawvere-metric obj) (abstract-op 'LawvereMetric (list (make-abstract-const obj 'symbol)) 'meta))
(define (b-lipschitz f c) (abstract-op 'Lipschitz (list (make-abstract-const f 'symbol)
                                                        (make-abstract-const c 'real)) 'meta))

;; Lift to L
(define (L-dagger-smc) (embed-proposition (b-dagger-smc)))
(define (L-lawvere-metric obj) (embed-proposition (b-lawvere-metric obj)))
(define (L-lipschitz f c) (embed-proposition (b-lipschitz f c)))

;; Lens functors and constants (symbolic names)
(define (L-Rdet) (embed-proposition (abstract-op 'Lens (list (make-abstract-const 'Rdet 'symbol)) 'meta)))
(define (L-Rnd)  (embed-proposition (abstract-op 'Lens (list (make-abstract-const 'Rnd 'symbol)) 'meta)))

;; Sequent pack: DaggerSMC ∧ LawvereMetric(B) ∧ Lipschitz(Rdet,c) ∧ Lipschitz(Rnd,1) ⊢ Consistent
(define (semantics-sequent)
  (define Γ (list (L-dagger-smc)
                  (L-lawvere-metric 'B)
                  (L-lipschitz 'Rdet (make-abstract-const 9/10 'real))
                  (L-lipschitz 'Rnd (make-abstract-const 1 'real))))
  (sequent Γ (embed-proposition (abstract-op 'Consistent '() 'meta))))

;; Minimal derivation sanity: build a simple and-intro step witness
(define (semantics-derivation-check)
  (define A (L-dagger-smc))
  (define B (L-lawvere-metric 'B))
  (define wit (rule-and-intro (list A) B A))
  (check-step (deriv-step 'and-intro (list (list A) B A) wit)))

(define (semantics-pack)
  (and (semiring-element? (semantics-sequent))
       (semantics-derivation-check)))

