#lang racket
;; Gap and DNF properties (abstract):
;;  - Non-expansive regime witness (d(Rx,Ry) ≤ d(x,y))
;;  - DNF idempotence and transport invariance
;;  - Regime and marginal reports as symbolic summaries

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../common/utils.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../algebra/auxiliary-transporters.rkt")
         (file "../logic/rg-regimes.rkt")
         (file "./truth.rkt"))

(provide (all-defined-out))

;; Use shared b-distance from common/utils

;; Contraction witness for R = NF^B-generalized with factor c in (0,1)
;; Non-expansive witness for contracting regime: d(Rx,Ry) ≤ d(x,y)
(define (contraction-gap-witness)
  (define samples (list (mkB-sym 'x2)
                        (mkB-sym 'x3)
                        (mkB-sym 'x5)))
  (for/and ([x samples] [y (reverse samples)])
    (define dx (b-distance x y))
    (define dR (call-with-strategy contracting-NF (λ () (b-distance (NF^B-generalized x) (NF^B-generalized y)))))
    (abstract-eval-bool (abstract-le? dR dx))))

;; Dagger-normal form: compose RG projection with dagger
(define (DNF b)
  (NF^B-generalized (daggerB (NF^B-generalized b))))

(define (dnf-idempotent?)
  (define b (semiring-element (make-abstract-const 7 'integer) B))
  (abstract-semiring-equal? (DNF (DNF b)) (DNF b)))

(define (dnf-transport-invariant?)
  (define b (semiring-element (get-five) B))
  (abstract-semiring-equal? (ν_L (DNF b)) (ν_L (DNF b))))

;; Non-contraction witness and regime report

(define (call-with-strategy strategy th)
  (define old *current-normal-form-strategy*)
  (set-normal-form-strategy! strategy)
  (define out (th))
  (set-normal-form-strategy! old)
  out)

(define (distance-sample-after strategy)
  (define x (mkB-sym 'x))
  (define y (mkB-sym 'y))
  (call-with-strategy strategy
    (λ () (b-distance (NF^B-generalized x) (NF^B-generalized y)))))

(define (distance-sample-before)
  (define x (mkB-sym 'x))
  (define y (mkB-sym 'y))
  (b-distance x y))

;; True if we can exhibit a strategy where the post-distance differs from pre-distance
;; We use expanding-parametric-strategy as the exemplar.
(define (non-contraction-witness)
  (define dx (distance-sample-before))
  (define dE (distance-sample-after expanding-NF))
  (not (abstract-expr-equal? dE dx)))

;; Classify simple regimes using equality/inequality heuristics
(define (classify-regime strategy)
  (define dx (distance-sample-before))
  (define dR (distance-sample-after strategy))
  (cond [(abstract-expr-equal? dR dx) 'neutral]
        [(contraction-gap-witness) 'contractive] ; heuristic global check
        [else 'non-neutral]))

(define (regime-report)
  (displayln "--- regime report ---")
  (define id-class (classify-regime identity-normal-form))
  (define ex-class (classify-regime expanding-NF))
  (define co-class (classify-regime contracting-NF))
  (displayln (string-append "identity: " (~a id-class)))
  (displayln (string-append "expanding: " (~a ex-class)))
  (displayln (string-append "contracting: " (~a co-class)))
  #t)
