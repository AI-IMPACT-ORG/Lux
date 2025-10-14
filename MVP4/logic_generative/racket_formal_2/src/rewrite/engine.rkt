#lang racket
;; Rewrite engine (abstract):
;;  - equational normalization via symbolic rules to a bounded fixpoint
;;  - reduction under a provided normal-form strategy (no numeric evaluation)

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../common/utils.rkt")
         (file "../logic/rg-regimes.rkt")
         (file "./rules.rkt"))

(provide (all-defined-out))

;; equal-el? provided by common/utils

(define (apply-rules once rules x)
  (for/fold ([acc x]) ([r rules])
    (if ((rewrite-rule-guard r) acc)
        ((rewrite-rule-apply r) acc)
        acc)))

;; Equational normalization: iterate eq rules to a fixpoint (bounded)
(define (normalize-E x #:max-steps [n 5])
  (let loop ([i n] [cur x])
    (define nxt (apply-rules #t eq-rules cur))
    (if (or (zero? i) (equal-el? nxt cur))
        nxt
        (loop (sub1 i) nxt))))

;; Reduction: apply red rules once under a given strategy
(define (reduce-R x #:strategy [strategy identity-normal-form])
  (call-with-strategy strategy (λ () (apply-rules #t red-rules x))))

;; Sample checks for verification
(define (rewrite-eq-roundtrip?)
  (define P (semiring-element (abstract-op 'prop (list (abstract-op 'and (list (make-abstract-const #t 'boolean)
                                                                            (make-abstract-const #f 'boolean)) 'boolean)) 'boolean) L))
  (equal-el? (normalize-E (normalize-E P)) (normalize-E P)))

(define (rewrite-red-noninvertible?)
  (define b (mkB-sym 'b0))
  ;; Use expanding regime to witness a nontrivial reduction step in the abstract setting
  (define r1 (reduce-R b #:strategy expanding-NF))
  (not (equal-el? b r1)))

(define (rewrite-metric-monotone?)
  ;; Check d(Rx,Ry) ≤ d(x,y) for a sample under contracting strategy (non-expansive)
  (define x (mkB-sym 'x))
  (define y (mkB-sym 'y))
  (define dx (b-distance x y))
  (define dR (call-with-strategy contracting-NF (λ () (b-distance (NF^B-generalized x) (NF^B-generalized y)))))
  (abstract-eval-bool (abstract-le? dR dx)))
