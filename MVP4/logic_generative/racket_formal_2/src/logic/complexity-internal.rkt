#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Internal DTIME/NTIME skeleton and lens soundness

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../logic/rg-regimes.rkt")
         (file "./internalize.rkt")
         (file "./guarded-negation.rkt")
         (file "../common/utils.rkt")
         (file "../theorems/complexity-separation.rkt")
         (file "../theorems/complexity-lens.rkt"))

(provide (all-defined-out))

;; Symbolic class predicates (L-level via embedding)
(define (L-Class sym)
  (embed-proposition (abstract-op 'Class (list (make-abstract-const sym 'symbol)) 'meta)))

(define (L-P) (L-Class 'P))
(define (L-NP) (L-Class 'NP))
(define (L-coNP) (L-Class 'coNP))

(define (L-DTIME f)
  (embed-proposition (abstract-op 'DTIME (list f) 'meta)))

(define (L-NTIME f)
  (embed-proposition (abstract-op 'NTIME (list f) 'meta)))

;; Karp reduction skeleton (symbolic)
(define (L-KarpRed A B)
  (embed-proposition (abstract-op 'KarpRed (list A B) 'meta)))

;; Lens soundness: under deterministic lens, P/DTIME invariants reflect as identical observers;
;; under nondeterministic (header-only) lens, NP/NTIME invariants reflect as identical observers.

(define (header-only-nf b)
  (call-with-strategy header-only-normal-form (λ () (NF^B-generalized b))))

(define (obs-eq x y)
  (and (abstract-semiring-equal? (nu-L-raw x) (nu-L-raw y))
       (abstract-semiring-equal? (nu-R-raw x) (nu-R-raw y))))

(define (soundness-under-lenses)
  (header-only-idempotent-on-canonical))

;; Sanity pack: expose L-level witnesses for class predicates (trivial embeddings)
(define (complexity-internal-sanity)
  (and (semiring-element? (L-P))
       (semiring-element? (L-NP))
       (semiring-element? (L-coNP))
       (semiring-element? (L-DTIME (make-abstract-const 'n^k 'term)))
       (semiring-element? (L-NTIME (make-abstract-const 'n^k 'term)))))
