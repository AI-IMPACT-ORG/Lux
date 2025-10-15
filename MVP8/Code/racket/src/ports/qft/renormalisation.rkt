#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; QFT renormalisation sequents: scheme independence, Callan–Symanzik, Ward/BRST

(require (file "../../foundations/abstract-core.rkt")
         (file "../../algebra/algebraic-structures.rkt")
         (file "../../logic/internalize.rkt")
         (file "../../logic/inference.rkt")
         (file "../../logic/traced-operators.rkt"))

(provide (all-defined-out))

(define (L-rc-universal label)
  (embed-proposition (abstract-op 'RCUniversal (list (make-abstract-const label 'symbol)) 'meta)))

(define (L-scheme-independent label)
  (embed-proposition (abstract-op 'SchemeIndependent (list (make-abstract-const label 'symbol)) 'meta)))

(define (scheme-independence-sequent label)
  (sequent (list (L-rc-universal label)) (L-scheme-independent label)))

(define (L-cs label)
  (embed-proposition (abstract-op 'CallanSymanzik (list (make-abstract-const label 'symbol)) 'meta)))

(define (callan-symanzik-sequent label)
  (define Γ (list (L-trace 'Rdet 'X_RG)
                  (L-trace-lipschitz 'Rdet 'X_RG (make-abstract-const 9/10 'real))
                  (embed-proposition (abstract-op 'ScaleSemantics (list (make-abstract-const label 'symbol)) 'meta))))
  (sequent Γ (L-cs label)))

(define (L-gauge label) (embed-proposition (abstract-op 'GaugeInvariant (list (make-abstract-const label 'symbol)) 'meta)))
(define (L-brst label) (embed-proposition (abstract-op 'BRSTNilpotent (list (make-abstract-const label 'symbol)) 'meta)))
(define (L-ward label) (embed-proposition (abstract-op 'WardIdentity (list (make-abstract-const label 'symbol)) 'meta)))

(define (ward-identity-sequent label)
  (sequent (list (L-gauge label) (L-brst label)) (L-ward label)))

(define (renorm-pack)
  (and (semiring-element? (scheme-independence-sequent 'qft-default))
       (semiring-element? (callan-symanzik-sequent 'qft-default))
       (semiring-element? (ward-identity-sequent 'qft-default))))

