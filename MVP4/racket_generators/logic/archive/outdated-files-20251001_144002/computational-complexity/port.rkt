#lang racket

(require racket/match
         "../../../core/signature.rkt"
         "../../../core/nf.rkt"
         "../../../core/observers.rkt"
         "../../../core/cumulants.rkt"
         "../../../core/delta.rkt"
         "../../../core/kernel.rkt"
         "../../feynman.rkt")

(provide (struct-out computation-port)
         make-computation-port
         computation-encode-term
         computation-normalise
         computation-run
         computation-complexity
         computation-explain-complexity
         computation-complexity-strict
         computation-certificate
         computation-coupling
         computation-sum-over-histories)

;; A unified computation port that exposes Church (lambda), Turing (machines), and
;; Feynman (histories) via a single coherent façade.

(struct computation-port (signature flavour)
  #:transparent)

(define (make-computation-port #:signature [signature (current-signature)]
                               #:flavour [flavour 'agnostic])
  (computation-port signature flavour))

;; Encode a term into a computation artifact (sexp) for portability
(define (computation-encode-term term)
  (list 'comp-term (term-name term) (term-header term) (term-core term)))

;; Normalise a term as the canonical program semantics (Church view)
(define (computation-normalise term)
  (normal-form term))

;; Run a computation: lightweight façade combining Church/Turing/Feynman
;; Returns a record with nf, delta-nf, and a simple cost proxy
(define (computation-run term)
  (define nf (normal-form term))
  (define dterm (delta term))
  (define dnf (normal-form dterm))
  (define cost (+ (nf-phase nf) (nf-scale nf)))
  (list 'run
        'nf nf
        'delta-nf dnf
        'cost cost))

;; Heuristic complexity estimator returning one of 'P 'NP 'PSPACE 'EXP
(define (computation-complexity term)
  (define nf (normal-form term))
  (define dnf (normal-form (delta term)))
  (define cost (+ (nf-phase nf) (nf-scale nf)))
  ;; simple nondeterminism proxy via multiple histories
  (clear-histories!)
  (push-history! (list term))
  (when (and (list? (term-core term)) (>= (length (term-core term)) 2))
    (push-history! (list term)))
  (define nondet? (> (length (histories)) 1))
  (define delta-growth? (or (> (nf-phase dnf) (nf-phase nf))
                            (> (nf-scale dnf) (nf-scale nf))))
  (cond
    [(and (number? cost) (<= cost 2) (not nondet?) (not delta-growth?)) 'P]
    [(and (not delta-growth?) nondet?) 'NP]
    [(and (number? cost) (<= cost 10)) 'PSPACE]
    [else 'EXP]))

(define (computation-explain-complexity term)
  (define nf (normal-form term))
  (define dnf (normal-form (delta term)))
  (define cls (computation-complexity term))
  (list 'complexity
        'class cls
        'nf-phase (nf-phase nf)
        'nf-scale (nf-scale nf)
        'delta-phase (nf-phase dnf)
        'delta-scale (nf-scale dnf)))

;; Strict mode: only classify if Δ monotonicity (soundness) holds
(define (computation-complexity-strict term)
  (define nf (normal-form term))
  (define dnf (normal-form (delta term)))
  (define cost (+ (nf-phase nf) (nf-scale nf)))
  ;; Δ monotonicity check: phase and scale should not decrease under Δ
  (define delta-monotonic? (and (>= (nf-phase dnf) (nf-phase nf))
                                (>= (nf-scale dnf) (nf-scale nf))))
  ;; Additional soundness: NF should be well-formed
  (define nf-well-formed? (and (number? (nf-phase nf))
                               (number? (nf-scale nf))
                               (not (eq? (nf-core nf) 'undefined))))
  (if (and delta-monotonic? nf-well-formed?)
      (computation-complexity term)
      'UNSOUND))

;; Certificate object logging structural conditions used
(define (computation-certificate term)
  (define nf (normal-form term))
  (define dnf (normal-form (delta term)))
  (define cost (+ (nf-phase nf) (nf-scale nf)))
  (define delta-monotonic? (and (>= (nf-phase dnf) (nf-phase nf))
                                (>= (nf-scale dnf) (nf-scale nf))))
  (define nf-well-formed? (and (number? (nf-phase nf))
                               (number? (nf-scale nf))
                               (not (eq? (nf-core nf) 'undefined))))
  ;; Nondeterminism proxy
  (clear-histories!)
  (push-history! (list term))
  (when (and (list? (term-core term)) (>= (length (term-core term)) 2))
    (push-history! (list term)))
  (define nondet? (> (length (histories)) 1))
  (define delta-growth? (or (> (nf-phase dnf) (nf-phase nf))
                            (> (nf-scale dnf) (nf-scale nf))))
  (define cls (computation-complexity term))
  (list 'certificate
        'class cls
        'delta-monotonic delta-monotonic?
        'nf-well-formed nf-well-formed?
        'cost cost
        'nondeterministic nondet?
        'delta-growth delta-growth?
        'soundness-proxy (and delta-monotonic? nf-well-formed?)
        'conditions (list
                     (if (<= cost 2) 'low-cost 'high-cost)
                     (if nondet? 'nondeterministic 'deterministic)
                     (if delta-growth? 'delta-growing 'delta-stable)
                     (if (and delta-monotonic? nf-well-formed?) 'sound 'unsound))))

;; Coupling extraction (g) as an algorithmic observable
(define (computation-coupling i)
  (value-g i))

;; Feynman aggregation in the computation view
(define (computation-sum-over-histories)
  (define test-kernel (kernel kernel-header-zero (transition 'computation (λ (term) term) '())))
  (sum-over-histories test-kernel 3))


