#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Moduli System (CLASS)
;;
;; Abstract flows over header components with optional parametric strategies.
;; Default contracting strategy is neutral (identity) in the abstract setting
;; to avoid injecting numeric behavior into proofs.

(require racket/contract
         racket/match
         racket/function
         racket/hash
         racket/list
         rackunit
         (file "../core.rkt")
         (file "../foundation/v2-axioms.rkt")
         (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../algebra/explog-decomposition.rkt")
         (file "../algebra/central-scalars.rkt"))

(provide (all-defined-out))

;; Flow function system
(struct abstract-flow-function (name domain codomain flow-fn properties) #:transparent)
(define (make-abstract-flow-function name domain codomain flow-fn . properties)
  (abstract-flow-function name domain codomain flow-fn properties))

(define polynomial-flow (make-abstract-flow-function 'polynomial 'integer 'integer (λ (x) (abstract-mul x (get-two))) '(monotonic increasing)))
(define exponential-flow (make-abstract-flow-function 'exponential 'integer 'integer (λ (x) (abstract-expt (get-two) x)) '(monotonic increasing)))
;; Safe log-floor: for non-positive or non-numeric inputs, return 0 to keep semantics abstract
;; Abstract-safe log-floor: keep symbolic unless definitively safe
(define (safe-log-floor x)
  (define xn (to-number x))
  (if (and xn (> xn 0))
      (abstract-floor (abstract-log x))
      (make-abstract-const 0 'integer)))
(define logarithmic-flow (make-abstract-flow-function 'logarithmic 'integer 'integer (λ (x) (safe-log-floor x)) '(monotonic increasing)))
(define trigonometric-flow (make-abstract-flow-function 'trigonometric 'integer 'integer (λ (x) (abstract-floor (abstract-sin x))) '(periodic bounded)))

(struct moduli-flow (name type flow-fn params) #:transparent)
(define (make-moduli-flow name type flow-fn . params) (moduli-flow name type flow-fn params))

(define μ_L (make-moduli-flow 'μ_L 'scale (abstract-flow-function-flow-fn polynomial-flow)))
(define θ_L (make-moduli-flow 'θ_L 'phase (abstract-flow-function-flow-fn exponential-flow)))
(define μ_R (make-moduli-flow 'μ_R 'scale (abstract-flow-function-flow-fn logarithmic-flow)))
(define θ_R (make-moduli-flow 'θ_R 'phase (abstract-flow-function-flow-fn trigonometric-flow)))

(define (make-expanding-flow name) (make-moduli-flow name 'phase (λ (x) (* x 2))))
(define (make-contracting-flow name) (make-moduli-flow name 'phase (λ (x) (quotient x 2))))
(define (make-neutral-flow name) (make-moduli-flow name 'phase (λ (x) x)))
(define (make-polynomial-flow name coeffs) (make-moduli-flow name 'phase (λ (x) (apply + (map (λ (c i) (* c (expt x i))) coeffs (range (length coeffs)))))))
(define (make-symbolic-flow name) (make-moduli-flow name 'phase (λ (x) (make-abstract-symbol (string->symbol (format "f~a" x))))))

(define (compose-moduli-flows flow1 flow2)
  (make-moduli-flow (string->symbol (format "~a∘~a" (moduli-flow-name flow2) (moduli-flow-name flow1)))
                    (moduli-flow-type flow1)
                    (compose (moduli-flow-flow-fn flow2) (moduli-flow-flow-fn flow1))))

(struct r-data-matrix (matrix) #:transparent)
(define identity-r-data (r-data-matrix '((1 0) (0 1))))
(define custom-r-data (r-data-matrix '((2/3 1/3) (1/3 2/3))))
(define (split-scale-headers m_Λ r-data)
  (match-let ([(r-data-matrix matrix) r-data])
    (let ([m-z-coeff (caar matrix)] [m-z̄-coeff (cadar matrix)])
      (list (* m_Λ m-z-coeff) (* m_Λ m-z̄-coeff)))))
(define *current-r-data* identity-r-data)
(define (set-r-data! r-data) (set! *current-r-data* r-data))
(define (get-current-r-data) *current-r-data*)

(struct moduli-increment-strategy (phase-fn scale-z-fn scale-z̄-fn) #:transparent)
(define (make-flow-based-increment μ_L θ_L μ_R θ_R)
  (moduli-increment-strategy (λ (k) (- ((moduli-flow-flow-fn θ_L) k) k))
                             (λ (m_z) (- ((moduli-flow-flow-fn μ_L) m_z) m_z))
                             (λ (m_z̄) (- ((moduli-flow-flow-fn μ_R) m_z̄) m_z̄))))
(define sign-based-increment (moduli-increment-strategy (λ (k) (if (> k 0) 1 (if (< k 0) -1 0)))
                                                        (λ (m_z) (if (> m_z 0) 1 (if (< m_z 0) -1 0)))
                                                        (λ (m_z̄) (if (> m_z̄ 0) 1 (if (< m_z̄ 0) -1 0)))))
(define symbolic-increment (moduli-increment-strategy (λ (k) (make-abstract-symbol (string->symbol (format "Δk~a" k))))
                                                      (λ (m_z) (make-abstract-symbol (string->symbol (format "Δm_z~a" m_z))))
                                                      (λ (m_z̄) (make-abstract-symbol (string->symbol (format "Δm_z̄~a" m_z̄))))))
(define *current-increment-strategy* sign-based-increment)
(define (set-increment-strategy! strategy) (set! *current-increment-strategy* strategy))

(struct normal-form-strategy (name nf-fn params) #:transparent)
(define identity-normal-form (normal-form-strategy 'identity (λ (t) t) '()))
(define header-only-normal-form (normal-form-strategy 'header-only (λ (t)
  (define d (dec-z-zbar t)) (rec-z-zbar (first d) (second d) (third d) (fourth d))) '()))
(define (lexicographic-tropical-normalize-headers k m mz) (list k m mz))
(define lexicographic-tropical-normal-form (normal-form-strategy 'lexicographic-tropical (λ (t)
  (define d (dec-z-zbar t))
  (define H (lexicographic-tropical-normalize-headers (first d) (second d) (third d)))
  (rec-z-zbar (first H) (second H) (third H) (fourth d))) '()))

(define (NF-parametric μ θ b)
  (define d (dec-z-zbar b))
  (define fθ ((moduli-flow-flow-fn θ) (first d)))
  (define gμz ((moduli-flow-flow-fn μ) (second d)))
  (define gμzb ((moduli-flow-flow-fn μ) (third d)))
  (rec-z-zbar fθ gμz gμzb (fourth d)))
(define (NF-B-parametric μ θ b) (NF-parametric μ θ b))
(define (NF-parametric-multi flows b)
  (define d (dec-z-zbar b))
  (define k (for/fold ([k (first d)]) ([pair flows]) (match pair [(list μ θ) ((moduli-flow-flow-fn θ) k)] [_ k])))
  (define mz (for/fold ([m (second d)]) ([pair flows]) (match pair [(list μ θ) ((moduli-flow-flow-fn μ) m)] [_ m])))
  (define mzb (for/fold ([m (third d)]) ([pair flows]) (match pair [(list μ θ) ((moduli-flow-flow-fn μ) m)] [_ m])))
  (rec-z-zbar k mz mzb (fourth d)))

(struct parametric-normal-form-strategy (flows) #:transparent)
(define (make-parametric-normal-form flows) (parametric-normal-form-strategy flows))
(define (parametric-nf-fn strategy)
  (match strategy [(parametric-normal-form-strategy flows) (λ (b) (NF-parametric-multi flows b))]
                 [_ (λ (b) b)]))
;; Default parametric strategies: keep contracting neutral (identity) in abstract setting
(define expanding-parametric-strategy (make-parametric-normal-form (list (list μ_L θ_L) (list μ_R θ_R))))
(define contracting-parametric-strategy (make-parametric-normal-form '()))
(define *current-normal-form-strategy* identity-normal-form)
(define (set-normal-form-strategy! strategy) (set! *current-normal-form-strategy* strategy))
(define (NF^B-generalized b) ((normal-form-strategy-nf-fn *current-normal-form-strategy*) b))

;; B-valued normaliser [[·]]_{μ,θ}: alias to header-only normalization in the
;; reference mechanisation. This matches the paper's B-normaliser in ports.
(define (B-normalize b)
  ((normal-form-strategy-nf-fn header-only-normal-form) b))

(struct generalized-coupling (name coupling-fn domain codomain) #:transparent)
(struct generalized-metric (name metric-fn space properties) #:transparent)
(struct rg-flow (name coupling metric convergence-fn fixed-points) #:transparent)
(struct rg-truth (statement coupling metric proof-method confidence) #:transparent)
(define (make-generalized-coupling name coupling-fn domain codomain) (generalized-coupling name coupling-fn domain codomain))
(define (make-generalized-metric name metric-fn space properties) (generalized-metric name metric-fn space properties))
(define (make-rg-flow name coupling metric convergence-fn fixed-points) (rg-flow name coupling metric convergence-fn fixed-points))
(define (make-rg-truth statement coupling metric proof-method confidence) (rg-truth statement coupling metric proof-method confidence))
(define (couple-elements coupling x y) ((generalized-coupling-coupling-fn coupling) x y))
(define (couple-sequence coupling elements) (foldl (generalized-coupling-coupling-fn coupling) (first elements) (rest elements)))
(define (metric-distance metric x y) ((generalized-metric-metric-fn metric) x y))
(define (metric-convergence? metric seq tol) (if (< (length seq) 2) #t (andmap (λ (d) (< d tol)) (map (λ (i) (metric-distance metric (list-ref seq i) (list-ref seq (+ i 1)))) (range (- (length seq) 1))))))

(define (normal-form-4mod t)
  (define d (dec-z-zbar t))
  (list (first d) (abstract-add (second d) (third d)) (fourth d)))
(define (normal-form-B-4mod t)
  (define nf (normal-form-4mod t))
  (rec-z-zbar (list-ref nf 0) 0 0 (list-ref nf 2)))

(define (test-flow-compatibility)
  (define θ1+θ2 (compose-moduli-flows θ_L θ_R))
  (define μ1+μ2 (compose-moduli-flows μ_L μ_R))
  (define test-x 5)
  (and (= ((moduli-flow-flow-fn θ1+θ2) test-x) ((moduli-flow-flow-fn θ_R) ((moduli-flow-flow-fn θ_L) test-x)))
       (= ((moduli-flow-flow-fn μ1+μ2) test-x) ((moduli-flow-flow-fn μ_R) ((moduli-flow-flow-fn μ_L) test-x)))))

(define (run-moduli-system-tests)
  (displayln "=== V10 CLASS Moduli System Tests (Lux) ===")
  (check-true (moduli-flow? μ_L))
  (check-true (moduli-flow? θ_L))
  (check-true (moduli-flow? μ_R))
  (check-true (moduli-flow? θ_R))
  (check-true (test-flow-compatibility))
  (define test-term (semiring-element 2.0 B))
  (define nf-result (normal-form-4mod test-term))
  (check-true (list? nf-result))
  (check-equal? (length nf-result) 3)
  (define b-result (normal-form-B-4mod test-term))
  (check-true (semiring-element? b-result))
  (check-equal? (semiring-element-semiring-type b-result) B)
  (check-true (semiring-element? z))
  (check-true (semiring-element? z̄))
  (check-true (semiring-element? Λ))
  (check-equal? (semiring-element-semiring-type z) B)
  (check-equal? (semiring-element-semiring-type z̄) B)
  (check-equal? (semiring-element-semiring-type Λ) B)
  (displayln "=== All Moduli System Tests (Lux) Passed ==="))
