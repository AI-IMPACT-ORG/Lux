#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.
;; Exponential/Logarithmic Decomposition and NF

 (require racket/function
          racket/list
          (file "../foundations/abstract-core.rkt")
          (file "./algebraic-structures.rkt")
          (file "./central-scalars.rkt"))

(provide (all-defined-out))

(define (z3-model?)
  (let ([v (getenv "LUX_HEADER_MODEL")]) (and v (string-ci=? v "Z3"))))

(define (flatten-mul e)
  (cond
    [(and (abstract-op? e) (eq? (abstract-op-operator e) 'mul))
     (append (flatten-mul (first (abstract-op-operands e)))
             (flatten-mul (second (abstract-op-operands e))))]
    [else (list e)]))

(define (dec-z-zbar b)
  (define v (origin-strip-value (semiring-element-value b)))
  (cond
    [(and (abstract-op? v) (eq? (abstract-op-operator v) 'RecTag))
     (define ops (abstract-op-operands v))
     (list (abstract-const-value (first ops))
           (abstract-const-value (second ops))
           (abstract-const-value (third ops))
           (semiring-element (fourth ops) Core))]
    [(z3-model?)
     ;; Try to extract exponents of φ, z, z̄ and reconstruct core as product of remaining factors
     (define factors (flatten-mul v))
     (define (is-expt-of base e)
       (and (abstract-op? e)
            (eq? (abstract-op-operator e) 'expt)
            (abstract-expr-equal? (first (abstract-op-operands e)) base)
            (abstract-const? (second (abstract-op-operands e)))))
     (define φ (get-φ))
     (define z (get-z))
     (define z̄ (get-z̄))
     (define k 0)
     (define mz 0)
     (define mzb 0)
     (define rest-factors '())
     (for ([f factors])
       (cond
         [(is-expt-of φ f) (set! k (abstract-const-value (second (abstract-op-operands f))))]
         [(is-expt-of z f) (set! mz (abstract-const-value (second (abstract-op-operands f))))]
         [(is-expt-of z̄ f) (set! mzb (abstract-const-value (second (abstract-op-operands f))))]
         [else (set! rest-factors (cons f rest-factors))]))
     (define core-v (cond
                      [(null? rest-factors) (get-one)]
                      [(null? (cdr rest-factors)) (car rest-factors)]
                      [else (foldl (λ (a acc) (abstract-mul a acc)) (car rest-factors) (cdr rest-factors))]))
     (list k mz mzb (semiring-element core-v Core))]
    [else
     ;; Abstract default: zero headers + carry payload to Core, canonically ordered
     (define fs (flatten-mul v))
     (define sfs (sort fs (λ (a b) (string<? (~a a) (~a b)))))
     (define core-v (cond
                      [(null? sfs) (get-one)]
                      [(null? (cdr sfs)) (car sfs)]
                      [else (foldl (λ (a acc) (abstract-mul a acc)) (car sfs) (cdr sfs))]))
     (list 0 0 0 (semiring-element core-v Core))]))

(define (rec-z-zbar k mz mzb core)
  (define cv (semiring-element-value core))
  (cond
    [(and (eq? k 0) (eq? mz 0) (eq? mzb 0)) (semiring-element cv B)]
    [(z3-model?)
     (semiring-element
      (abstract-mul (abstract-mul (abstract-expt (get-φ) (make-abstract-const k 'integer))
                                  (abstract-expt (get-z) (make-abstract-const mz 'integer)))
                    (abstract-mul (abstract-expt (get-z̄) (make-abstract-const mzb 'integer)) cv))
      B)]
    [else
     (semiring-element (abstract-op 'RecTag (list (make-abstract-const k 'integer)
                                                  (make-abstract-const mz 'integer)
                                                  (make-abstract-const mzb 'integer)
                                                  cv)
                                    'tuple)
                       B)]) )

(define (collapse k mz mzb core)
  (list k (+ mz mzb) core))

(define (NF-B t)
  (define d (dec-z-zbar t))
  (collapse (first d) (second d) (third d) (fourth d)))

(define (test-exp-log-isomorphism b)
  (define d (dec-z-zbar b))
  (define r (apply rec-z-zbar d))
  (and (semiring-element? r)
       (eq? (semiring-element-semiring-type r) B)
       (abstract-expr-equal? (origin-strip-value (semiring-element-value b))
                             (origin-strip-value (semiring-element-value r)))))

(define (test-header-factoring b)
  (test-exp-log-isomorphism b))

(define (test-multiplicative-compatibility t u)
  (define tt (semiring-element t B))
  (define uu (semiring-element u B))
  (define tu ((semiring-ops-mul B-ops) tt uu))
  (define dt (dec-z-zbar tt))
  (define du (dec-z-zbar uu))
  (define dtu (dec-z-zbar tu))
  (and (eq? (first dtu) (+ (first dt) (first du)))
       (eq? (second dtu) (+ (second dt) (second du)))
       (eq? (third dtu) (+ (third dt) (third du)))
       (abstract-semiring-equal? (fourth dtu)
                                 ((semiring-ops-mul Core-ops)
                                  (fourth dt) (fourth du)))))
