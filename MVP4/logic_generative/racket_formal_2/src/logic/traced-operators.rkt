#lang racket
;; Traced operators (JSV-style) at the L-level: reusable across ports

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./internalize.rkt")
         (file "./inference.rkt")
         (file "./sequent-checker.rkt"))

(provide (all-defined-out))

;; Meta constructors
(define (b-trace F X)              (abstract-op 'Trace (list (make-abstract-const F 'symbol)
                                                            (make-abstract-const X 'symbol)) 'meta))
(define (b-trace-lipschitz F X c)  (abstract-op 'TraceLipschitz (list (make-abstract-const F 'symbol)
                                                                     (make-abstract-const X 'symbol)
                                                                     (make-abstract-const c 'real)) 'meta))
(define (b-trace-neutral F X)      (abstract-op 'TraceNeutral (list (make-abstract-const F 'symbol)
                                                                   (make-abstract-const X 'symbol)) 'meta))
(define (b-trace-natural ν F X)    (abstract-op 'TraceNatural (list (make-abstract-const ν 'symbol)
                                                                   (make-abstract-const F 'symbol)
                                                                   (make-abstract-const X 'symbol)) 'meta))

;; L lifts
(define (L-trace F X)             (embed-proposition (b-trace F X)))
(define (L-trace-lipschitz F X c) (embed-proposition (b-trace-lipschitz F X c)))
(define (L-trace-neutral F X)     (embed-proposition (b-trace-neutral F X)))
(define (L-trace-natural ν F X)   (embed-proposition (b-trace-natural ν F X)))

;; Sequent templates
(define (trace-lipschitz-sequent F X c)
  (sequent (list (L-trace F X)) (L-trace-lipschitz F X c)))

(define (trace-neutrality-sequent F X)
  (sequent (list (L-trace F X)) (L-trace-neutral F X)))

(define (trace-naturality-sequent ν F X)
  (sequent (list (L-trace F X)) (L-trace-natural ν F X)))

;; Small sanity pack
(define (traced-operators-pack)
  (and (semiring-element? (trace-lipschitz-sequent 'F_Rdet 'X_witness (make-abstract-const 9/10 'real)))
       (semiring-element? (trace-neutrality-sequent 'F_Rnd 'X_witness))
       (semiring-element? (trace-naturality-sequent 'nu_L 'F_Rdet 'X_witness))))

