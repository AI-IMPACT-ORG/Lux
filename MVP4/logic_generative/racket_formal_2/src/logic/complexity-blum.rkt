#lang racket
;; Blum-style complexity fragment and Karp-reduction closure, inside Lux

(require (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "./internalize.rkt")
         (file "./guarded-negation.rkt"))

(provide (all-defined-out))

;; Symbolic Blum measure and axioms
(define (blum-measure M x)
  (abstract-op 'BlumPhi (list M x) 'meta))

(define (blum-axiom1)
  ;; A1: φ is partial recursive (symbolic form)
  (embed-proposition (abstract-op 'BlumAxiom1 '() 'meta)))

(define (blum-axiom2)
  ;; A2: dom(φ_M) = dom(M) (symbolic)
  (embed-proposition (abstract-op 'BlumAxiom2 '() 'meta)))

(define (blum-axioms-sanity)
  (and (semiring-element? (blum-axiom1))
       (semiring-element? (blum-axiom2))))

;; Class predicates
(define (L-P) (embed-proposition (abstract-op 'Class (list (make-abstract-const 'P 'symbol)) 'meta)))
(define (L-NP) (embed-proposition (abstract-op 'Class (list (make-abstract-const 'NP 'symbol)) 'meta)))

;; DTIME/NTIME predicates with an abstract cost symbol f
(define (L-DTIME f) (embed-proposition (abstract-op 'DTIME (list f) 'meta)))
(define (L-NTIME f) (embed-proposition (abstract-op 'NTIME (list f) 'meta)))

;; Karp reduction predicate and closure rule
(define (L-KarpRed A B)
  (embed-proposition (abstract-op 'KarpRed (list A B) 'meta)))

;; Closure under Karp reductions in P: (KarpRed A B ∧ P(B)) ⇒ P(A)
(define (closure-under-karp)
  (define A (embed-proposition (abstract-op 'Lang (list (make-abstract-const 'A 'symbol)) 'meta)))
  (define B (embed-proposition (abstract-op 'Lang (list (make-abstract-const 'B 'symbol)) 'meta)))
  (define KR (L-KarpRed A B))
  (define PB (L-P))
  (gn-implies (gn-and KR PB) (L-P)))
