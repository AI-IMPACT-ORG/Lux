#lang racket
; (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use.

;; Lux Ops Test Suite
;; Comprehensive test runner for Lux Ops functionality (formerly V10 Class)
;; Tests guarded negation, domain ports, Feynman path integrals, and truth theorems

(require "spec-aligned-comprehensive-tests.rkt"
         "truth-theorems.rkt"
         "../src/ports/domain-registry.rkt"
         "../src/physics/feynman-path-integral.rkt"
         "../src/logic/guarded-negation.rkt"
         "../src/foundations/abstract-core.rkt"
         "../src/algebra/algebraic-structures.rkt")
(define passed 0)
(define total 0)
(define (inc! b lbl)
  (set! total (add1 total))
  (when b (set! passed (add1 passed)))
  (printf "~a: ~a\n" lbl (if b "ok" "fail")))
(set-guard! (semiring-element (make-abstract-const 1 'integer) L))
(inc! (test-guarded-negation-properties) 'gn-props)
(inc! (test-nand-properties) 'nand)
(inc! (test-computational-universality) 'comp-univ)
(inc! (semiring-element? (gn-and (semiring-element (make-abstract-const 1 'integer) L)
                                 (semiring-element (make-abstract-const 1 'integer) L)))
      'gn-and)
(inc! (semiring-element? (gn-or (semiring-element (make-abstract-const 1 'integer) L)
                                (semiring-element (make-abstract-const 0 'integer) L)))
      'gn-or)
(inc! (semiring-element? (gn-xor (semiring-element (make-abstract-const 1 'integer) L)
                                 (semiring-element (make-abstract-const 0 'integer) L)))
      'gn-xor)
(define ports (list (get-domain-port 'turing)
                    (get-domain-port 'lambda)
                    (get-domain-port 'blockchain)
                    (get-domain-port 'proof-assistant)
                    (get-domain-port 'feynman)))
(for ([s '(1 3 5 7)])
  (define sample (semiring-element (make-abstract-const s 'integer) Core))
  (for ([p ports] #:when p)
    (inc! (let ([defined? (psdm-defined? p sample)]) (or (not defined?) (semiring-element? (domain-port-eval p sample))))
          (format "port(~a,~a)" s (domain-port-name p)))))
(inc! (let* ([t1 (semiring-element (make-abstract-const 1.0 'real) B)]
             [hs (generate-histories t1 1)])
        (list? hs))
      'histories)
(inc! (let ([z (feynman-path-integral (semiring-element (make-abstract-const 1.0 'real) B) '())]) (semiring-element? z)) 'z)
(inc! (let* ([hs (generate-histories (semiring-element (make-abstract-const 1.0 'real) B) 2)]
             [Z (partition-function hs (semiring-element (make-abstract-const 1 'integer) B))])
        (semiring-element? Z))
      'partition)
(inc! (church-turing-equivalence) 'church-turing)
(inc! (eor-health) 'eor)
(inc! (logic-zeta-equivalence) 'logic-zeta)
(inc! (umbral-renormalization) 'umbral)
(inc! (bulk-equals-two-boundaries) 'bulk-eq)
(printf "Lux-Ops check summary: ~a/~a\n" passed total)
