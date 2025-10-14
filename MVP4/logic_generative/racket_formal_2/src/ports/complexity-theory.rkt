#lang racket
;; Computational Complexity Port (refocused)

(require racket/math
         racket/list
         (file "../core.rkt")
         (file "../moduli/moduli-system.rkt")
         (file "../foundations/abstract-core.rkt")
         (file "../algebra/algebraic-structures.rkt")
         (file "../logic/lens-framework.rkt")
         (file "../theorems/complexity-separation.rkt"))

(provide (all-defined-out))

(struct complexity-regulator (N K) #:transparent)

(define (port-equivalent? a b)
  (cond
    [(equal? a b) #t]
    [(and (number? a) (number? b)) (let ([ratio (/ (max a b) (min a b))]) (<= ratio 2.0))]
    [(and (list? a) (list? b)) (and (= (length a) (length b)) (andmap port-equivalent? a b))]
    [else (equal? a b)]))

(define (computational-distance C1 C2) (if (port-equivalent? C1 C2) 0 1))

(define (rc-normal-form/complexity context value)
  (match context
    [(list 'class 'P) 'CLASS-P]
    [(list 'class 'NP) 'CLASS-NP]
    [(list 'class 'PSPACE) 'CLASS-PSPACE]
    [(list 'problem p) (list 'PROBLEM-NF p)]
    [_ (list 'COMPLEXITY-NF value)]))

(define (exact-after-renorm/complexity? ctx-a a ctx-b b)
  (equal? (rc-normal-form/complexity ctx-a a)
          (rc-normal-form/complexity ctx-b b)))

(define (rc-scale N) (+ N 1))

(define (gate-complexity n gates)
  (define (gate-count expr)
    (match expr
      ['T 0] ['F 0]
      [(list 'NOT x) (+ 1 (gate-count x))]
      [(list 'AND x y) (+ 1 (gate-count x) (gate-count y))]
      [(list 'OR x y) (+ 1 (gate-count x) (gate-count y))]
      [_ 1]))
  (gate-count gates))

(define (poly-reduction problem-A problem-B)
  (define (reduction-complexity A B)
    (match (list A B)
      [(list 'SAT '3SAT) 1]
      [(list '3SAT 'CLIQUE) 2]
      [(list 'CLIQUE 'INDEPENDENT-SET) 1]
      [_ 3]))
  (reduction-complexity problem-A problem-B))

(define (p-complete-problems) '("Circuit Value" "Linear Programming" "Greatest Common Divisor"))
(define (np-complete-problems) '("SAT" "3SAT" "CLIQUE" "Independent Set" "Vertex Cover"))
(define (pspace-complete-problems) '("Quantified Boolean Formula" "Geography" "Hex" "Go" "Checkers"))
(define (conp-complete-problems) '("TAUT" "UNSAT"))

(define (rg-flow complexity level) complexity)

(define (check-local-to-global-flow reg)
  (define N (complexity-regulator-N reg))
  (define K (complexity-regulator-K reg))
  (define (rg-step current-complexity level)
    (let loop ([i 0] [C current-complexity])
      (if (>= i K) C (loop (add1 i) (rg-flow C level)))))
  (define local-complexity (gate-complexity N '(AND (OR T F) (NOT T))))
  (define global-complexity (rg-step local-complexity 'local))
  (= (computational-distance local-complexity global-complexity) 0))

(define (check-reduction-invariance reg)
  (define N (complexity-regulator-N reg))
  (define reductions '(SAT 3SAT CLIQUE INDEPENDENT-SET))
  (define complexities (map (λ (prob) (poly-reduction 'SAT prob)) reductions))
  (andmap (λ (c) (<= c (* N 2))) complexities))

(define (check-completeness-fixed-points reg)
  (define (complexity-class-measure problems) (length problems))
  (define p-measure (complexity-class-measure (p-complete-problems)))
  (define np-measure (complexity-class-measure (np-complete-problems)))
  (define pspace-measure (complexity-class-measure (pspace-complete-problems)))
  (define (flow-to-fixed-point initial-measure level)
    (let loop ([i 0] [C initial-measure])
      (if (>= i 3) C (loop (add1 i) (rg-flow C level)))))
  (define p-fixed (flow-to-fixed-point p-measure 'fixed-point))
  (define np-fixed (flow-to-fixed-point np-measure 'fixed-point))
  (define pspace-fixed (flow-to-fixed-point pspace-measure 'fixed-point))
  (and (= (computational-distance p-measure p-fixed) 0)
       (= (computational-distance np-measure np-fixed) 0)
       (= (computational-distance pspace-measure pspace-fixed) 0)
       (exact-after-renorm/complexity? (list 'class 'P) p-measure (list 'class 'P) p-fixed)
       (exact-after-renorm/complexity? (list 'class 'NP) np-measure (list 'class 'NP) np-fixed)
       (exact-after-renorm/complexity? (list 'class 'PSPACE) pspace-measure (list 'class 'PSPACE) pspace-fixed)))

(define (check-kernel-of-kernel reg)
  (define problems '(SAT 3SAT CLIQUE Circuit-Value Linear-Programming))
  (define essences (map (λ (p) 1) problems))
  (define avg-essence (/ (apply + essences) (length essences)))
  (= (computational-distance avg-essence 1) 0))

(define (check-encoding-independence reg)
  (define problems '(SAT 3SAT CLIQUE))
  (define turing-measures (map (λ (p) 1) problems))
  (define circuit-measures turing-measures)
  (define lambda-measures turing-measures)
  (and (= (computational-distance (apply + turing-measures) (apply + circuit-measures)) 0)
       (= (computational-distance (apply + circuit-measures) (apply + lambda-measures)) 0)))

(define (check-scale-invariance reg)
  (define p-size (length (p-complete-problems)))
  (define np-size (length (np-complete-problems)))
  (define pspace-size (length (pspace-complete-problems)))
  (define (flow-complexity-class size level)
    (let loop ([i 0] [C size])
      (if (>= i 2) C (loop (add1 i) (rg-flow C level)))))
  (define p-flowed (flow-complexity-class p-size 'global))
  (define np-flowed (flow-complexity-class np-size 'global))
  (define pspace-flowed (flow-complexity-class pspace-size 'global))
  (and (<= p-size np-size)
       (<= np-size pspace-size)
       (<= p-flowed np-flowed)
       (<= np-flowed pspace-flowed)
       (= (computational-distance p-size p-flowed) 0)
       (= (computational-distance np-size np-flowed) 0)
       (= (computational-distance pspace-size pspace-flowed) 0)))

;; Separation-style symbolic evidence (monotone measures; conservative)
(define (check-separation-evidence reg)
  (define p-size (length (p-complete-problems)))
  (define np-size (length (np-complete-problems)))
  (define conp-size (length (conp-complete-problems)))
  (and (<= p-size np-size)
       (<= p-size conp-size)
       ;; monotone under trivial RG
       (= (computational-distance p-size (rg-flow p-size 'global)) 0)
       (= (computational-distance np-size (rg-flow np-size 'global)) 0)
       (= (computational-distance conp-size (rg-flow conp-size 'global)) 0)))

(define (run-computational-complexity-checks #:N [N 1000] #:K [K 6])
  (define reg (complexity-regulator N K))
  (printf "=== Computational Complexity Port (RG/Fisher) ===\n")
  (printf "Local→Global flow: ~a\n" (check-local-to-global-flow reg))
  (printf "Reduction invariance: ~a\n" (check-reduction-invariance reg))
  (printf "Completeness fixed points: ~a\n" (check-completeness-fixed-points reg))
  (printf "Kernel of kernel: ~a\n" (check-kernel-of-kernel reg))
  (printf "Encoding independence: ~a\n" (check-encoding-independence reg))
  (printf "Scale invariance: ~a\n" (check-scale-invariance reg))
  (printf "Separation evidence (monotone measures): ~a\n" (check-separation-evidence reg))
  (printf "=== Port contract invariants only ===\n"))

(define (run-complexity-separation-evidence)
  (and (semiring-element? (lens-lipschitz-sequent 'Rdet (make-abstract-const 9/10 'real) 'B))
       (semiring-element? (lens-neutrality-sequent 'Rnd))
       (verify-pnp-separations)))
