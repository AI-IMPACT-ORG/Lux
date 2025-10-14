#lang racket
; (c) 2025 AI.IMPACT GmbH
;; Incompleteness schemata (Gödel 1 & 2) — symbolic witnesses
;; Programs assemble symbolic proof obligations as abstract expressions.

(require (file "../foundations/abstract-core.rkt")
         (file "./internal-coding.rkt")
         (file "./internalize.rkt"))

(provide (all-defined-out))

;; Boolean connectives as abstract expressions
(define (bool-not b) (abstract-op 'not (list b) 'boolean))
(define (bool-and a b) (abstract-op 'and (list a b) 'boolean))
(define (bool-implies a b) (abstract-op 'implies (list a b) 'boolean))

;; Predicate: Provable? (coded sentence) — symbolic
(define (provable? code) (abstract-op 'Prov (list code) 'boolean))

;; Predicate: Consistent — symbolic 0-ary predicate
(define (Consistent?) (abstract-op 'Consistent '() 'boolean))

;; (Optional) Derivability conditions placeholder (Hilbert–Bernays–Löb)
(define (HBL-derivability?) (abstract-op 'HBL '() 'boolean))

;; Diagonal/fixed-point constructor (symbolic)
(define (diagonalize tag)
  ;; Returns a code representing the self-referential sentence for `tag`.
  (encode-term (abstract-op 'diag (list (make-abstract-const (~a tag) 'symbol)) 'code)))

;; Gödel 1 schema: G ↔ ¬Prov(G), from which Consistent ⇒ ¬Prov(G)
(define (godel1-witness)
  (define G (encode-term (abstract-op 'self-not-provable '() 'code)))
  (define axiom-fixed-point (abstract-op 'equiv (list G (bool-not (provable? G))) 'boolean))
  (define claim (bool-implies (Consistent?) (bool-not (provable? G))))
  (hash 'G-code G 'fixed-point axiom-fixed-point 'claim claim))

;; Gödel 2 schema: Consistent ⇒ ¬Prov(Consistent)
(define (godel2-witness)
  (define cons (Consistent?))
  (define claim (bool-implies cons (bool-not (provable? (encode-term cons)))))
  (hash 'claim claim))

;; Internalized L-level proof terms (programs)
(define (godel1-proof)
  (define w (godel1-witness))
  (internalize-boolean (hash-ref w 'claim)))

(define (godel2-proof)
  (define w (godel2-witness))
  (internalize-boolean (hash-ref w 'claim)))
