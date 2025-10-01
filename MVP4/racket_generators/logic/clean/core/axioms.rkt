#lang racket

(provide core-axioms)

(define core-axioms
  '("⊕_L forms a commutative idempotent monoid"
    "⊕_R forms a commutative idempotent monoid"
    "⊕B forms a commutative monoid with annihilating 0_B"
    "⊗B distributes over ⊕B and has unit 1_B"
    "Observers ν_* retract ι_*"
    "Basepoint Gen4(a0,a1,a2,a3) = 0_B"
    "Braids ad_i commute up to central F_{ij}"
    "Triality conjugations are typed anti-involutions"
    "Residual bulk is invisible to observers"))
