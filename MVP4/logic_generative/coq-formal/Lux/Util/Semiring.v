(* (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. *)

From Coq Require Import Setoids.Setoid.
From Coq Require Import Morphisms.

Module Type CommutativeSemiring.
  Parameter carrier : Type.
  Parameter zero one : carrier.
  Parameter add mul : carrier -> carrier -> carrier.

  Infix "+" := add.
  Infix "*" := mul.

  Axiom add_assoc : forall x y z, x + (y + z) = (x + y) + z.
  Axiom add_comm  : forall x y, x + y = y + x.
  Axiom add_zero_l : forall x, zero + x = x.

  Axiom mul_assoc : forall x y z, x * (y * z) = (x * y) * z.
  Axiom mul_comm  : forall x y, x * y = y * x.
  Axiom mul_one_l : forall x, one * x = x.

  Axiom mul_distr_l : forall x y z, x * (y + z) = (x * y) + (x * z).
  Axiom mul_zero_l : forall x, zero * x = zero.
End CommutativeSemiring.

Module SemiringNotations (S:CommutativeSemiring).
  Infix "+" := S.add.
  Infix "*" := S.mul.
  Notation "0" := S.zero.
  Notation "1" := S.one.
End SemiringNotations.

