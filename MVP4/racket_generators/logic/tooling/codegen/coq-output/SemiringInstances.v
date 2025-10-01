Require Import CoreTypes.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

(* Semiring Instances using Coq Type Classes - Much More Economical *)

(* Type class for commutative idempotent semirings *)
Class CommIdempotentSemiring (A : Type) := {
  plus : A -> A -> A;
  mult : A -> A -> A;
  zero : A;
  one : A;
  
  (* Axioms *)
  plus_comm : forall x y, plus x y = plus y x;
  plus_assoc : forall x y z, plus (plus x y) z = plus x (plus y z);
  plus_idempotent : forall x, plus x x = x;
  plus_zero : forall x, plus zero x = x;
  
  mult_comm : forall x y, mult x y = mult y x;
  mult_assoc : forall x y z, mult (mult x y) z = mult x (mult y z);
  mult_idempotent : forall x, mult x x = x;
  mult_one : forall x, mult one x = x;
  mult_distrib : forall x y z, mult x (plus y z) = plus (mult x y) (mult x z);
  mult_absorption : forall x y, mult x (plus x y) = x
}.

(* Type class for commutative semirings *)
Class CommSemiring (A : Type) := {
  plus_sr : A -> A -> A;
  mult_sr : A -> A -> A;
  zero_sr : A;
  one_sr : A;
  
  (* Axioms *)
  plus_sr_comm : forall x y, plus_sr x y = plus_sr y x;
  plus_sr_assoc : forall x y z, plus_sr (plus_sr x y) z = plus_sr x (plus_sr y z);
  plus_sr_zero : forall x, plus_sr zero_sr x = x;
  plus_sr_annihilating : forall x, plus_sr x zero_sr = x;
  
  mult_sr_comm : forall x y, mult_sr x y = mult_sr y x;
  mult_sr_assoc : forall x y z, mult_sr (mult_sr x y) z = mult_sr x (mult_sr y z);
  mult_sr_one : forall x, mult_sr one_sr x = x;
  mult_sr_distrib : forall x y z, mult_sr x (plus_sr y z) = plus_sr (mult_sr x y) (mult_sr x z)
}.

(* Instances for Left boundary *)
Instance LeftSemiring : CommIdempotentSemiring (Term Left) := {
  plus := fun x y => Op PlusL (Pair x y);
  mult := fun x y => Op MultL (Pair x y);
  zero := Const ZeroL;
  one := Const OneL;
  
  plus_comm := plusL_comm;
  plus_assoc := plusL_assoc;
  plus_idempotent := plusL_idempotent;
  plus_zero := plusL_zero;
  
  mult_comm := multL_comm;
  mult_assoc := multL_assoc;
  mult_idempotent := multL_idempotent;
  mult_one := multL_one;
  mult_distrib := multL_distrib;
  mult_absorption := multL_absorption
}.

(* Instances for Right boundary *)
Instance RightSemiring : CommIdempotentSemiring (Term Right) := {
  plus := fun x y => Op PlusR (Pair x y);
  mult := fun x y => Op MultR (Pair x y);
  zero := Const ZeroR;
  one := Const OneR;
  
  plus_comm := plusR_comm;
  plus_assoc := plusR_assoc;
  plus_idempotent := plusR_idempotent;
  plus_zero := plusR_zero;
  
  mult_comm := multR_comm;
  mult_assoc := multR_assoc;
  mult_idempotent := multR_idempotent;
  mult_one := multR_one;
  mult_distrib := multR_distrib;
  mult_absorption := multR_absorption
}.

(* Instance for Bulk *)
Instance BulkSemiring : CommSemiring (Term Bulk) := {
  plus_sr := fun x y => Op PlusB (Pair x y);
  mult_sr := fun x y => Op MultB (Pair x y);
  zero_sr := Const ZeroB;
  one_sr := Const OneB;
  
  plus_sr_comm := plusB_comm;
  plus_sr_assoc := plusB_assoc;
  plus_sr_zero := plusB_zero;
  plus_sr_annihilating := plusB_annihilating;
  
  mult_sr_comm := multB_comm;
  mult_sr_assoc := multB_assoc;
  mult_sr_one := multB_one;
  mult_sr_distrib := multB_distrib
}.

(* This gives us automatic proof automation for semiring properties! *)
