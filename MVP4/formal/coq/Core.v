Require Import Arith.Arith.
Require Import Arith.PeanoNat.


(* CLEAN v10 Core - Expanded with Logical Structure *)

Inductive Sort : Type :=
|   L : Sort
|   B : Sort
|   R : Sort
|   I : Sort.

Inductive Operation : Type :=
|   PlusB : Operation
|   MultB : Operation
|   Plus_L : Operation
|   Plus_R : Operation
|   Inject_L : Operation
|   Inject_R : Operation
|   Project_L : Operation
|   Project_R : Operation
|   Ad0 : Operation
|   Ad1 : Operation
|   Ad2 : Operation
|   Ad3 : Operation
|   starB : Operation
|   starL : Operation
|   starR : Operation.

Inductive Constant : Type :=
|   ZeroB : Constant
|   OneB : Constant
|   ZeroL : Constant
|   OneL : Constant
|   ZeroR : Constant
|   OneR : Constant
|   Phi : Constant
|   BarPhi : Constant
|   Z : Constant
|   BarZ : Constant
|   Lambda : Constant
|   Gen4 : Constant.

Inductive Term : Type :=
|   ConstL : Constant -> Term
|   ConstB : Constant -> Term
|   ConstR : Constant -> Term
|   ConstI : Constant -> Term
|   TermPlusB : Term -> Term -> Term
|   TermMultB : Term -> Term -> Term
|   TermPlus_L : Term -> Term -> Term
|   TermPlus_R : Term -> Term -> Term
|   TermInject_L : Term -> Term
|   TermInject_R : Term -> Term
|   TermProject_L : Term -> Term
|   TermProject_R : Term -> Term
|   TermAd0 : Term -> Term -> Term
|   TermAd1 : Term -> Term -> Term
|   TermAd2 : Term -> Term -> Term
|   TermAd3 : Term -> Term -> Term
|   TermstarB : Term -> Term -> Term
|   TermstarL : Term -> Term -> Term
|   TermstarR : Term -> Term -> Term.

Inductive Kernel : Type :=
|   KernelId : Kernel.

Inductive Header : Type :=
|   header_zero : Header
|   header_add : Header -> Header -> Header
|   header_multiply : Header -> Header -> Header.

Inductive NormalForm : Type :=
|   nf_phase : NormalForm
|   nf_scale : NormalForm
|   nf_core : NormalForm.

Axiom plusB_comm : forall x y : Term, TermPlusB x y = TermPlusB y x.
Axiom multB_comm : forall x y : Term, TermMultB x y = TermMultB y x.
Axiom bulk_equals_boundaries : forall t : Term, exists l r : Term, t = TermPlusB l r.
Axiom observer_invisibility : forall t : Term, TermProject_L t = TermProject_R t -> t = TermInject_L (TermProject_L t).
