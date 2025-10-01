Require Import Arith.Arith.
Require Import Arith.PeanoNat.
Require Import Logic.FunctionalExtensionality.
Require Import ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.

(* ============================================================================ *)
(* CLEAN v10 Core Types - Elegant Architecture with Dependent Types           *)
(* ============================================================================ *)

(* ---------------------------------------------------------------------------- *)
(* Sorts: The fundamental types of the CLEAN framework                          *)
(* ---------------------------------------------------------------------------- *)
Inductive Sort :=
| Left : Sort
| Bulk : Sort  
| Right : Sort
| Unit : Sort.

(* ---------------------------------------------------------------------------- *)
(* Constants: Type-safe constants for each sort                                 *)
(* ---------------------------------------------------------------------------- *)
Inductive Constant : Sort -> Type :=
| ZeroL : Constant Left
| OneL : Constant Left
| ZeroR : Constant Right
| OneR : Constant Right
| ZeroB : Constant Bulk
| OneB : Constant Bulk
| Phi : Constant Bulk
| BarPhi : Constant Bulk
| ZScalar : Constant Bulk
| BarZ : Constant Bulk
| Lambda : Constant Bulk.

(* ---------------------------------------------------------------------------- *)
(* Terms: The main syntactic objects with dependent types                      *)
(* ---------------------------------------------------------------------------- *)
Inductive Term : Sort -> Type :=
| Const : forall s, Constant s -> Term s
| PlusL : Term Left -> Term Left -> Term Left
| MultL : Term Left -> Term Left -> Term Left
| PlusR : Term Right -> Term Right -> Term Right
| MultR : Term Right -> Term Right -> Term Right
| PlusB : Term Bulk -> Term Bulk -> Term Bulk
| MultB : Term Bulk -> Term Bulk -> Term Bulk
| InjectL : Term Left -> Term Bulk
| InjectR : Term Right -> Term Bulk
| ProjectL : Term Bulk -> Term Left
| ProjectR : Term Bulk -> Term Right.

(* ---------------------------------------------------------------------------- *)
(* Headers: Metadata for terms with phase and scale information                *)
(* ---------------------------------------------------------------------------- *)
Record Header : Type :=
  mkHeader {
    phase : Z;
    scale : nat
  }.

(* ---------------------------------------------------------------------------- *)
(* Kernels: Transition functions with headers                                   *)
(* ---------------------------------------------------------------------------- *)
Record Kernel : Type :=
  mkKernel {
    kernel_header : Header;
    kernel_transition : Term Bulk -> Term Bulk
  }.

(* ---------------------------------------------------------------------------- *)
(* Type Classes: Elegant abstraction for semiring properties                   *)
(* ---------------------------------------------------------------------------- *)

(* Commutative Idempotent Semiring *)
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

(* Commutative Semiring *)
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

(* ---------------------------------------------------------------------------- *)
(* Axioms: The foundational properties of CLEAN v10                             *)
(* ---------------------------------------------------------------------------- *)

(* Semiring axioms for Left boundary *)
Axiom plusL_comm : forall x y : Term Left, PlusL x y = PlusL y x.
Axiom plusL_assoc : forall x y z : Term Left, 
  PlusL (PlusL x y) z = PlusL x (PlusL y z).
Axiom plusL_idempotent : forall x : Term Left, PlusL x x = x.
Axiom plusL_zero : forall x : Term Left, PlusL (Const Left ZeroL) x = x.

Axiom multL_comm : forall x y : Term Left, MultL x y = MultL y x.
Axiom multL_assoc : forall x y z : Term Left,
  MultL (MultL x y) z = MultL x (MultL y z).
Axiom multL_idempotent : forall x : Term Left, MultL x x = x.
Axiom multL_one : forall x : Term Left, MultL (Const Left OneL) x = x.
Axiom multL_distrib : forall x y z : Term Left,
  MultL x (PlusL y z) = PlusL (MultL x y) (MultL x z).
Axiom multL_absorption : forall x y : Term Left,
  MultL x (PlusL x y) = x.

(* Semiring axioms for Right boundary - identical structure *)
Axiom plusR_comm : forall x y : Term Right, PlusR x y = PlusR y x.
Axiom plusR_assoc : forall x y z : Term Right, 
  PlusR (PlusR x y) z = PlusR x (PlusR y z).
Axiom plusR_idempotent : forall x : Term Right, PlusR x x = x.
Axiom plusR_zero : forall x : Term Right, PlusR (Const Right ZeroR) x = x.

Axiom multR_comm : forall x y : Term Right, MultR x y = MultR y x.
Axiom multR_assoc : forall x y z : Term Right,
  MultR (MultR x y) z = MultR x (MultR y z).
Axiom multR_idempotent : forall x : Term Right, MultR x x = x.
Axiom multR_one : forall x : Term Right, MultR (Const Right OneR) x = x.
Axiom multR_distrib : forall x y z : Term Right,
  MultR x (PlusR y z) = PlusR (MultR x y) (MultR x z).
Axiom multR_absorption : forall x y : Term Right,
  MultR x (PlusR x y) = x.

(* Bulk semiring axioms *)
Axiom plusB_comm : forall x y : Term Bulk, PlusB x y = PlusB y x.
Axiom plusB_assoc : forall x y z : Term Bulk, 
  PlusB (PlusB x y) z = PlusB x (PlusB y z).
Axiom plusB_zero : forall x : Term Bulk, PlusB (Const Bulk ZeroB) x = x.
Axiom plusB_annihilating : forall x : Term Bulk, PlusB x (Const Bulk ZeroB) = x.

Axiom multB_comm : forall x y : Term Bulk, MultB x y = MultB y x.
Axiom multB_assoc : forall x y z : Term Bulk,
  MultB (MultB x y) z = MultB x (MultB y z).
Axiom multB_one : forall x : Term Bulk, MultB (Const Bulk OneB) x = x.
Axiom multB_distrib : forall x y z : Term Bulk,
  MultB x (PlusB y z) = PlusB (MultB x y) (MultB x z).

(* Observer axioms - retraction property *)
Axiom observer_retraction_L : forall x : Term Left, 
  ProjectL (InjectL x) = x.
Axiom observer_retraction_R : forall x : Term Right, 
  ProjectR (InjectR x) = x.

(* Limited Omniscience Axiom - the key axiom *)
Axiom residual_invisibility : forall t : Term Bulk,
  let rho := PlusB (InjectL (ProjectL t)) (InjectR (ProjectR t)) in
  let residual := PlusB t rho in
  ProjectL residual = Const Left ZeroL /\ ProjectR residual = Const Right ZeroR.

(* Basepoint axiom *)
Axiom basepoint_normalization : 
  MultB (Const Bulk Phi) (Const Bulk BarPhi) = Const Bulk OneB.

(* ---------------------------------------------------------------------------- *)
(* Instances: Automatic type class resolution                                  *)
(* ---------------------------------------------------------------------------- *)

Instance LeftSemiring : CommIdempotentSemiring (Term Left) := {
  plus := PlusL;
  mult := MultL;
  zero := Const Left ZeroL;
  one := Const Left OneL;
  
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

Instance RightSemiring : CommIdempotentSemiring (Term Right) := {
  plus := PlusR;
  mult := MultR;
  zero := Const Right ZeroR;
  one := Const Right OneR;
  
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

Instance BulkSemiring : CommSemiring (Term Bulk) := {
  plus_sr := PlusB;
  mult_sr := MultB;
  zero_sr := Const Bulk ZeroB;
  one_sr := Const Bulk OneB;
  
  plus_sr_comm := plusB_comm;
  plus_sr_assoc := plusB_assoc;
  plus_sr_zero := plusB_zero;
  plus_sr_annihilating := plusB_annihilating;
  
  mult_sr_comm := multB_comm;
  mult_sr_assoc := multB_assoc;
  mult_sr_one := multB_one;
  mult_sr_distrib := multB_distrib
}.

(* ---------------------------------------------------------------------------- *)
(* Proof Automation: Elegant tactics for CLEAN properties                      *)
(* ---------------------------------------------------------------------------- *)

Ltac clean_semiring :=
  repeat (rewrite plusB_comm || rewrite multB_comm || 
          rewrite plusL_comm || rewrite multL_comm ||
          rewrite plusR_comm || rewrite multR_comm);
  repeat (rewrite plusB_assoc || rewrite multB_assoc ||
          rewrite plusL_assoc || rewrite multL_assoc ||
          rewrite plusR_assoc || rewrite multR_assoc);
  repeat (rewrite plusB_zero || rewrite multB_one ||
          rewrite plusL_zero || rewrite multL_one ||
          rewrite plusR_zero || rewrite multR_one).

Ltac clean_observers :=
  repeat (rewrite observer_retraction_L || rewrite observer_retraction_R);
  clean_semiring.

Ltac clean_residual :=
  apply residual_invisibility;
  clean_observers.

Ltac clean_auto :=
  try clean_semiring;
  try clean_observers;
  try clean_residual;
  auto.

(* ---------------------------------------------------------------------------- *)
(* Export: Clean interface for downstream modules                             *)
(* ---------------------------------------------------------------------------- *)

Export Sort.
Export Constant.
Export Term.
Export Header.
Export Kernel.
Export CommIdempotentSemiring.
Export CommSemiring.
Export LeftSemiring.
Export RightSemiring.
Export BulkSemiring.

(* This completes the elegant CoreTypes module! *)
