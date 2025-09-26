(* Auto-generated from lt-core host bundle *)
(* μ₁ = 1 *)
(* μ₂ = 2 *)
(* μ₃ = 3 *)
(* μ₄ = 4 *)
(* μ₁★ = 1 *)
(* μ₂★ = 2 *)
(* μ₃★ = 3 *)
(* μ₄★ = 4 *)
(* λ = 1 *)
(* λ★ = 1 *)

From Coq Require Import Arith.PeanoNat.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.

Inductive Register : Type :=
  | InputReg : Register
  | OutputReg : Register
  | PortReg : Register
.

Inductive EdgeKind : Type :=
  | Sigma6 : EdgeKind
  | Tensor : EdgeKind
  | Wire : EdgeKind
.

Record arity := { input_arity : nat; output_arity : nat }.

Definition registers_list : list Register :=
  [InputReg; OutputReg; PortReg].

Definition edgeKinds_list : list EdgeKind :=
  [Sigma6; Tensor; Wire].

Definition arity_of (k : EdgeKind) : arity :=
  match k with
  | Sigma6 => {| input_arity := 3; output_arity := 3 |}
  | Tensor => {| input_arity := 2; output_arity := 2 |}
  | Wire => {| input_arity := 2; output_arity := 2 |}
  end.

Definition src_of (k : EdgeKind) : list Register :=
  match k with
  | Sigma6 => [PortReg; PortReg; PortReg]
  | Tensor => [PortReg; PortReg]
  | Wire => [InputReg; OutputReg]
  end.

Definition dst_of (k : EdgeKind) : list Register :=
  match k with
  | Sigma6 => [PortReg; PortReg; PortReg]
  | Tensor => [PortReg; PortReg]
  | Wire => [OutputReg; InputReg]
  end.

Record type_graph := {
  tg_registers : list Register;
  tg_edgeKinds : list EdgeKind;
  tg_arityMap  : EdgeKind -> arity;
  tg_srcMap    : EdgeKind -> list Register;
  tg_dstMap    : EdgeKind -> list Register
}.

Definition sample_graph : type_graph :=
  {| tg_registers := registers_list;
     tg_edgeKinds := edgeKinds_list;
     tg_arityMap  := arity_of;
     tg_srcMap    := src_of;
     tg_dstMap    := dst_of |}.

Lemma registers_length : length (tg_registers sample_graph) = 3.
Proof. reflexivity. Qed.

Lemma edges_length : length (tg_edgeKinds sample_graph) = 3.
Proof. reflexivity. Qed.

Lemma src_length_sigma6 : length (src_of Sigma6) = 3.
Proof. reflexivity. Qed.

Lemma src_length_tensor : length (src_of Tensor) = 2.
Proof. reflexivity. Qed.

Lemma src_length_wire : length (src_of Wire) = 2.
Proof. reflexivity. Qed.

