theory M3
  imports Main
begin

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

datatype Register =
    InputReg
    OutputReg
    PortReg

datatype EdgeKind =
    Sigma6
    Tensor
    Wire

record Arity =
  inputs  :: nat
  outputs :: nat

definition registers :: "Register list" where
  "registers = [InputReg, OutputReg, PortReg]"

definition edgeKinds :: "EdgeKind list" where
  "edgeKinds = [Sigma6, Tensor, Wire]"

fun arity_of :: "EdgeKind ⇒ Arity" where
  "arity_of Sigma6 = ⦇ inputs = 3, outputs = 3 ⦈"
  "arity_of Tensor = ⦇ inputs = 2, outputs = 2 ⦈"
  "arity_of Wire = ⦇ inputs = 2, outputs = 2 ⦈"

fun src_of :: "EdgeKind ⇒ Register list" where
  "src_of Sigma6 = [PortReg, PortReg, PortReg]"
  "src_of Tensor = [PortReg, PortReg]"
  "src_of Wire = [InputReg, OutputReg]"

fun dst_of :: "EdgeKind ⇒ Register list" where
  "dst_of Sigma6 = [PortReg, PortReg, PortReg]"
  "dst_of Tensor = [PortReg, PortReg]"
  "dst_of Wire = [OutputReg, InputReg]"

record TypeGraph =
  tg_registers :: "Register list"
  tg_edgeKinds :: "EdgeKind list"
  tg_arityMap  :: "EdgeKind ⇒ Arity"
  tg_srcMap    :: "EdgeKind ⇒ Register list"
  tg_dstMap    :: "EdgeKind ⇒ Register list"

definition sample_graph :: TypeGraph where
  "sample_graph = ⦇ tg_registers = registers, tg_edgeKinds = edgeKinds,
     tg_arityMap = arity_of, tg_srcMap = src_of, tg_dstMap = dst_of ⦈"

lemma registers_length : length (tg_registers sample_graph) = 3
  by (simp add: sample_graph_def registers_def)

lemma edges_length : length (tg_edgeKinds sample_graph) = 3
  by (simp add: sample_graph_def edgeKinds_def)

lemma src_length_sigma6 : length (src_of Sigma6) = 3
  by simp

lemma src_length_tensor : length (src_of Tensor) = 2
  by simp

lemma src_length_wire : length (src_of Wire) = 2
  by simp

end
