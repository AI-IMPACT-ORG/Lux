Require Import M3Coq RGCoq TestsCoq.

Record MultiLogicBundle := {
  ml_graph : type_graph;
  ml_registers : length (tg_registers ml_graph) = 3;
  ml_edges : length (tg_edgeKinds ml_graph) = 3;
  ml_sigma6_base : renormalise 1 Sigma6 = arity_of Sigma6;
  ml_sigma6_double : renormalise 2 Sigma6 = {| input_arity := input_arity (arity_of Sigma6); output_arity := output_arity (arity_of Sigma6) * 2 |};
}.

Definition multi_logic_bundle : MultiLogicBundle :=
  {| ml_graph := sample_graph;
     ml_registers := registers_length;
     ml_edges := edges_length;
     ml_sigma6_base := renormalise_base_sigma6;
     ml_sigma6_double := sigma6_renormalise_twice |}.
