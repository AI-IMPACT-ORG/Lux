theory Bundle
  imports Tests
begin

record MultiLogicBundle =
  ml_graph :: TypeGraph
  ml_registers :: length (tg_registers ml_graph) = 3
  ml_edges :: length (tg_edgeKinds ml_graph) = 3
  ml_sigma6_base :: renormalise 1 Sigma6 = arity_of Sigma6
  ml_sigma6_double :: renormalise 2 Sigma6 = ⦇ inputs = inputs (arity_of Sigma6), outputs = outputs (arity_of Sigma6) * 2 ⦈

definition bundle :: MultiLogicBundle where
  "bundle = ⦇ ml_graph = sample_graph,
     ml_registers = registers_length,
     ml_edges = edges_length,
     ml_sigma6_base = renormalise_base_sigma6,
     ml_sigma6_double = sigma6_renormalise_twice ⦈"

end
