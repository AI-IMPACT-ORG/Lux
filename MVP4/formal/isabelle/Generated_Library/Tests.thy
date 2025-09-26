theory Tests
  imports M3 RG
begin

lemma src_pattern_sigma6 : src_of Sigma6 = [PortReg, PortReg, PortReg]
  by simp

lemma src_pattern_tensor : src_of Tensor = [PortReg, PortReg]
  by simp

lemma src_pattern_wire : src_of Wire = [InputReg, OutputReg]
  by simp

lemma sigma6_renormalise_twice : renormalise 2 Sigma6 = ⦇ inputs = inputs (arity_of Sigma6), outputs = outputs (arity_of Sigma6) * 2 ⦈
  by (simp add: renormalise_def scale_arity_def)

end
