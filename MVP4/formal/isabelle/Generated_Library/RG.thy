theory RG
  imports M3
begin

definition scale_arity :: "nat ⇒ Arity ⇒ Arity" where
  "scale_arity s a = ⦇ inputs = inputs a, outputs = outputs a * s ⦈"

definition renormalise :: "nat ⇒ EdgeKind ⇒ Arity" where
  "renormalise s k = scale_arity s (arity_of k)"

lemma scale_arity_identity : scale_arity 1 a = a
  by (cases a) (simp add: scale_arity_def)

lemma renormalise_base_sigma6 : renormalise 1 Sigma6 = arity_of Sigma6
  by (simp add: renormalise_def scale_arity_def)

lemma renormalise_base_tensor : renormalise 1 Tensor = arity_of Tensor
  by (simp add: renormalise_def scale_arity_def)

lemma renormalise_base_wire : renormalise 1 Wire = arity_of Wire
  by (simp add: renormalise_def scale_arity_def)

end
