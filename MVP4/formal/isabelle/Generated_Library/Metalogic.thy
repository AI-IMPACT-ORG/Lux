theory Metalogic
  imports RG
begin

record MetalogicBundle =
  ml_noether :: renormalise 1 Sigma6 = arity_of Sigma6
  ml_ward :: renormalise 2 Sigma6 = ⦇ inputs = inputs (arity_of Sigma6), outputs = outputs (arity_of Sigma6) * 2 ⦈
  ml_gamma_gamma :: scale_arity 1 (arity_of Sigma6) = arity_of Sigma6
  ml_renormalisable :: renormalise 2 Sigma6 = scale_arity 2 (arity_of Sigma6)
  ml_rice :: renormalise 1 Sigma6 = renormalise 1 Sigma6

definition metalogic_bundle :: MetalogicBundle where
  "metalogic_bundle = ⦇ ml_noether = renormalise_base_sigma6,
     ml_ward = sigma6_renormalise_twice,
     ml_gamma_gamma = scale_arity_identity (arity_of Sigma6),
     ml_renormalisable = refl,
     ml_rice = refl ⦈"

end
