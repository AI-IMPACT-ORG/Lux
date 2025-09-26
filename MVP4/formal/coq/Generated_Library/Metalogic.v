Require Import M3Coq RGCoq.

Record MetalogicBundle := {
  ml_noether : renormalise 1 Sigma6 = arity_of Sigma6;
  ml_ward : renormalise 2 Sigma6 = {| input_arity := input_arity (arity_of Sigma6); output_arity := output_arity (arity_of Sigma6) * 2 |};
  ml_gamma_gamma : scale_arity 1 (arity_of Sigma6) = arity_of Sigma6;
  ml_renormalisable : renormalise 2 Sigma6 = scale_arity 2 (arity_of Sigma6);
  ml_rice : renormalise 1 Sigma6 = renormalise 1 Sigma6
}.

Definition metalogic_bundle : MetalogicBundle :=
  {| ml_noether := renormalise_base_sigma6;
     ml_ward := sigma6_renormalise_twice;
     ml_gamma_gamma := scale_arity_identity (arity_of Sigma6);
     ml_renormalisable := eq_refl;
     ml_rice := eq_refl |}.
