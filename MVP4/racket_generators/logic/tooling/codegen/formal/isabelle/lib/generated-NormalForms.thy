theory NormalForms
imports lib.generated-Core
begin


(* CLEAN v10 Normal Forms - Logical Structure *)



definition normal_form :: "Term ⇒ Term" where "normal_form = λ t ⇒ t"

definition nf_phase :: "Term ⇒ Term" where "nf_phase = λ nf ⇒ nf"

definition nf_scale :: "Term ⇒ Term" where "nf_scale = λ nf ⇒ nf"

definition nf_core :: "Term ⇒ Term" where "nf_core = λ nf ⇒ nf"

definition normalize_terms :: "Term ⇒ Term ⇒ Term" where "normalize_terms = λ t1 t2 ⇒ t1"

