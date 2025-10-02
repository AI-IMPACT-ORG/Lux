theory Observers
imports lib.generated-Core
begin


(* CLEAN v10 Observers - Expanded with Logical Functions *)

definition project_L :: "Term ⇒ Term" where "project_L = λ t ⇒ t"

definition project_R :: "Term ⇒ Term" where "project_R = λ t ⇒ t"

definition reconstitute :: "Term ⇒ Term" where "reconstitute = λ t ⇒ t"

definition residual :: "Term ⇒ Term" where "residual = λ t ⇒ t"

definition triality_sum :: "Term ⇒ Term ⇒ Term ⇒ Term" where "triality_sum = λ l b r ⇒ l"
