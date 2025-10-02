theory Core
imports Main
begin


(* CLEAN v10 Core - Expanded with Logical Structure *)

datatype Sort =   L : Sort |   B : Sort |   R : Sort |   I : Sort

datatype Operation =   PlusB : Operation |   MultB : Operation |   Plus_L : Operation |   Plus_R : Operation |   Inject_L : Operation |   Inject_R : Operation |   Project_L : Operation |   Project_R : Operation |   Ad0 : Operation |   Ad1 : Operation |   Ad2 : Operation |   Ad3 : Operation |   starB : Operation |   starL : Operation |   starR : Operation

datatype Constant =   ZeroB : Constant |   OneB : Constant |   ZeroL : Constant |   OneL : Constant |   ZeroR : Constant |   OneR : Constant |   Phi : Constant |   BarPhi : Constant |   Z : Constant |   BarZ : Constant |   Lambda : Constant |   Gen4 : Constant

datatype Term =   ConstL : Constant -> Term |   ConstB : Constant -> Term |   ConstR : Constant -> Term |   ConstI : Constant -> Term |   PlusB : Term -> Term -> Term |   MultB : Term -> Term -> Term |   Plus_L : Term -> Term -> Term |   Plus_R : Term -> Term -> Term |   Inject_L : Term -> Term |   Inject_R : Term -> Term |   Project_L : Term -> Term |   Project_R : Term -> Term |   Ad0 : Term -> Term -> Term |   Ad1 : Term -> Term -> Term |   Ad2 : Term -> Term -> Term |   Ad3 : Term -> Term -> Term |   starB : Term -> Term -> Term |   starL : Term -> Term -> Term |   starR : Term -> Term -> Term


definition reflect_L :: "Term ⇒ Term" where "reflect_L = λ t ⇒ t"

definition reflect_R :: "Term ⇒ Term" where "reflect_R = λ t ⇒ t"

definition observer_value :: "Term ⇒ Term" where "observer_value = λ t ⇒ t"
