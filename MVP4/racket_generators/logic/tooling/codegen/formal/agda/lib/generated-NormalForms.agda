module lib.NormalForms where
open import lib.generated-Core
open import Agda.Builtin.Bool

-- CLEAN v10 Normal Forms - Logical Structure



normal_form : Term → Term
normal_form = λ t → t

nf_phase : Term → Term
nf_phase = λ nf → nf

nf_scale : Term → Term
nf_scale = λ nf → nf

nf_core : Term → Term
nf_core = λ nf → nf

normalize_terms : Term → Term → Term
normalize_terms = λ t1 t2 → t1

