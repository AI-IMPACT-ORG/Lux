namespace NormalForms


-- CLEAN v10 Normal Forms - Logical Structure

inductive Term : Type where
| ConstB
inductive Header : Type where
| header_zero
| header_add Header Header
| header_multiply Header Header
inductive NormalForm : Type where
| nf_phase Header
| nf_scale Header
| nf_core Term


def normal_form : Term → NormalForm :=
  λ t → NormalForm.nf_core t

def nf_phase : NormalForm → Header :=
  λ nf → nf

def nf_scale : NormalForm → Header :=
  λ nf → nf

def nf_core : NormalForm → Term :=
  λ nf → nf

def normalize_terms : Term → Term → NormalForm :=
  λ t1 t2 → NormalForm.nf_core t1

