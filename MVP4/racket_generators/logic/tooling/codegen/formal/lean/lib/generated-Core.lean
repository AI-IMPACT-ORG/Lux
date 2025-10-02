namespace Core


-- CLEAN v10 Core - Expanded with Logical Structure

inductive CleanSort : Type where
| L
| B
| R
| I

inductive Operation : Type where
| PlusB
| MultB
| Plus_L
| Plus_R
| Inject_L
| Inject_R
| Project_L
| Project_R
| Ad0
| Ad1
| Ad2
| Ad3
| starB
| starL
| starR

inductive Constant : Type where
| ZeroB
| OneB
| ZeroL
| OneL
| ZeroR
| OneR
| Phi
| BarPhi
| Z
| BarZ
| Lambda
| Gen4

inductive Term : Type where
| ConstL
| ConstB
| ConstR
| ConstI
| TermPlusB : Term → Term → Term
| TermMultB : Term → Term → Term
| TermPlus_L : Term → Term → Term
| TermPlus_R : Term → Term → Term
| TermInject_L : Term → Term
| TermInject_R : Term → Term
| TermProject_L : Term → Term
| TermProject_R : Term → Term
| TermAd0 : Term → Term → Term
| TermAd1 : Term → Term → Term
| TermAd2 : Term → Term → Term
| TermAd3 : Term → Term → Term
| TermstarB : Term → Term → Term
| TermstarL : Term → Term → Term
| TermstarR : Term → Term → Term

inductive Header : Type where
| header_zero
| header_add Header Header
| header_multiply Header Header
inductive NormalForm : Type where
| nf_phase Header
| nf_scale Header
| nf_core Term

def reflect_L : Term → Term :=
  λ t → t

def reflect_R : Term → Term :=
  λ t → t

def observer_value : Term → Term :=
  λ t → t
