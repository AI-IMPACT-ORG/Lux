module lib.Core where
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Equality

-- CLEAN v10 Core - Expanded with Logical Structure

data Sort : Set where
  L : Sort
  B : Sort
  R : Sort
  I : Sort

data Operation : Set where
  PlusB : Operation
  MultB : Operation
  Plus_L : Operation
  Plus_R : Operation
  Inject_L : Operation
  Inject_R : Operation
  Project_L : Operation
  Project_R : Operation
  Ad0 : Operation
  Ad1 : Operation
  Ad2 : Operation
  Ad3 : Operation
  starB : Operation
  starL : Operation
  starR : Operation

data Constant : Set where
  ZeroB : Constant
  OneB : Constant
  ZeroL : Constant
  OneL : Constant
  ZeroR : Constant
  OneR : Constant
  Phi : Constant
  BarPhi : Constant
  Z : Constant
  BarZ : Constant
  Lambda : Constant
  Gen4 : Constant

data Term : Set where
  ConstL : Constant -> Term
  ConstB : Constant -> Term
  ConstR : Constant -> Term
  ConstI : Constant -> Term
  PlusB : Term -> Term -> Term
  MultB : Term -> Term -> Term
  Plus_L : Term -> Term -> Term
  Plus_R : Term -> Term -> Term
  Inject_L : Term -> Term
  Inject_R : Term -> Term
  Project_L : Term -> Term
  Project_R : Term -> Term
  Ad0 : Term -> Term -> Term
  Ad1 : Term -> Term -> Term
  Ad2 : Term -> Term -> Term
  Ad3 : Term -> Term -> Term
  starB : Term -> Term -> Term
  starL : Term -> Term -> Term
  starR : Term -> Term -> Term


reflect_L : Term → Term
reflect_L = λ t → t

reflect_R : Term → Term
reflect_R = λ t → t

observer_value : Term → Term
observer_value = λ t → t
