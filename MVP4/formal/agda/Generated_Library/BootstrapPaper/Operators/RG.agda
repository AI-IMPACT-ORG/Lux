module Generated_Library.BootstrapPaper.Operators.RG where

open import Generated_Library.BootstrapPaper.Foundations.M3
open import Data.Nat using (ℕ; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

scaleArity : ℕ → Arity → Arity
scaleArity scale a = record { inputs = inputs a ; outputs = outputs a * scale }

renormalise : ℕ → EdgeKind → Arity
renormalise scale k = scaleArity scale (arityOf k)

scaleArity-identity : (a : Arity) → scaleArity 1 a ≡ a
scaleArity-identity a = refl

renormalise-base-sigma6 : renormalise 1 Sigma6 ≡ arityOf Sigma6
renormalise-base-sigma6 = refl
renormalise-base-tensor : renormalise 1 Tensor ≡ arityOf Tensor
renormalise-base-tensor = refl
renormalise-base-wire : renormalise 1 Wire ≡ arityOf Wire
renormalise-base-wire = refl
