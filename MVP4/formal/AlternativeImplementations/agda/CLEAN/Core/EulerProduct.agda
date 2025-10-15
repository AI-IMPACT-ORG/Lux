module CLEAN.Core.EulerProduct where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import CLEAN.Core.Dirichlet
open import CLEAN.Core.NormalForm

-- Regulated Dirichlet sum built from a base normal form and regulator parameter.

dirichletSum : NormalForm ⊤ → Regulator → DirichletSeries
dirichletSum nf r = mkSeries nf (λ _ → (nf , Regulator.lambda r))

-- Regulated Euler product using delta-flow as the multiplicative generator.

eulerProduct : NormalForm ⊤ → Regulator → DirichletSeries
eulerProduct nf r = mkSeries nf (λ _ → (DeltaNF nf , Regulator.lambda r))
