module Generated_Library.BootstrapPaper.Tests.Core where

open import Generated_Library.BootstrapPaper.Foundations.M3
open import Generated_Library.BootstrapPaper.Operators.RG
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

src-pattern-sigma6 : srcOf Sigma6 ≡ PortReg ∷ PortReg ∷ PortReg ∷ []
src-pattern-sigma6 = refl
src-pattern-tensor : srcOf Tensor ≡ PortReg ∷ PortReg ∷ []
src-pattern-tensor = refl
src-pattern-wire : srcOf Wire ≡ InputReg ∷ OutputReg ∷ []
src-pattern-wire = refl

sigma6-renormalise-twice : renormalise 2 Sigma6 ≡ record { inputs = inputs (arityOf Sigma6) ; outputs = outputs (arityOf Sigma6) * 2 }
sigma6-renormalise-twice = refl
