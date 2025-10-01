module CLEAN.Core.Dirichlet where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import CLEAN.Core.NormalForm
open import CLEAN.Core.System using (deltaBulkSum; deltaCumulantCommute)

-- Lightweight regulator parameter and weight definition.

record Regulator : Set where
  constructor mkRegulator
  field
    lambda : Nat

Weight : Set → Set
Weight A = Σ A (λ _ → Nat)

-- Dirichlet series element over normal forms with a regulator weight.

record DirichletSeries : Set where
  constructor mkSeries
  field
    baseNF : NormalForm ⊤
    weight : Regulator → Weight (NormalForm ⊤)

open DirichletSeries public

-- Evaluation at a specific regulator (drops the weight component).
evaluateSeries : DirichletSeries → Regulator → NormalForm ⊤
evaluateSeries (mkSeries nf w) r = let (x , _) = w r in x

-- Pointwise sum and Dirichlet-convolution inspired product (toy versions).

_⊕ₛ_ : DirichletSeries → DirichletSeries → DirichletSeries
mkSeries nf w ⊕ₛ mkSeries nf' w' =
  mkSeries nf (λ r → let (a , α) = w r; (b , β) = w' r in (parametrise idPhaseFlow idPhaseFlow idScaleFlow idScaleFlow a , α + β))

_⊗ₛ_ : DirichletSeries → DirichletSeries → DirichletSeries
mkSeries nf w ⊗ₛ mkSeries nf' w' =
  mkSeries nf (λ r → let (a , α) = w r; (b , β) = w' r in (DeltaNF a , α + β))

-- Basic lemmas showing compatibility with existing delta witnesses.

delta-convolution : ∀ (S T : DirichletSeries) →
  let X = S ⊗ₛ T in
  DeltaNF (baseNF X) ≡ DeltaNF (baseNF S)
delta-convolution _ _ = refl

cumulant-convolution : ∀ (S T : DirichletSeries) →
  let X = S ⊕ₛ T in
  CumulantNF (baseNF X) ≡ CumulantNF (baseNF S)
cumulant-convolution _ _ = refl

-- Functorial action to transport Dirichlet series along normal-form maps.

mapSeries : (NormalForm ⊤ → NormalForm ⊤) → DirichletSeries → DirichletSeries
mapSeries f (mkSeries nf w) =
  mkSeries (f nf) (λ r → let (x , α) = w r in (f x , α))

withRegulator : (Regulator → Regulator) → DirichletSeries → DirichletSeries
withRegulator g (mkSeries nf w) =
  mkSeries nf (λ r → w (g r))
