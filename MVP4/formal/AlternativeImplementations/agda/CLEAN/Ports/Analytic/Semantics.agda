module CLEAN.Ports.Analytic.Semantics where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤)

open import CLEAN.Core.Dirichlet
open import CLEAN.Core.NormalForm
open import CLEAN.Ports.Analytic.ZetaDefinition

open LogicalZeta

private
  mapEq : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
  mapEq f eq rewrite eq = refl

------------------------------------------------------------------------
-- Denotational view: a logical zeta series evaluated in a carrier.
------------------------------------------------------------------------

record LogicalZetaDenotation : Set₁ where
  constructor mkDenotation
  field
    Carrier       : Set
    dirichletSem  : Regulator → Carrier
    eulerSem      : Regulator → Carrier
    deltaSemantic : ∀ r → dirichletSem r ≡ eulerSem r

open LogicalZetaDenotation public

-- | Trivial denotation via normal-form evaluation.
identityDenotation : LogicalZeta → LogicalZetaDenotation
identityDenotation ζ = mkDenotation
  (NormalForm ⊤)
  (λ r → DeltaNF (evaluateSeries (dirichletSeries ζ r) r))
  (λ r → evaluateSeries (eulerSeries ζ r) r)
  (deltaAgreement ζ)

-- | Push a logical zeta through a user-supplied interpretation.
interpretDenotation : ∀ {A : Set} → (NormalForm ⊤ → A) → LogicalZeta → LogicalZetaDenotation
interpretDenotation {A} interpret ζ = mkDenotation
  A
  (λ r → interpret (DeltaNF (evaluateSeries (dirichletSeries ζ r) r)))
  (λ r → interpret (evaluateSeries (eulerSeries ζ r) r))
  (λ r → mapEq interpret (deltaAgreement ζ r))
