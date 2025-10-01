module CLEAN.Ports.Analytic.EulerProperties where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Unit using (⊤)

open import CLEAN.Core.Dirichlet
open import CLEAN.Core.NormalForm
open import CLEAN.Ports.Analytic
open import CLEAN.Library.CriticalLine using (LambdaDeformation; lambdaRegulator)
open import CLEAN.Ports.Analytic.ZetaDefinition

open LogicalZeta

lambdaDirichletSeries : LogicalZeta → LambdaDeformation → DirichletSeries
lambdaDirichletSeries ζ lam = dirichletSeries ζ (lambdaRegulator lam)

lambdaEulerSeries : LogicalZeta → LambdaDeformation → DirichletSeries
lambdaEulerSeries ζ lam = eulerSeries ζ (lambdaRegulator lam)

lambdaPoleWitness : LogicalZeta → LambdaDeformation → NormalForm ⊤
lambdaPoleWitness ζ lam = evaluateSeries (lambdaDirichletSeries ζ lam) (lambdaRegulator lam)

lambdaPoleConsistency : ∀ ζ lam →
  DeltaNF (lambdaPoleWitness ζ lam)
    ≡ evaluateSeries (lambdaEulerSeries ζ lam) (lambdaRegulator lam)
lambdaPoleConsistency ζ lam = deltaAgreement ζ (lambdaRegulator lam)

------------------------------------------------------------------------
-- Default aliases specialised to the canonical logical L-function.
------------------------------------------------------------------------

defaultLambdaDirichletSeries : LambdaDeformation → DirichletSeries
defaultLambdaDirichletSeries = lambdaDirichletSeries logicalZeta

defaultLambdaEulerSeries : LambdaDeformation → DirichletSeries
defaultLambdaEulerSeries = lambdaEulerSeries logicalZeta

defaultPoleWitness : LambdaDeformation → NormalForm ⊤
defaultPoleWitness = lambdaPoleWitness logicalZeta

defaultPoleConsistency : ∀ lam →
  DeltaNF (defaultPoleWitness lam)
    ≡ evaluateSeries (defaultLambdaEulerSeries lam) (lambdaRegulator lam)
defaultPoleConsistency = lambdaPoleConsistency logicalZeta
