module CLEAN.Library.CriticalLine where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat using (zero)

open import CLEAN.Core.NormalForm
open import CLEAN.Core.Signature using (OpId; GaugeΛ)
open import CLEAN.Application.Classification
open import CLEAN.Application.Complexity using (coNPStratified)
open import CLEAN.Ports.Analytic
open import CLEAN.Core.Dirichlet
open import CLEAN.Core.EulerProduct

------------------------------------------------------------------------
-- Lambda-based argument for the critical line property.
------------------------------------------------------------------------

record LambdaDeformation : Set where
  constructor mkLambdaDeformation
  field
    baseline         : NormalForm ⊤
    lambdaTruth      : NormalForm ⊤
    deformationProof : lambdaTruth ≡ DeltaNF baseline
    operator         : OpId
    operatorIsLambda : operator ≡ GaugeΛ

lambdaCriticalLineWitness : LambdaDeformation → CriticalLineWitness sampleField
lambdaCriticalLineWitness _ = criticalLineFromStar swapStar

lambdaCriticalLineOutcome : LambdaDeformation → LogicOutcome coNPStratified sampleField
lambdaCriticalLineOutcome _ = godelCriticalLine

lambdaRegulator : LambdaDeformation → Regulator
lambdaRegulator _ = mkRegulator zero

lambdaDirichlet : LambdaDeformation → DirichletSeries
lambdaDirichlet lam = dirichletSum (LambdaDeformation.baseline lam) (lambdaRegulator lam)
