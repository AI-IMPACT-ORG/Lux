module CLEAN.Ports.Analytic.DirichletSeries where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Unit using (⊤; tt)

open import CLEAN.Core.Dirichlet
open import CLEAN.Core.NormalForm
open import CLEAN.Ports.Analytic

fstPair : NumberPair → NormalForm ⊤
fstPair (x , _) = x

analyticSeries : DirichletSeries
analyticSeries = mkSeries analyticNF (λ _ → (analyticNF , zero))

conjugateSeries : DirichletSeries
conjugateSeries = mkSeries analyticNF (λ _ → (fstPair analyticZeroPair , zero))

symmetricWeight : ∀ r → DirichletSeries.weight analyticSeries r ≡ DirichletSeries.weight conjugateSeries r
symmetricWeight _ = refl
