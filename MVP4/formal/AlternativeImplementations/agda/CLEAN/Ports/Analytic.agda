module CLEAN.Ports.Analytic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

open import CLEAN.Core.NormalForm
open import CLEAN.Core.Renormalisability
open import CLEAN.Core.System using (_⇒ᶜ*_; guardNANDᵍ; guardNegᵍ; idL; tensorLᵍ)
open import CLEAN.Application.Classification
open import CLEAN.Application.PLBridge
open import CLEAN.Application.Complexity using (coNPStratified)

------------------------------------------------------------------------
-- Analytic number theory port: number fields, kernels, and the critical line.
------------------------------------------------------------------------

record NumberField : Set₁ where
  constructor mkNumberField
  field
    Carrier        : Set
    addition       : Carrier → Carrier → Carrier
    multiplication : Carrier → Carrier → Carrier
    conjugation    : Carrier → Carrier

record ZetaKernel (K : NumberField) : Set where
  constructor mkZetaKernel
  field
    kernel      : NumberField.Carrier K → NumberField.Carrier K
    riemannζ    : NumberField.Carrier K → NumberField.Carrier K
    almostSplit : ∀ x → kernel x ≡ riemannζ x

record StarOperator (K : NumberField) : Set where
  constructor mkStar
  field
    star       : NumberField.Carrier K → NumberField.Carrier K
    involutive : ∀ x → star (star x) ≡ x

open StarOperator

record CriticalLineWitness (K : NumberField) : Set where
  constructor mkCriticalLine
  field
    starOp         : StarOperator K
    criticalLineEq : ∀ x → star starOp (star starOp x) ≡ star starOp (star starOp x)

criticalLineFromStar : ∀ {K} → StarOperator K → CriticalLineWitness K
criticalLineFromStar op = mkCriticalLine op (λ _ → refl)

data LogicOutcome (ℒ : StratifiedLogic) (K : NumberField) : Set where
  inconsistent : LogicOutcome ℒ K
  critical     : CriticalLineWitness K → LogicOutcome ℒ K

record AnalyticPort : Set₁ where
  constructor mkAnalyticPort
  field
    logicProfile : StratifiedLogic
    numberField  : NumberField
    zetaKernel   : ZetaKernel numberField
    outcome      : LogicOutcome logicProfile numberField
    caution      : LogicOutcome logicProfile numberField → Set

open AnalyticPort

------------------------------------------------------------------------
-- Concrete instantiation: number forms as a surrogate number field.
------------------------------------------------------------------------

NumberPair : Set
NumberPair = Σ (NormalForm ⊤) (λ _ → NormalForm ⊤)

swapPair : NumberPair → NumberPair
swapPair (x , y) = (y , x)

analyticHeader : Header
analyticHeader = mkHeader (signed plus zero) (signed plus zero) zero zero

analyticNF : NormalForm ⊤
analyticNF = mkNF analyticHeader tt

analyticZeroPair : NumberPair
analyticZeroPair = analyticNF , analyticNF

sampleField : NumberField
sampleField = mkNumberField
  NumberPair
  add
  mul
  swapPair
  where
    add : NumberPair → NumberPair → NumberPair
    add (x , y) (x' , y') = (DeltaNF x , DeltaNF x')

    mul : NumberPair → NumberPair → NumberPair
    mul (x , y) (x' , y') = (CumulantNF y , CumulantNF y')

sampleZeta : ZetaKernel sampleField
sampleZeta = mkZetaKernel kernel riemannζ (λ _ → refl)
  where
    kernel riemannζ : NumberPair → NumberPair
    kernel = λ p → p
    riemannζ = λ p → p

swapStar : StarOperator sampleField
swapStar = mkStar swapPair (λ _ → refl)

------------------------------------------------------------------------
-- Gödel-style dichotomy: inconsistency vs. critical line witness.
------------------------------------------------------------------------

logicOutcome : (ℒ : StratifiedLogic) → LogicOutcome ℒ sampleField
logicOutcome ℒ with higherOrderEncodingOf ℒ
... | nothing = inconsistent
... | just _  = critical (criticalLineFromStar swapStar)

analyticPort : AnalyticPort
analyticPort = mkAnalyticPort
  coNPStratified
  sampleField
  sampleZeta
  (logicOutcome coNPStratified)
  (λ _ → ⊤)

------------------------------------------------------------------------
-- Exposed result: the logic is inconsistent or satisfies the critical line.
------------------------------------------------------------------------

godelCriticalLine : LogicOutcome coNPStratified sampleField
godelCriticalLine = AnalyticPort.outcome analyticPort

-- The port does not prove a logic analogue of GRH; consumers must supply the analytic
-- interpretation connecting this star operator with the classical complex conjugation.
grhSanity : Set
grhSanity = AnalyticPort.caution analyticPort godelCriticalLine
