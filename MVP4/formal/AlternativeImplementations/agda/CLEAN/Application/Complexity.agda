module CLEAN.Application.Complexity where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import CLEAN.Core.NormalForm
open import CLEAN.Ports.Boolean
open import CLEAN.Core.Renormalisability
open import CLEAN.Application.Classification
open import CLEAN.Application.PLBridge

------------------------------------------------------------------------
-- Complexity-aware ports layered on the stratified classification.
------------------------------------------------------------------------

record ComplexityExample : Set₁ where
  constructor example
  field
    stratified : StratifiedLogic
    invariants : Σ LogicOrder (λ _ → ComplexityTag)
    encoding   : Maybe HigherOrderEncoding

complexityExample : StratifiedLogic → ComplexityExample
complexityExample ℒ =
  example ℒ (logicInvariants ℒ) (higherOrderEncodingOf ℒ)

npStratified : StratifiedLogic
npStratified = mkRenormalisable cleanRenormalisable

coNPStratified : StratifiedLogic
coNPStratified = defaultNonRenormalisable

npExample : ComplexityExample
npExample = complexityExample npStratified

coNPExample : ComplexityExample
coNPExample = complexityExample coNPStratified

------------------------------------------------------------------------
-- NP decision port reusing the Boolean evaluation infrastructure.
------------------------------------------------------------------------

record NPDecisionPort : Set₁ where
  constructor mkNPDecisionPort
  field
    stratified            : StratifiedLogic
    invariant             : logicInvariants stratified ≡ (FirstOrder , NPClass)
    domainWitness         : ∀ {Core} (nf : NormalForm Core) → BooleanDomain nf
    evaluator             : ∀ {Core} (nf : NormalForm Core) → BooleanDomain nf → Bool
    evaluatorMatchesBoolean : ∀ {Core} (nf : NormalForm Core) (d : BooleanDomain nf)
                              → evaluator nf d ≡ booleanEval nf d

npDomainWitness : ∀ {Core} (nf : NormalForm Core) → BooleanDomain nf
npDomainWitness _ = suc zero , pos-suc zero

npEvaluator : ∀ {Core} (nf : NormalForm Core) → BooleanDomain nf → Bool
npEvaluator = booleanEval

npEvaluatorMatches : ∀ {Core} (nf : NormalForm Core) (d : BooleanDomain nf)
  → npEvaluator nf d ≡ booleanEval nf d
npEvaluatorMatches _ _ = refl

npDecisionPort : NPDecisionPort
npDecisionPort = mkNPDecisionPort
  npStratified
  refl
  npDomainWitness
  npEvaluator
  npEvaluatorMatches

------------------------------------------------------------------------
-- coNP decision port leveraging the stored higher-order encoding.
------------------------------------------------------------------------

record CoNPDecisionPort : Set₁ where
  constructor mkCoNPDecisionPort
  field
    stratified          : StratifiedLogic
    invariant           : logicInvariants stratified ≡ (HigherOrder , coNPClass)
    encoding            : HigherOrderEncoding
    encodingWitness     : higherOrderEncodingOf stratified ≡ just encoding
    operatorAction      : HOTerm → HOTerm
    operatorActionSpec  : ∀ t → operatorAction t ≡ higherOrderAction encoding t

coNPEncoding : HigherOrderEncoding
coNPEncoding = defaultHigherOrderEncoding

coNPOperatorAction : HOTerm → HOTerm
coNPOperatorAction = higherOrderAction coNPEncoding

coNPOperatorActionSpec : ∀ t → coNPOperatorAction t ≡ higherOrderAction coNPEncoding t
coNPOperatorActionSpec _ = refl

coNPDecisionPort : CoNPDecisionPort
coNPDecisionPort = mkCoNPDecisionPort
  coNPStratified
  refl
  coNPEncoding
  defaultEncodingWitness
  coNPOperatorAction
  coNPOperatorActionSpec
