module CLEAN.Application.PLBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String; primStringAppend)

open import CLEAN.Core.NormalForm
open import CLEAN.Core.System using (trivialNF)

_++_ : String → String → String
_++_ = primStringAppend

infixr 5 _++_

------------------------------------------------------------------------
-- Untyped lambda calculus surface used for PL-style encodings.
------------------------------------------------------------------------

data HOTerm : Set where
  var   : String → HOTerm
  lam   : String → HOTerm → HOTerm
  app   : HOTerm → HOTerm → HOTerm
  const : String → HOTerm

------------------------------------------------------------------------
-- Encoding helpers from CLEAN normal forms into lambda terms.
------------------------------------------------------------------------

private
  encodeSign : Sign → String
  encodeSign plus  = "plus"
  encodeSign minus = "minus"

  encodeHeader : Header → String
  encodeHeader h =
    ("phase(" ++ encodeSign (sign (phaseL h))) ++
    ("," ++ encodeSign (sign (phaseR h)) ++ ")")

encodeNormalFormAsLambda : ∀ {Core} → NormalForm Core → HOTerm
encodeNormalFormAsLambda (mkNF h _) =
  lam "x" (app (const (encodeHeader h)) (var "x"))

------------------------------------------------------------------------
-- Higher-order encoding record exposed to the meta-classification.
------------------------------------------------------------------------

record HigherOrderEncoding : Set₁ where
  constructor mkEncoding
  field
    encodeNF           : ∀ {Core} → NormalForm Core → HOTerm
    prototype          : HOTerm
    higherOrderOperator : HOTerm
    operatorShape      : higherOrderOperator ≡ lam "F" (app (var "F") prototype)
    prototypeIsEncoding : prototype ≡ encodeNF trivialNF

open HigherOrderEncoding public

-- | Apply the stored higher-order operator to a supplied lambda term.
higherOrderAction : HigherOrderEncoding → HOTerm → HOTerm
higherOrderAction enc term = app (higherOrderOperator enc) term

------------------------------------------------------------------------
-- Canonical higher-order encoding induced by the lambda surface.
------------------------------------------------------------------------

defaultHigherOrderEncoding : HigherOrderEncoding
defaultHigherOrderEncoding = mkEncoding
  encodeNormalFormAsLambda
  nfPrototype
  higherOperator
  reproShape
  prototype≡encode
  where
    nfPrototype : HOTerm
    nfPrototype = encodeNormalFormAsLambda trivialNF

    higherOperator : HOTerm
    higherOperator = lam "F" (app (var "F") nfPrototype)

    reproShape : higherOperator ≡ lam "F" (app (var "F") nfPrototype)
    reproShape = refl

    prototype≡encode : nfPrototype ≡ encodeNormalFormAsLambda trivialNF
    prototype≡encode = refl
