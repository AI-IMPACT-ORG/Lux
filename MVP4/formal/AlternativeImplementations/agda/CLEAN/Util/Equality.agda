module CLEAN.Util.Equality where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Tiny combinators for chaining equality proofs.
------------------------------------------------------------------------

transEq : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

symEq : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
symEq refl = refl

congEq : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
congEq f refl = refl
