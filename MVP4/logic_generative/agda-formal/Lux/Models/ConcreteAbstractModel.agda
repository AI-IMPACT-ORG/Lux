-- (c) 2025 AI.IMPACT GmbH

{-# OPTIONS --cubical --without-K #-}

module Lux.Models.ConcreteAbstractModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)

open import Lux.Foundations.Types
open import Lux.Models.AbstractModel

-- ============================================================================
-- CONCRETE INSTANTIATION OF ABSTRACT MODEL
-- ============================================================================

-- Simple concrete semiring: natural numbers with max and plus
data NatSemiring : Set where
  zero : NatSemiring
  suc : NatSemiring → NatSemiring

-- Addition (max)
_⊕N_ : NatSemiring → NatSemiring → NatSemiring
zero ⊕N y = y
suc x ⊕N zero = suc x
suc x ⊕N suc y = suc (x ⊕N y)

-- Multiplication (plus)
_⊗N_ : NatSemiring → NatSemiring → NatSemiring
zero ⊗N _ = zero
suc x ⊗N y = y ⊕N (x ⊗N y)

-- Semiring laws for natural numbers
nat-semiring : AbstractSemiring
nat-semiring = record
  { Carrier = NatSemiring
  ; _⊕_ = _⊕N_
  ; _⊗_ = _⊗N_
  ; zero = zero
  ; one = suc zero
  ; ⊕-assoc = λ x y z → ⊕N-assoc x y z
  ; ⊕-comm = λ x y → ⊕N-comm x y
  ; ⊕-identity = λ x → ⊕N-identity x
  ; ⊗-assoc = λ x y z → ⊗N-assoc x y z
  ; ⊗-comm = λ x y → ⊗N-comm x y
  ; ⊗-identity = λ x → ⊗N-identity x
  ; distrib = λ x y z → ⊗N-distrib x y z
  ; zero-absorb = λ x → ⊗N-zero-absorb x
  }
  where
    -- Proofs of semiring laws for naturals
    ⊕N-assoc : ∀ x y z → (x ⊕N y) ⊕N z ≡ x ⊕N (y ⊕N z)
    ⊕N-assoc zero y z = refl
    ⊕N-assoc (suc x) zero z = refl
    ⊕N-assoc (suc x) (suc y) zero = refl
    ⊕N-assoc (suc x) (suc y) (suc z) = cong suc (⊕N-assoc x y z)
    
    ⊕N-comm : ∀ x y → x ⊕N y ≡ y ⊕N x
    ⊕N-comm zero zero = refl
    ⊕N-comm zero (suc y) = refl
    ⊕N-comm (suc x) zero = refl
    ⊕N-comm (suc x) (suc y) = cong suc (⊕N-comm x y)
    
    ⊕N-identity : ∀ x → x ⊕N zero ≡ x
    ⊕N-identity zero = refl
    ⊕N-identity (suc x) = refl
    
    ⊗N-assoc : ∀ x y z → (x ⊗N y) ⊗N z ≡ x ⊗N (y ⊗N z)
    ⊗N-assoc zero y z = refl
    ⊗N-assoc (suc x) y z = 
      begin
        (y ⊕N (x ⊗N y)) ⊗N z
      ≡⟨ ⊗N-distrib y (x ⊗N y) z ⟩
        (y ⊗N z) ⊕N ((x ⊗N y) ⊗N z)
      ≡⟨ cong (λ w → (y ⊗N z) ⊕N w) (⊗N-assoc x y z) ⟩
        (y ⊗N z) ⊕N (x ⊗N (y ⊗N z))
      ≡⟨⟩
        suc x ⊗N (y ⊗N z)
      ∎
      where open ≡-Reasoning
    
    ⊗N-comm : ∀ x y → x ⊗N y ≡ y ⊗N x
    ⊗N-comm zero y = ⊗N-zero-absorb y
    ⊗N-comm (suc x) zero = ⊗N-zero-absorb (suc x)
    ⊗N-comm (suc x) (suc y) = 
      begin
        suc y ⊕N (x ⊗N suc y)
      ≡⟨ cong (λ w → suc y ⊕N w) (⊗N-comm x (suc y)) ⟩
        suc y ⊕N (suc y ⊗N x)
      ≡⟨⟩
        suc y ⊗N suc x
      ∎
      where open ≡-Reasoning
    
    ⊗N-identity : ∀ x → x ⊗N suc zero ≡ x
    ⊗N-identity zero = refl
    ⊗N-identity (suc x) = 
      begin
        suc zero ⊕N (x ⊗N suc zero)
      ≡⟨ cong (λ w → suc zero ⊕N w) (⊗N-identity x) ⟩
        suc zero ⊕N x
      ≡⟨ ⊕N-comm (suc zero) x ⟩
        x ⊕N suc zero
      ≡⟨ ⊕N-identity x ⟩
        x
      ∎
      where open ≡-Reasoning
    
    ⊗N-distrib : ∀ x y z → x ⊗N (y ⊕N z) ≡ (x ⊗N y) ⊕N (x ⊗N z)
    ⊗N-distrib zero y z = refl
    ⊗N-distrib (suc x) y z = 
      begin
        (y ⊕N z) ⊕N (x ⊗N (y ⊕N z))
      ≡⟨ cong (λ w → (y ⊕N z) ⊕N w) (⊗N-distrib x y z) ⟩
        (y ⊕N z) ⊕N ((x ⊗N y) ⊕N (x ⊗N z))
      ≡⟨ ⊕N-assoc (y ⊕N z) (x ⊗N y) (x ⊗N z) ⟩
        ((y ⊕N z) ⊕N (x ⊗N y)) ⊕N (x ⊗N z)
      ≡⟨ cong (λ w → w ⊕N (x ⊗N z)) (⊕N-assoc y z (x ⊗N y)) ⟩
        (y ⊕N (z ⊕N (x ⊗N y))) ⊕N (x ⊗N z)
      ≡⟨ cong (λ w → (y ⊕N w) ⊕N (x ⊗N z)) (⊕N-comm z (x ⊗N y)) ⟩
        (y ⊕N ((x ⊗N y) ⊕N z)) ⊕N (x ⊗N z)
      ≡⟨ sym (⊕N-assoc y (x ⊗N y) z) ⟩
        ((y ⊕N (x ⊗N y)) ⊕N z) ⊕N (x ⊗N z)
      ≡⟨ ⊕N-assoc (y ⊕N (x ⊗N y)) z (x ⊗N z) ⟩
        (y ⊕N (x ⊗N y)) ⊕N (z ⊕N (x ⊗N z))
      ≡⟨⟩
        (suc x ⊗N y) ⊕N (suc x ⊗N z)
      ∎
      where open ≡-Reasoning
    
    ⊗N-zero-absorb : ∀ x → x ⊗N zero ≡ zero
    ⊗N-zero-absorb zero = refl
    ⊗N-zero-absorb (suc x) = ⊗N-zero-absorb x

-- Concrete observer system for naturals
nat-observers : AbstractObserverSystem nat-semiring nat-semiring nat-semiring
nat-observers = record
  { νL = λ x → x
  ; νR = λ x → x
  ; ιL = λ x → x
  ; ιR = λ x → x
  ; retraction-L = λ x → refl
  ; retraction-R = λ x → refl
  ; hom-L-add = λ x y → refl
  ; hom-R-add = λ x y → refl
  ; hom-L-mult = λ x y → refl
  ; hom-R-mult = λ x y → refl
  ; νL-zero = refl
  ; νL-one = refl
  ; νR-zero = refl
  ; νR-one = refl
  }

-- Concrete central scalars for naturals
nat-central-scalars : AbstractCentralScalars nat-semiring
nat-central-scalars = record
  { φ = suc zero
  ; z = suc zero
  ; z̄ = suc zero
  ; Λ = suc zero
  ; φ-central = λ x → ⊗N-comm (suc zero) x
  ; z-central = λ x → ⊗N-comm (suc zero) x
  ; z̄-central = λ x → ⊗N-comm (suc zero) x
  ; Λ-central = λ x → ⊗N-comm (suc zero) x
  ; Λ-definition = refl
  ; φ-unit-left = ⊗N-identity (suc zero)
  ; φ-unit-right = ⊗N-identity (suc zero)
  ; z-unit-left = ⊗N-identity (suc zero)
  ; z-unit-right = ⊗N-identity (suc zero)
  ; z̄-unit-left = ⊗N-identity (suc zero)
  ; z̄-unit-right = ⊗N-identity (suc zero)
  ; Λ-unit-left = ⊗N-identity (suc zero)
  ; Λ-unit-right = ⊗N-identity (suc zero)
  }
  where
    open AbstractSemiring nat-semiring using (⊗-comm; ⊗-identity)
    ⊗N-comm = AbstractSemiring.⊗-comm nat-semiring
    ⊗N-identity = AbstractSemiring.⊗-identity nat-semiring

-- Concrete braiding operations for naturals
nat-braiding : AbstractBraidingOperations nat-semiring
nat-braiding = record
  { ad₀ = λ x → x
  ; ad₁ = λ x → x
  ; ad₂ = λ x → x
  ; ad₃ = λ x → x
  ; yang-baxter-01 = λ t → refl
  ; yang-baxter-12 = λ t → refl
  ; yang-baxter-23 = λ t → refl
  ; comm-02 = λ t → refl
  ; comm-03 = λ t → refl
  ; comm-13 = λ t → refl
  ; braid-add = λ t u → refl
  ; braid-mult = λ t u → refl
  }

-- Complete concrete abstract model
concrete-abstract-model : AbstractModel
concrete-abstract-model = record
  { left-semiring = nat-semiring
  ; right-semiring = nat-semiring
  ; bulk-semiring = nat-semiring
  ; core-semiring = nat-semiring
  ; observers = nat-observers
  ; central-scalars = nat-central-scalars
  ; braiding = nat-braiding
  ; cross-centrality = λ x y → refl
  ; local-faithfulness-L = λ x t → refl
  ; local-faithfulness-R = λ y t → refl
  ; gen4-axiom = λ a₀ a₁ a₂ a₃ → refl
  }

