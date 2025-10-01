module CLEAN.Core.Diagram where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import CLEAN.Core.Signature
open import CLEAN.Core.Sorts

-- | String diagrams indexed by their boundary vectors.
data Diagram (Σ : Signature) : ∀ {m n} → Vec Sort m → Vec Sort n → Set where
  idD : ∀ {m} {xs : Vec Sort m} → Diagram Σ xs xs
  gen : (op : Operation Σ)
      → Diagram Σ (inputs (dataOf Σ op)) (outputs (dataOf Σ op))
  _∘_ : ∀ {ℓ m n}
       {xs : Vec Sort ℓ} {ys : Vec Sort m} {zs : Vec Sort n}
       → Diagram Σ ys zs → Diagram Σ xs ys → Diagram Σ xs zs
  _⊗_ : ∀ {ℓ₁ ℓ₂ m₁ m₂}
       {xs₁ : Vec Sort ℓ₁} {xs₂ : Vec Sort ℓ₂}
       {ys₁ : Vec Sort m₁} {ys₂ : Vec Sort m₂}
       → Diagram Σ xs₁ ys₁ → Diagram Σ xs₂ ys₂ → Diagram Σ (xs₁ ++ xs₂) (ys₁ ++ ys₂)

infixr 40 _⊗_
infixl 45 _∘_

-- | Convenience helper exposing the boundary record for a diagram shape.
boundaryShape : ∀ {Σ m n} {xs : Vec Sort m} {ys : Vec Sort n}
  → Diagram Σ xs ys → Boundary m n
boundaryShape {xs = xs} {ys = ys} _ = mkBoundary xs ys

-- | Placeholder symmetry record for future braiding refinements.
record Symmetry {Σ m} (xs : Vec Sort m) : Set where
  constructor swap
  field
    symmetry : Diagram Σ (xs ++ []) ([] ++ xs)
