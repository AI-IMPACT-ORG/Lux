module CLEAN.Core.Sorts where

open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

infixl 50 _+_
_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)

-- | Simple length-indexed vectors so the model stays self-contained.
data Vec {ℓ} (A : Set ℓ) : Nat → Set ℓ where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

-- | Finite sets used for indexing into vectors.
data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

-- | Vector append.
infixr 45 _++_
_++_ : ∀ {ℓ m n} {A : Set ℓ}
      → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

-- | Lookup into a length-indexed vector.
lookup : ∀ {ℓ n} {A : Set ℓ} → Vec A n → Fin n → A
lookup [] ()
lookup (x ∷ xs) zero = x
lookup (x ∷ xs) (suc i) = lookup xs i

-- | The four observable sectors used throughout the CLEAN v10 spec.
data Sort : Set where
  L B R I : Sort

sortName : Sort → String
sortName L = "L"
sortName B = "B"
sortName R = "R"
sortName I = "I"

infixr 40 _∔_
-- | Disjoint sum of sort families used when stitching boundaries together.
_∔_ : Sort → Sort → Sort
L ∔ x = L
B ∔ x = B
R ∔ x = R
I ∔ x = x

-- | Dependent pairs over sorts for labelling diagram nodes.
record Labelled (ℓ : Level) : Set (lsuc ℓ) where
  constructor mk
  field
    sort  : Sort
    label : Set ℓ

open Labelled public

-- | Finite coproduct of sort-indexed families.
record Family (ℓ : Level) : Set (lsuc ℓ) where
  constructor ⟨_⟩
  field
    Carrier : Sort → Set ℓ

open Family public

-- | Pointed carriers for constants such as the gauge fields.
record Pointed (ℓ : Level) : Set (lsuc ℓ) where
  constructor intro
  field
    fam    : Family ℓ
    point  : fam .Carrier I

open Pointed public

-- | Boundary data packages the source and target wire vectors together.
record Boundary (m n : Nat) : Set where
  constructor mkBoundary
  field
    src : Vec Sort m
    dst : Vec Sort n

open Boundary public

-- | Helper constructor when lengths are inferred.
boundaryOf : ∀ {m n} → Vec Sort m → Vec Sort n → Boundary m n
boundaryOf xs ys = mkBoundary xs ys

-- | Parallel tensor of boundaries.
tensorBoundary : ∀ {ℓ₁ m₁ ℓ₂ m₂}
  → Boundary ℓ₁ m₁ → Boundary ℓ₂ m₂
  → Boundary (ℓ₁ + ℓ₂) (m₁ + m₂)
tensorBoundary (mkBoundary xs ys) (mkBoundary xs' ys') =
  mkBoundary (xs ++ xs') (ys ++ ys')
