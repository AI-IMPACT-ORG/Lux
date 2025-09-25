module Example where

-- Example usage of the BootstrapPaper formal verification library
-- This demonstrates how to use the library in downstream Agda developments

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Generated_Library.AllModules

-- Example: Define a simple theorem using BootstrapPaper components
example-theorem : ModuliSpace → Bool
example-theorem ms = true

-- Example: Use RG operators
example-rg-flow : Bool → Bool
example-rg-flow x = rg-flow (λ y → y) x

-- Example: Test RG anomaly measure
example-anomaly-test : Bool → Bool
example-anomaly-test x = rg-anomaly-measure x

-- Example: Verify RG properties
example-rg-property : ∀ (x : Bool) → rg-anomaly-measure (rg-anomaly-measure x) ≡ x
example-rg-property x = rg-anomaly-involutive x

-- Example: Use concrete moduli values
example-moduli-access : ModuliSpace → Nat
example-moduli-access ms = get-mu1 ms

-- Example: Test moduli constraints
example-moduli-constraints : ModuliSpace → Bool
example-moduli-constraints ms = mu1-positive ms

-- Example: Use theorem helpers
example-consistency : Bool → Bool
example-consistency x = consistency-theorem x

example-completeness : Bool → Bool
example-completeness x = completeness-theorem x

example-soundness : Bool → Bool
example-soundness x = soundness-theorem x

-- Example: Mathematical theorem tests
example-goedel : Bool → Bool
example-goedel x = goedel-theorem-test x

example-tarski : Bool → Bool
example-tarski x = tarski-theorem-test x

example-rice : Bool → Bool
example-rice x = rice-theorem-test x

example-noether : Bool → Bool
example-noether x = noether-theorem-test x

example-ward : Bool → Bool
example-ward x = ward-theorem-test x

-- Example: Type preservation tests
example-type-preservation : ∀ {A B : Set} → (f : A → B) → (x : A) → Bool
example-type-preservation f x = rg-type-preservation f x

-- Example: Well-typed theorem helpers
example-well-typed : ∀ {A : Set} → (x : A) → Bool
example-well-typed x = theorem-helpers-well-typed x

-- Example: Integration test
example-integration : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → (x : A) →
  rg-flow (g ∘ f) x ≡ g (f x)
example-integration f g x = rg-flow-composition-test f g x
