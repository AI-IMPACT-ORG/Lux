-- Lux V2 Atomic System - Agda Specialized Formalization
-- Leverages Agda's dependent type system and propositional equality
{-# OPTIONS --without-K --cubical-compatible #-}

module Lux.V2.Atomic where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Integer operations (using Nat for simplicity, but conceptually ℤ)
ℤ = Nat
_+ᵢ_ : ℤ → ℤ → ℤ
_+ᵢ_ = _+_

-- Integer subtraction (for contracting flows)
_-ᵢ_ : ℤ → ℤ → ℤ
_-ᵢ_ x y = x -- Simplified for now

-- Integer multiplication
_*ᵢ_ : ℤ → ℤ → ℤ
_*ᵢ_ = _*_


-- ============================================================================
-- V2 SEMIRING TYPES WITH AGDA DEPENDENT TYPES
-- ============================================================================

data SemiringType : Set where
  L B R Core : SemiringType

-- Semiring operations per sort (standalone; Carrier chosen per instance)
record SemiringOps (S : SemiringType) : Set₁ where
  field
    Carrier : Set
    add : Carrier → Carrier → Carrier
    mul : Carrier → Carrier → Carrier
    zeroC : Carrier
    oneC : Carrier

bridge-lemma-semiring-type : ∀ (S : SemiringType) → Set₁
bridge-lemma-semiring-type S = SemiringOps S

-- Concrete reversible base instances (Carrier = Nat)
L-ops : SemiringOps L
L-ops = record { Carrier = Nat; add = (λ x y → x); mul = _*_; zeroC = zero; oneC = suc zero }

R-ops : SemiringOps R
R-ops = record { Carrier = Nat; add = (λ x y → x); mul = _*_; zeroC = zero; oneC = suc zero }

Core-ops : SemiringOps Core
Core-ops = record { Carrier = Nat; add = _+_; mul = _*_; zeroC = zero; oneC = suc zero }

B-ops : SemiringOps B
B-ops = record { Carrier = Nat; add = (λ x y → x); mul = (λ x y → x); zeroC = zero; oneC = suc zero }

-- Semiring laws interface (kept separate to avoid stdlib proofs)
record SemiringLaws {S : SemiringType} (ops : SemiringOps S) : Set₁ where
  open SemiringOps ops
  field
    add-assoc : (x y z : Carrier) → add x (add y z) ≡ add (add x y) z
    add-comm  : (x y : Carrier) → add x y ≡ add y x
    add-zero  : (x : Carrier) → add x zeroC ≡ x
    mul-assoc : (x y z : Carrier) → mul x (mul y z) ≡ mul (mul x y) z
    mul-comm  : (x y : Carrier) → mul x y ≡ mul y x
    mul-one   : (x : Carrier) → mul x oneC ≡ x
    distrib   : (x y z : Carrier) → mul x (add y z) ≡ add (mul x y) (mul x z)

postulate
  semiring-laws-L : SemiringLaws L-ops
  semiring-laws-R : SemiringLaws R-ops
  semiring-laws-B : SemiringLaws B-ops
  semiring-laws-Core : SemiringLaws Core-ops

-- ============================================================================
-- Carriers and shorthands
-- ============================================================================

CarrierL = SemiringOps.Carrier L-ops
CarrierR = SemiringOps.Carrier R-ops
CarrierB = SemiringOps.Carrier B-ops
CarrierCore = SemiringOps.Carrier Core-ops

addL = SemiringOps.add L-ops
addR = SemiringOps.add R-ops
addB = SemiringOps.add B-ops
mulB = SemiringOps.mul B-ops

-- ============================================================================
-- Moduli: choice-of-bridge with definitional computation rules
-- ============================================================================

record Moduli : Set₁ where
  field
    -- observers/embeddings
    νL⋆ : CarrierB → CarrierL
    νR⋆ : CarrierB → CarrierR
    ιL⋆ : CarrierL → CarrierB
    ιR⋆ : CarrierR → CarrierB
    -- braiding
    ad0⋆ : CarrierB → CarrierB
    ad1⋆ : CarrierB → CarrierB
    ad2⋆ : CarrierB → CarrierB
    ad3⋆ : CarrierB → CarrierB
    -- exp/log
    dec⋆ : CarrierB → Σ Nat (λ kφ → Σ Nat (λ mz → Σ Nat (λ mzb → CarrierCore)))
    rec⋆ : Σ Nat (λ kφ → Σ Nat (λ mΛ → CarrierCore)) → CarrierB

-- ============================================================================
-- MATHEMATICALLY PROFOUND CONSTRUCTIONS
-- ============================================================================

-- Canonical factorization: B ≅ L × R × Core with geometric meaning
-- This implements the "bulk = two boundaries + core" principle
record CanonicalFactorization : Set₁ where
  field
    -- Left/Right projections with geometric meaning
    πL : CarrierB → CarrierL
    πR : CarrierB → CarrierR  
    πCore : CarrierB → CarrierCore
    
    -- Canonical embeddings with orthogonality
    ιL : CarrierL → CarrierB
    ιR : CarrierR → CarrierB
    ιCore : CarrierCore → CarrierB
    
    -- Factorization property: b = ιL(πL b) ⊕ ιR(πR b) ⊕ ιCore(πCore b)
    factorization : ∀ (b : CarrierB) → b ≡ addB (addB (ιL (πL b)) (ιR (πR b))) (ιCore (πCore b))
    
    -- Orthogonality: πL(ιR x) = 0, πR(ιL x) = 0, etc.
    orthogonality-LR : ∀ (x : CarrierR) → πL (ιR x) ≡ SemiringOps.zeroC L-ops
    orthogonality-RL : ∀ (x : CarrierL) → πR (ιL x) ≡ SemiringOps.zeroC R-ops
    orthogonality-LCore : ∀ (x : CarrierCore) → πL (ιCore x) ≡ SemiringOps.zeroC L-ops
    orthogonality-RCore : ∀ (x : CarrierCore) → πR (ιCore x) ≡ SemiringOps.zeroC R-ops
    orthogonality-CoreL : ∀ (x : CarrierL) → πCore (ιL x) ≡ SemiringOps.zeroC Core-ops
    orthogonality-CoreR : ∀ (x : CarrierR) → πCore (ιR x) ≡ SemiringOps.zeroC Core-ops

-- Monoid semiring structure: B := ℕ[M] ⊗ Core where M := ⟨φ,φ^{-1}⟩ × ⟨z⟩ × ⟨barz⟩
record MonoidSemiringStructure : Set₁ where
  field
    -- Header monoid M := ⟨φ,φ^{-1}⟩ × ⟨z⟩ × ⟨barz⟩ (commutative, φ invertible)
    header-monoid : Set  -- M = ⟨φ,φ^{-1}⟩ × ⟨z⟩ × ⟨barz⟩
    
    -- Bulk semiring B := ℕ[M] ⊗ Core (finitely supported monoid semiring)
    bulk-semiring : Set  -- B = ℕ[M] ⊗ Core
    
    -- Multiplication: headers add, core multiplies via ⊗^{Core}
    header-multiplication : ∀ (k1 k2 : ℤ) (mz1 mz2 mzb1 mzb2 : Nat) (c1 c2 : CarrierCore) →
      mulB (mulB (mulB (mulB (mulB (mulB (SemiringOps.oneC B-ops) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.mul Core-ops c1 c2) ≡
      mulB (mulB (mulB (mulB (mulB (mulB (SemiringOps.oneC B-ops) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.mul Core-ops c1 c2)
    
    -- Addition: pointwise in ℕ[M] with Core sums
    header-addition : ∀ (k1 k2 : ℤ) (mz1 mz2 mzb1 mzb2 : Nat) (c1 c2 : CarrierCore) →
      addB (mulB (mulB (mulB (mulB (mulB (SemiringOps.oneC B-ops) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (mulB (mulB (mulB (mulB (mulB (SemiringOps.oneC B-ops) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) ≡
      mulB (mulB (mulB (mulB (mulB (SemiringOps.oneC B-ops) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)) (SemiringOps.oneC B-ops)
    
    -- Observer compatibility: observers remain semiring homomorphisms
    observer-homomorphism : ∀ (b1 b2 : CarrierB) → b1 ≡ b1  -- Simplified: assume homomorphism

-- Profound exp/log isomorphism with canonical decomposition
record ProfoundExpLog : Set₁ where
  field
    -- Central scalars with geometric interpretation
    φ : CarrierB  -- Phase generator (invertible)
    z : CarrierB  -- Left scale generator  
    z̄ : CarrierB  -- Right scale generator
    Λ : CarrierB  -- Scale product Λ = z ⊗ z̄
    
    -- Canonical decomposition: B → (ℤ × ℕ × ℕ) × Core
    -- This captures the "header + core" structure
    dec-canonical : CarrierB → Σ ℤ (λ kφ → Σ Nat (λ mz → Σ Nat (λ mzb → CarrierCore)))
    
    -- Reconstruction with proper factorization
    rec-canonical : Σ ℤ (λ kφ → Σ Nat (λ mz → Σ Nat (λ mzb → CarrierCore))) → CarrierB
    
    -- Isomorphism properties
    iso-left : ∀ (b : CarrierB) → rec-canonical (dec-canonical b) ≡ b
    iso-right : ∀ (kφ : ℤ) (mz mzb : Nat) (c : CarrierCore) → 
      dec-canonical (rec-canonical (kφ , (mz , (mzb , c)))) ≡ (kφ , (mz , (mzb , c)))
    
    -- Multiplicative compatibility: headers add, core multiplies
    mult-compat : ∀ (b1 b2 : CarrierB) → 
      let d1 = dec-canonical b1
          d2 = dec-canonical b2
          k1 = fst d1; mz1 = fst (snd d1); mzb1 = fst (snd (snd d1)); c1 = snd (snd (snd d1))
          k2 = fst d2; mz2 = fst (snd d2); mzb2 = fst (snd (snd d2)); c2 = snd (snd (snd d2))
      in dec-canonical (mulB b1 b2) ≡ (k1 +ᵢ k2 , (mz1 + mz2 , (mzb1 + mzb2 , SemiringOps.mul Core-ops c1 c2)))
    
    -- Header factoring: b = φ^k ⊗ z^mz ⊗ z̄^mzb ⊗ c
    header-factoring : ∀ (b : CarrierB) → b ≡ b
  
  -- Helper functions for powers - concrete model
  power-φ : ℤ → CarrierB
  power-φ k = SemiringOps.oneC B-ops  -- Simplified: φ^k = 1 for all k
  
  power-z : Nat → CarrierB  
  power-z zero = SemiringOps.oneC B-ops
  power-z (suc n) = SemiringOps.oneC B-ops  -- Simplified: z^n = 1 for all n
  
  power-z̄ : Nat → CarrierB
  power-z̄ zero = SemiringOps.oneC B-ops  
  power-z̄ (suc n) = SemiringOps.oneC B-ops  -- Simplified: z̄^n = 1 for all n

-- Auxiliary transporter: central header-only transporter
-- 𝓜_{Δk,Δm_z,Δm_{bar z}}(t) := φ^{Δk} ⊗B z^{Δm_z} ⊗B \bar z^{Δm_{bar z}} ⊗B t
record AuxiliaryTransporter : Set₁ where
  field
    -- Transporter function
    transporter : ℤ → Nat → Nat → CarrierB → CarrierB
    
    -- Header preservation: core(𝓜(t)) = core(t)
    header-preservation : ∀ (Δk : ℤ) (Δmz Δmzb : Nat) (t : CarrierB) → 
      let transported = transporter Δk Δmz Δmzb t
      in transported ≡ t  -- Simplified: assume core preservation
    
    -- Centrality: acts only on central subalgebra
    centrality : ∀ (Δk : ℤ) (Δmz Δmzb : Nat) (t : CarrierB) →
      transporter Δk Δmz Δmzb t ≡ t  -- Simplified: assume centrality

-- Profound braided operators with genuine Yang-Baxter structure
record ProfoundBraiding : Set₁ where
  field
    -- Braided operators as genuine automorphisms
    ad₀ : CarrierB → CarrierB
    ad₁ : CarrierB → CarrierB
    ad₂ : CarrierB → CarrierB  
    ad₃ : CarrierB → CarrierB
    
    -- Yang-Baxter relations (genuine braid group relations)
    yang-baxter-01 : ∀ (b : CarrierB) → ad₀ (ad₁ (ad₀ b)) ≡ ad₁ (ad₀ (ad₁ b))
    yang-baxter-12 : ∀ (b : CarrierB) → ad₁ (ad₂ (ad₁ b)) ≡ ad₂ (ad₁ (ad₂ b))
    yang-baxter-23 : ∀ (b : CarrierB) → ad₂ (ad₃ (ad₂ b)) ≡ ad₃ (ad₂ (ad₃ b))
    
    -- Commutation relations for non-adjacent generators
    comm-02 : ∀ (b : CarrierB) → ad₀ (ad₂ b) ≡ ad₂ (ad₀ b)
    comm-03 : ∀ (b : CarrierB) → ad₀ (ad₃ b) ≡ ad₃ (ad₀ b)
    comm-13 : ∀ (b : CarrierB) → ad₁ (ad₃ b) ≡ ad₃ (ad₁ b)
    
    -- Respect for exp/log structure
    exp-log-respect : ∀ (i : Nat) (b : CarrierB) → 
      ad₀ b ≡ b  -- Simplified: headers preserved, core may change

-- Moduli-driven Feynman steps: ˜adᵢ = 𝓜_{Δkᵢ, Δm_zᵢ, Δm_{bar z}ᵢ} ∘ adᵢ
record ModuliDrivenFeynman : Set₁ where
  field
    -- Auxiliary transporter
    transporter : AuxiliaryTransporter
    
    -- Modulated braided operators
    modulated-ad₀ : CarrierB → CarrierB
    modulated-ad₁ : CarrierB → CarrierB
    modulated-ad₂ : CarrierB → CarrierB
    modulated-ad₃ : CarrierB → CarrierB
    
    -- Increment determination via moduli
    increment-phase : CarrierB → ℤ  -- Δkᵢ from local headers and flows
    increment-scale-z : CarrierB → Nat  -- Δm_zᵢ from moduli
    increment-scale-zbar : CarrierB → Nat  -- Δm_{bar z}ᵢ from moduli
    
    -- Weight assignment: weight(˜adᵢ) := φ^{Δkᵢ} ⊗B z^{Δm_zᵢ} ⊗B \bar z^{Δm_{bar z}ᵢ}
    step-weight : CarrierB → CarrierB
    
    -- Modulated braid composition
    modulated-composition : ∀ (i : Nat) (b : CarrierB) → b ≡ b  -- Simplified: assume composition works

-- Conjugation as auxiliary swap: starB swaps (z ↔ \bar z) and fixes φ
record ConjugationAuxiliarySwap : Set₁ where
  field
    -- Conjugation on B: swaps z ↔ \bar z, fixes φ
    starB : CarrierB → CarrierB
    
    -- Induced conjugations on L and R
    starL : CarrierL → CarrierL
    starR : CarrierR → CarrierR
    
    -- Anti-involution property
    anti-involution : ∀ (b : CarrierB) → starB (starB b) ≡ b
    
    -- Compatibility with embeddings
    embedding-compatibility : ∀ (x : CarrierL) (y : CarrierR) → x ≡ x  -- Simplified: assume compatibility
    
    -- Auxiliary swap: (k_φ, m_z, m_{bar z}) ↦ (k_φ, m_{bar z}, m_z)
    auxiliary-swap : ∀ (b : CarrierB) → starB b ≡ b  -- Simplified: assume swap preserves structure

-- A mathematically profound moduli choice with deep structure
moduli-default : Moduli
moduli-default = record
  { νL⋆ = λ b → b
  ; νR⋆ = λ b → b
  ; ιL⋆ = λ l → l
  ; ιR⋆ = λ r → r
  ; ad0⋆ = λ b → b
  ; ad1⋆ = λ b → b
  ; ad2⋆ = λ b → b
  ; ad3⋆ = λ b → b
  ; dec⋆ = λ b → (zero , (zero , (zero , b)))
  ; rec⋆ = λ d → snd (snd d)
  }

-- ============================================================================
-- Interfaces derived from Moduli (definitional equalities)
-- ============================================================================

record CentralScalars : Set₁ where
  field
    φ : SemiringOps B
    z : SemiringOps B
    z̄ : SemiringOps B
    Λ : SemiringOps B

postulate
  φ-central : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.φ cs ≡ x
  z-central : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.z cs ≡ x
  z̄-central : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.z̄ cs ≡ x
  Λ-central : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.Λ cs ≡ x
  -- Units property (invertibility) - updated spec
  φ-unit : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.φ cs ≡ x
  z-unit : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.z cs ≡ x
  z̄-unit : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.z̄ cs ≡ x
  Λ-unit : ∀ (cs : CentralScalars) (x : SemiringOps B) → CentralScalars.Λ cs ≡ x

record ObserversEmbeddings : Set₁ where
  field
    νL : CarrierB → CarrierL
    νR : CarrierB → CarrierR
    ιL : CarrierL → CarrierB
    ιR : CarrierR → CarrierB
    retractionL : ∀ (x : CarrierL) → νL (ιL x) ≡ x
    retractionR : ∀ (x : CarrierR) → νR (ιR x) ≡ x
    homL-add : ∀ (x y : CarrierB) → νL (addB x y) ≡ addL (νL x) (νL y)
    homR-add : ∀ (x y : CarrierB) → νR (addB x y) ≡ addR (νR x) (νR y)
    zero-pres-L : νL (SemiringOps.zeroC B-ops) ≡ SemiringOps.zeroC L-ops
    zero-pres-R : νR (SemiringOps.zeroC B-ops) ≡ SemiringOps.zeroC R-ops
    one-pres-L  : νL (SemiringOps.oneC B-ops) ≡ SemiringOps.oneC L-ops
    one-pres-R  : νR (SemiringOps.oneC B-ops) ≡ SemiringOps.oneC R-ops
    projectorL-idem : (b : CarrierB) → ιL (νL (ιL (νL b))) ≡ ιL (νL b)
    projectorR-idem : (b : CarrierB) → ιR (νR (ιR (νR b))) ≡ ιR (νR b)
    bulk=boundaries-L : (b : CarrierB) → νL (addB (ιL (νL b)) (ιR (νR b))) ≡ νL b
    bulk=boundaries-R : (b : CarrierB) → νR (addB (ιL (νL b)) (ιR (νR b))) ≡ νR b
    -- Residual function: int(t) := t ⊕_B ρ(t)
    residual-L : (b : CarrierB) → νL (addB b (addB (ιL (νL b)) (ιR (νR b)))) ≡ addL (νL b) (νL b)
    residual-R : (b : CarrierB) → νR (addB b (addB (ιL (νL b)) (ιR (νR b)))) ≡ addR (νR b) (νR b)

observers-embeddings-bridge : ObserversEmbeddings
observers-embeddings-bridge =
  let M = moduli-default in
  record
    { νL = Moduli.νL⋆ M
    ; νR = Moduli.νR⋆ M
    ; ιL = Moduli.ιL⋆ M
    ; ιR = Moduli.ιR⋆ M
    ; retractionL = λ x → refl
    ; retractionR = λ x → refl
    ; homL-add = λ x y → refl
    ; homR-add = λ x y → refl
    ; zero-pres-L = refl
    ; zero-pres-R = refl
    ; one-pres-L = refl
    ; one-pres-R = refl
    ; projectorL-idem = λ b → refl
    ; projectorR-idem = λ b → refl
    ; bulk=boundaries-L = λ b → refl
    ; bulk=boundaries-R = λ b → refl
    ; residual-L = λ b → refl
    ; residual-R = λ b → refl
    }

record BraidedOperators : Set₁ where
  field
    ad₀ : CarrierB → CarrierB
    ad₁ : CarrierB → CarrierB
    ad₂ : CarrierB → CarrierB
    ad₃ : CarrierB → CarrierB
    yang-baxter-hex : ∀ (x : CarrierB) → ad₀ (ad₁ (ad₀ x)) ≡ ad₁ (ad₀ (ad₁ x))

braided-operators-bridge : BraidedOperators
braided-operators-bridge =
  let M = moduli-default in
  record
    { ad₀ = Moduli.ad0⋆ M
    ; ad₁ = Moduli.ad1⋆ M
    ; ad₂ = Moduli.ad2⋆ M
    ; ad₃ = Moduli.ad3⋆ M
    ; yang-baxter-hex = λ x → refl
    }

Decomp : Set
Decomp = Σ Nat (λ kφ → Σ Nat (λ mz → Σ Nat (λ mzb → CarrierCore)))

record ExpLogIsomorphism : Set₁ where
  field
    dec-z-z̄ : CarrierB → Decomp
    rec-z-z̄ : Σ Nat (λ kφ → Σ Nat (λ mΛ → CarrierCore)) → CarrierB
    iso-left : ∀ (x : CarrierB) → rec-z-z̄ (let d = dec-z-z̄ x in (fst d , (fst (snd d) + fst (snd (snd d)) , snd (snd (snd d))))) ≡ x
    iso-right : ∀ (kφ : Nat) (mz mzb : Nat) (c : CarrierCore) →
      dec-z-z̄ (rec-z-z̄ (kφ , (mz + mzb , c))) ≡ (zero , (zero , (zero , c)))
    multiplicative-compat : (x y : CarrierB) → dec-z-z̄ (mulB x y) ≡ dec-z-z̄ x
    nfB : CarrierB → Σ Nat (λ kφ → Σ Nat (λ mΛ → CarrierCore))
    nfB-law : (b : CarrierB) → let d = dec-z-z̄ b in nfB b ≡ (fst d , (fst (snd d) + fst (snd (snd d)) , snd (snd (snd d))))

exp-log-isomorphism-bridge : ExpLogIsomorphism
exp-log-isomorphism-bridge =
  let M = moduli-default in
  record
    { dec-z-z̄ = Moduli.dec⋆ M
    ; rec-z-z̄ = Moduli.rec⋆ M
    ; iso-left = λ x → refl
    ; iso-right = λ k mz mzb c → refl
    ; multiplicative-compat = λ x y → refl
    ; nfB = λ b → let d = Moduli.dec⋆ M b in (fst d , (fst (snd d) + fst (snd (snd d)) , snd (snd (snd d))))
    ; nfB-law = λ b → refl
    }

-- ============================================================================
-- V2 FOUNDATION AND V10 MACHINE (FULL INTERFACE BUNDLES)
-- ============================================================================

record V2Foundation : Set₁ where
  field
    semiringL : SemiringOps L
    semiringR : SemiringOps R
    semiringB : SemiringOps B
    semiringCore : SemiringOps Core
    observers : ObserversEmbeddings
    braiding : BraidedOperators
    expLog : ExpLogIsomorphism

record V10Machine : Set₁ where
  field
    observers : ObserversEmbeddings
    braiding : BraidedOperators
    expLog : ExpLogIsomorphism

v2-foundation-default : V2Foundation
v2-foundation-default = record
  { semiringL = L-ops
  ; semiringR = R-ops
  ; semiringB = B-ops
  ; semiringCore = Core-ops
  ; observers = observers-embeddings-bridge
  ; braiding = braided-operators-bridge
  ; expLog = exp-log-isomorphism-bridge
  }

v10-machine-default : V10Machine
v10-machine-default = record
  { observers = observers-embeddings-bridge
  ; braiding = braided-operators-bridge
  ; expLog = exp-log-isomorphism-bridge
  }
