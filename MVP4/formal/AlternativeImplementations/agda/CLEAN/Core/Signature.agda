module CLEAN.Core.Signature where

open import Agda.Primitive using (Level; lsuc; lzero)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

open import CLEAN.Core.Sorts

record OpData : Set where
  constructor op
  field
    tag      : String
    inArity  : Nat
    outArity : Nat
    inputs   : Vec Sort inArity
    outputs  : Vec Sort outArity

open OpData public

data OpId : Set where
  ιL ιR νL νR : OpId
  BulkSum     : OpId
  Ad₀ Ad₁ Ad₂ Ad₃ : OpId
  Gaugeφ Gaugeφ̄ Gaugez Gaugez̄ GaugeΛ : OpId
  Basepoint₀ Basepoint₁ Basepoint₂ Basepoint₃ : OpId
  Gen₄ : OpId
  TrialityL TrialityR TrialityB : OpId
  ConjB ConjL ConjR : OpId
  CopyB : OpId
  EraseB : OpId
  TensorL GuardNeg GuardNAND : OpId
  BraidBB DeltaB CumulantB : OpId

record Signature : Set₁ where
  constructor mkΣ
  field
    Operation : Set
    dataOf    : Operation → OpData

open Signature public

Σ₁₀ : Signature
Σ₁₀ = mkΣ OpId opData where
  opData : OpId → OpData
  opData ιL = op "iotaL" 1 1 (L ∷ []) (B ∷ [])
  opData ιR = op "iotaR" 1 1 (R ∷ []) (B ∷ [])
  opData νL = op "nuL" 1 1 (B ∷ []) (L ∷ [])
  opData νR = op "nuR" 1 1 (B ∷ []) (R ∷ [])
  opData BulkSum = op "bulkSum" 2 1 (B ∷ (B ∷ [])) (B ∷ [])
  opData Ad₀ = op "ad0" 1 1 (B ∷ []) (B ∷ [])
  opData Ad₁ = op "ad1" 1 1 (B ∷ []) (B ∷ [])
  opData Ad₂ = op "ad2" 1 1 (B ∷ []) (B ∷ [])
  opData Ad₃ = op "ad3" 1 1 (B ∷ []) (B ∷ [])
  opData Gaugeφ = op "phi" 1 1 (I ∷ []) (B ∷ [])
  opData Gaugeφ̄ = op "phiBar" 1 1 (I ∷ []) (B ∷ [])
  opData Gaugez = op "z" 1 1 (I ∷ []) (B ∷ [])
  opData Gaugez̄ = op "zBar" 1 1 (I ∷ []) (B ∷ [])
  opData GaugeΛ = op "Lambda" 1 1 (I ∷ []) (B ∷ [])
  opData Basepoint₀ = op "a0" 1 1 (I ∷ []) (B ∷ [])
  opData Basepoint₁ = op "a1" 1 1 (I ∷ []) (B ∷ [])
  opData Basepoint₂ = op "a2" 1 1 (I ∷ []) (B ∷ [])
  opData Basepoint₃ = op "a3" 1 1 (I ∷ []) (B ∷ [])
  opData Gen₄ = op "Gen4" 4 1 (B ∷ (B ∷ (B ∷ (B ∷ [])))) (B ∷ [])
  opData TrialityL = op "T_L" 1 1 (B ∷ []) (L ∷ [])
  opData TrialityR = op "T_R" 1 1 (B ∷ []) (R ∷ [])
  opData TrialityB = op "T_B" 2 1 (L ∷ (R ∷ [])) (B ∷ [])
  opData ConjB = op "starB" 1 1 (B ∷ []) (B ∷ [])
  opData ConjL = op "starL" 1 1 (L ∷ []) (L ∷ [])
  opData ConjR = op "starR" 1 1 (R ∷ []) (R ∷ [])
  opData CopyB = op "copyB" 1 2 (B ∷ []) (B ∷ (B ∷ []))
  opData EraseB = op "eraseB" 1 1 (B ∷ []) (I ∷ [])
  opData TensorL = op "tensorL" 2 1 (L ∷ (L ∷ [])) (L ∷ [])
  opData GuardNeg = op "guardNeg" 2 1 (L ∷ (L ∷ [])) (L ∷ [])
  opData GuardNAND = op "guardNAND" 3 1 (L ∷ (L ∷ (L ∷ []))) (L ∷ [])
  opData BraidBB = op "braidBB" 2 2 (B ∷ (B ∷ [])) (B ∷ (B ∷ []))
  opData DeltaB = op "deltaB" 1 1 (B ∷ []) (B ∷ [])
  opData CumulantB = op "cumulantB" 1 1 (B ∷ []) (B ∷ [])

open Signature Σ₁₀ public renaming (dataOf to data₁₀)

inputsOf : (opId : OpId) → Vec Sort (inArity (data₁₀ opId))
inputsOf opId = inputs (data₁₀ opId)

outputsOf : (opId : OpId) → Vec Sort (outArity (data₁₀ opId))
outputsOf opId = outputs (data₁₀ opId)
