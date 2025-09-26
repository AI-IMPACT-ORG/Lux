module Generated_Library.BootstrapPaper.Proofs.MultiLogic where

open import Generated_Library.BootstrapPaper.Foundations.M3
open import Generated_Library.BootstrapPaper.Operators.RG
open import Generated_Library.BootstrapPaper.Tests.Core
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record MultiLogicBundle : Set where
  field
    graph          : TypeGraph
    registers-ok  : length (TypeGraph.registers graph) ≡ 3
    edges-ok      : length (TypeGraph.edgeKinds graph) ≡ 3
    sigma6-base   : renormalise 1 Sigma6 ≡ arityOf Sigma6
    sigma6-double : renormalise 2 Sigma6 ≡ record { inputs = inputs (arityOf Sigma6) ; outputs = outputs (arityOf Sigma6) * 2 }

bundle : MultiLogicBundle
bundle = record
  { graph = sampleGraph
  ; registers-ok = register-count≡3
  ; edges-ok = edge-count≡3
  ; sigma6-base = renormalise-base-sigma6
  ; sigma6-double = sigma6-renormalise-twice
  }
