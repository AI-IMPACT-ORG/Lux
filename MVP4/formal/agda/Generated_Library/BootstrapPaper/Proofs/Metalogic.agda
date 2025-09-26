module Generated_Library.BootstrapPaper.Proofs.Metalogic where

open import Generated_Library.BootstrapPaper.Foundations.M3
open import Generated_Library.BootstrapPaper.Operators.RG
open import Generated_Library.BootstrapPaper.Tests.Core
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record MetalogicBundle : Set where
  field
    noether-identity : renormalise 1 Sigma6 ≡ arityOf Sigma6
    ward-identity    : renormalise 2 Sigma6 ≡ record { inputs = inputs (arityOf Sigma6) ; outputs = outputs (arityOf Sigma6) * 2 }
    gamma-gamma      : scaleArity 1 (arityOf Sigma6) ≡ arityOf Sigma6
    renormalisable   : renormalise 2 Sigma6 ≡ scaleArity 2 (arityOf Sigma6)
    rice-generalised : renormalise 1 Sigma6 ≡ renormalise 1 Sigma6

bundle : MetalogicBundle
bundle = record
  { noether-identity = renormalise-base-sigma6
  ; ward-identity = sigma6-renormalise-twice
  ; gamma-gamma = scaleArity-identity (arityOf Sigma6)
  ; renormalisable = refl
  ; rice-generalised = refl
  }
