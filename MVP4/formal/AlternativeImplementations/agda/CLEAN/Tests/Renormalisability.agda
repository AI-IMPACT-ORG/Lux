module CLEAN.Tests.Renormalisability where

open import CLEAN.Library
open import CLEAN.Core.Renormalisability

open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Nat renaming (zero to zeroℕ; suc to sucℕ)

-- | CLEAN's rule family satisfies the renormalisation witness requirements.
renormalisable-clean : Renormalisable ruleFamily
renormalisable-clean = cleanRenormalisableFamily

sampleHeader : Header
sampleHeader = mkHeader (signed plus zeroℕ) (signed plus zeroℕ) zeroℕ zeroℕ

sampleNF : NormalForm ⊤
sampleNF = mkNF sampleHeader tt

-- | Example PSDM renormalisation bundle for a neutral normal form.
renormalisable-psdm : PSDMRenormalisation sampleNF
renormalisable-psdm = defaultPSDMRenormalisation sampleNF
