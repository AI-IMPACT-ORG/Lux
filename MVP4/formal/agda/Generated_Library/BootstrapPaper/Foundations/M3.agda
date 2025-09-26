module Generated_Library.BootstrapPaper.Foundations.M3 where

-- Auto-generated from lt-core host bundle
-- μ₁ = 1
-- μ₂ = 2
-- μ₃ = 3
-- μ₄ = 4
-- μ₁★ = 1
-- μ₂★ = 2
-- μ₃★ = 3
-- μ₄★ = 4
-- λ = 1
-- λ★ = 1

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.List.Base using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Register : Set where
  InputReg : Register
  OutputReg : Register
  PortReg : Register

data EdgeKind : Set where
  Sigma6 : EdgeKind
  Tensor : EdgeKind
  Wire : EdgeKind

record Arity : Set where
  field
    inputs  : ℕ
    outputs : ℕ

arityOf : EdgeKind → Arity
arityOf Sigma6 = record { inputs = 3 ; outputs = 3 }
arityOf Tensor = record { inputs = 2 ; outputs = 2 }
arityOf Wire = record { inputs = 2 ; outputs = 2 }

srcOf : EdgeKind → List Register
srcOf Sigma6 = PortReg ∷ PortReg ∷ PortReg ∷ []
srcOf Tensor = PortReg ∷ PortReg ∷ []
srcOf Wire = InputReg ∷ OutputReg ∷ []

dstOf : EdgeKind → List Register
dstOf Sigma6 = PortReg ∷ PortReg ∷ PortReg ∷ []
dstOf Tensor = PortReg ∷ PortReg ∷ []
dstOf Wire = OutputReg ∷ InputReg ∷ []

record TypeGraph : Set where
  field
    registers : List Register
    edgeKinds : List EdgeKind
    arityMap  : EdgeKind → Arity
    srcMap    : EdgeKind → List Register
    dstMap    : EdgeKind → List Register

sampleGraph : TypeGraph
sampleGraph = record { registers = InputReg ∷ OutputReg ∷ PortReg ∷ []
, edgeKinds = Sigma6 ∷ Tensor ∷ Wire ∷ []
, arityMap  = arityOf
, srcMap    = srcOf
, dstMap    = dstOf
}

register-count≡3 : length (TypeGraph.registers sampleGraph) ≡ 3
register-count≡3 = refl

edge-count≡3 : length (TypeGraph.edgeKinds sampleGraph) ≡ 3
edge-count≡3 = refl

src-length-sigma6 : length (srcOf Sigma6) ≡ 3
src-length-sigma6 = refl
src-length-tensor : length (srcOf Tensor) ≡ 2
src-length-tensor = refl
src-length-wire : length (srcOf Wire) ≡ 2
src-length-wire = refl

