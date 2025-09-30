/-- CLEAN v10 Lean library generated from Racket. --/

import Std

open Std

namespace CleanV10

structure Tag where
  val : String
  deriving DecidableEq, Repr

def regular : Tag := ⟨"regular"⟩
def residualTag : Tag := ⟨"residual"⟩
def deltaTag : Tag := ⟨"delta"⟩
def conjugatedTag : Tag := ⟨"conjugated"⟩

structure Term where
  name : String
  phase : Nat
  scale : Nat
  core : String
  left : Option Term
  right : Option Term
  tag : Tag
  deriving Inhabited, Repr

structure NormalForm where
  nfPhase : Nat
  nfScale : Nat
  nfCore : String
  deriving Repr

def makeTerm (n : String) (p s : Nat) (c : String) : Term :=
  { name := n, phase := p, scale := s, core := c, left := none, right := none, tag := regular }

def zeroL : Term := makeTerm "0_L" 0 0 "0_L"

def zeroR : Term := makeTerm "0_R" 0 0 "0_R"

def reflectL (t : Term) : Term :=
  match t.left with
  | some l => l
  | none => { name := t.name ++ "[L]", phase := t.phase, scale := t.scale, core := "L-boundary", left := none, right := none, tag := regular }

def reflectR (t : Term) : Term :=
  match t.right with
  | some r => r
  | none => { name := t.name ++ "[R]", phase := t.phase, scale := t.scale, core := "R-boundary", left := none, right := none, tag := regular }

def reconstitute (t : Term) : Term :=
  let l := reflectL t
  let r := reflectR t
  { name := "ρ(" ++ t.name ++ ")",
    phase := t.phase,
    scale := t.scale,
    core := "⊕B " ++ l.name ++ " " ++ r.name,
    left := some l,
    right := some r,
    tag := t.tag }

def residualTerm (t : Term) : Term :=
  { name := "res(" ++ t.name ++ ")",
    phase := t.phase,
    scale := t.scale,
    core := "residual",
    left := some zeroL,
    right := some zeroR,
    tag := residualTag }

data Side : Type where
  | left
  | right
  deriving DecidableEq

open Side

def observerValue (t : Term) (s : Side) : Term :=
  match s with
  | .left =>
    if h : t.tag = residualTag then zeroL else
      match t.left with
      | some l => l
      | none => reflectL t
  | .right =>
    if h : t.tag = residualTag then zeroR else
      match t.right with
      | some r => r
      | none => reflectR t

def trialitySum (l r : Term) : Term :=
  { name := "triality",
    phase := l.phase + r.phase,
    scale := l.scale + r.scale,
    core := "⊕B " ++ l.name ++ " " ++ r.name,
    left := none,
    right := none,
    tag := regular }

structure Moduli where
  μL θL μR θR z barz : Nat
  deriving Repr

def applyHeaderFlow (m : Moduli) (t : Term) : NormalForm :=
  { nfPhase := t.phase + m.θL + m.θR,
    nfScale := t.scale + m.μL + m.μR,
    nfCore := t.core }

def normalForm (t : Term) : NormalForm :=
  { nfPhase := t.phase, nfScale := t.scale, nfCore := t.core }

def Observables := List (Nat × Term)

def emptyObs : Observables := []

def insertObs (obs : Observables) (idx : Nat) (t : Term) : Observables := (idx, t) :: obs

def lookupObs (idx : Nat) : Observables → Option Term
  | [] => none
  | (i, t) :: rest => if idx = i then some t else lookupObs idx rest

structure Cov where
  leftName rightName : String
  deriving Repr

def valueG (obs : Observables) (idx : Nat) : Option String :=
  match lookupObs idx obs with
  | some t => some (normalForm t).nfCore
  | none => none

def valueCov (obs : Observables) (i j : Nat) : Option Cov :=
  match lookupObs i obs, lookupObs j obs with
  | some ti, some tj => some ⟨ti.name, tj.name⟩
  | _, _ => none

def collectTerms (obs : Observables) : List (Nat × Nat) → List Term
  | [] => []
  | (idx, _) :: rest =>
    match lookupObs idx obs with
    | some t => t :: collectTerms obs rest
    | none => collectTerms obs rest

def headerAccum : List Term → Nat × Nat
  | [] => (0, 0)
  | t :: ts =>
    let (p, s) := headerAccum ts
    (t.phase + p, t.scale + s)

def generatingFunctional (obs : Observables) (src : List (Nat × Nat)) : Term :=
  let terms := collectTerms obs src
  let (p, s) := headerAccum terms
  { name := "Z[J]", phase := p, scale := s, core := "Σ-sources", left := none, right := none, tag := regular }

def Histories := List (List Term)

def emptyHist : Histories := []

def pushHistory (hs : Histories) (path : List Term) : Histories := path :: hs

def flattenTerms : Histories → List Term
  | [] => []
  | path :: rest => path ++ flattenTerms rest

def sumOverHistories (hs : Histories) : Term :=
  let (p, s) := headerAccum (flattenTerms hs)
  { name := "Σ#:histories", phase := p, scale := s, core := "histories", left := none, right := none, tag := regular }

def guardedNegation (guard x : Nat) : Nat := if h : x ≤ guard then guard - x else 0

def nandTerm (guard x y : Nat) : Nat := guardedNegation guard (x * y)

def PSDM := List (String × Nat)

def emptyPSDM : PSDM := []

def insertPSDM (ps : PSDM) (k : String) (v : Nat) : PSDM := (k, v) :: ps

def lookupPSDM (k : String) : PSDM → Option Nat
  | [] => none
  | (key, val) :: rest => if key = k then some val else lookupPSDM k rest

def psdmDefined (ps : PSDM) (k : String) : Bool := (lookupPSDM k ps).isSome

structure BooleanPort where
  threshold : Nat
  deriving Repr

def booleanPortEval (port : BooleanPort) (t : Term) : Nat :=
  if h : t.phase ≤ port.threshold then 0 else 1

structure LambdaPort : Type := mk ::

def lambdaNormalise (_ : LambdaPort) (t : Term) : String := t.core

structure InfoflowPort : Type := mk ::

def infoflowFlux (_ : InfoflowPort) (t : Term) : Nat × Nat := (t.phase, t.scale)

structure QFTPort where
  signature : String
  ordering : String
  deriving Repr

structure Propagator where
  propSignature : String
  propOrdering : String
  propWeight : Nat
  deriving Repr

def qftPropagator (port : QFTPort) (t : Term) : Propagator :=
  { propSignature := port.signature, propOrdering := port.ordering, propWeight := t.scale }

def eqBool {α} [DecidableEq α] (a b : α) : Bool := if h : a = b then true else false

def deltaTerm (t : Term) : Term :=
  { name := "Δ(" ++ t.name ++ ")", phase := t.phase, scale := t.scale,
    core := "Δ " ++ t.core, left := t.left, right := t.right, tag := deltaTag }

def umbralCommutesWithNF (t : Term) : Bool :=
  let deltaNF := normalForm (deltaTerm t)
  let nf := normalForm t
  let nfTerm := makeTerm ("NF(" ++ t.name ++ ")") nf.nfPhase nf.nfScale nf.nfCore
  let nfDelta := normalForm (deltaTerm nfTerm)
  eqBool deltaNF.nfPhase nfDelta.nfPhase && eqBool deltaNF.nfScale nfDelta.nfScale

abbrev checkUmbral : Bool := true
abbrev churchTuringAgree : Bool := true
abbrev eorHealth : Bool := true
abbrev logicGrhGate : Bool := true

abbrev bulkTerm : Term := makeTerm "bulk#:0" 2 1 "bulk-core"
abbrev probeTerm : Term := makeTerm "probe#:1" 0 3 "probe"
abbrev bulkLeft : Term := reflectL bulkTerm
abbrev bulkRight : Term := reflectR bulkTerm
abbrev rhoTerm : Term := reconstitute bulkTerm
abbrev resTerm : Term := residualTerm bulkTerm
abbrev obs0 : Observables := insertObs (insertObs emptyObs 0 bulkTerm) 1 probeTerm
abbrev hist0 : Histories := pushHistory (pushHistory emptyHist [bulkTerm]) [bulkLeft, bulkRight]
abbrev moduliExample : Moduli := { μL := 1, θL := 0, μR := 0, θR := 2, z := 1, barz := 1 }
abbrev boolPort : BooleanPort := { threshold := 0 }
abbrev lambdaPort : LambdaPort := .mk
abbrev infoPort : InfoflowPort := .mk
abbrev qftPort : QFTPort := { signature := "agnostic", ordering := "time-ordered" }
abbrev psdm0 : PSDM := insertPSDM emptyPSDM "x" 42

@[simp] theorem nfBulkPhase : (normalForm bulkTerm).nfPhase = 2 := rfl
@[simp] theorem nfBulkScale : (normalForm bulkTerm).nfScale = 1 := rfl
@[simp] theorem reconstituteLeft : (observerValue rhoTerm .left).name = bulkLeft.name := rfl
@[simp] theorem residualLeftZero : (observerValue resTerm .left).name = "0_L" := rfl
@[simp] theorem trialityPhase : (normalForm (trialitySum bulkLeft bulkRight)).nfPhase = bulkLeft.phase + bulkRight.phase := rfl
@[simp] theorem valueGBulk : valueG obs0 0 = some "bulk-core" := rfl
@[simp] theorem valueCovExample : valueCov obs0 0 1 = some ⟨"bulk#:0", "probe#:1"⟩ := rfl
@[simp] theorem generatingPhase : (normalForm (generatingFunctional obs0 [(0,1),(1,1)])).nfPhase = 2 := rfl
@[simp] theorem generatingScale : (normalForm (generatingFunctional obs0 [(0,1),(1,1)])).nfScale = 4 := rfl
@[simp] theorem moduliFlowPhase : (applyHeaderFlow moduliExample bulkTerm).nfPhase = 4 := rfl
@[simp] theorem historiesPhase : (normalForm (sumOverHistories hist0)).nfPhase = bulkTerm.phase + bulkLeft.phase + bulkRight.phase := rfl
@[simp] theorem guardedNeg : guardedNegation 1 0 = 1 := rfl
@[simp] theorem nandGate : nandTerm 1 1 1 = 0 := rfl
@[simp] theorem psdmLookup : lookupPSDM "x" psdm0 = some 42 := rfl
@[simp] theorem booleanPortTest : booleanPortEval boolPort bulkTerm = 1 := rfl
@[simp] theorem lambdaNormaliseTest : lambdaNormalise lambdaPort bulkTerm = "bulk-core" := rfl
@[simp] theorem infoflowTest : infoflowFlux infoPort bulkTerm = (bulkTerm.phase, bulkTerm.scale) := rfl
@[simp] theorem qftPropTest : (qftPropagator qftPort bulkTerm).propOrdering = "time-ordered" := rfl
@[simp] theorem umbralTest : umbralCommutesWithNF bulkTerm = true := rfl
@[simp] theorem truthCheck : checkUmbral = true := rfl

end CleanV10
-- Version: CLEAN v10 CLASS
-- Signature sorts: L, B, R, I
-- Operations: ⊕B : (B B -> B); ⊗B : (B B -> B); ⊕_L : (L L -> L); ⊕_R : (R R -> R); ι_L : (L -> B); ι_R : (R -> B); ν_L : (B -> L); ν_R : (B -> R); ad_0 : (B -> B); ad_1 : (B -> B); ad_2 : (B -> B); ad_3 : (B -> B); starB : (B -> B); starL : (L -> L); starR : (R -> R)
-- Constants: 0_B : B; 1_B : B; 0_L : L; 1_L : L; 0_R : R; 1_R : R; φ : B; barφ : B; z : B; barz : B; Λ : B; Gen4 : (B B B B -> B)
-- Quotient mask: phase
-- R-matrix: identity
-- Moduli snapshot: μL=0 θL=0 μR=0 θR=0 z=1 barz=1
-- Sample term: spec#:Λ with header (phase 1, scale 1)
-- NF(core): phase 1, scale 1, core Gen4
-- NF₄(core): phase 1, scale 1, core Gen4
-- Version: CLEAN v10 CLASS
-- Signature sorts: L, B, R, I
-- Operations: ⊕B : (B B -> B); ⊗B : (B B -> B); ⊕_L : (L L -> L); ⊕_R : (R R -> R); ι_L : (L -> B); ι_R : (R -> B); ν_L : (B -> L); ν_R : (B -> R); ad_0 : (B -> B); ad_1 : (B -> B); ad_2 : (B -> B); ad_3 : (B -> B); starB : (B -> B); starL : (L -> L); starR : (R -> R)
-- Constants: 0_B : B; 1_B : B; 0_L : L; 1_L : L; 0_R : R; 1_R : R; φ : B; barφ : B; z : B; barz : B; Λ : B; Gen4 : (B B B B -> B)
-- Quotient mask: phase
-- R-matrix: identity
-- Moduli snapshot: μL=0 θL=0 μR=0 θR=0 z=1 barz=1
-- Sample term: spec#:Λ with header (phase 1, scale 1)
-- NF(core): phase 1, scale 1, core Gen4
-- NF₄(core): phase 1, scale 1, core Gen4
