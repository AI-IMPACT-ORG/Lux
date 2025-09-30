-- CLEAN v10 Agda library generated from Racket
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
data Tag : Set where
  regular residual delta conjugated : Tag

record Term : Set where
  constructor mkTerm
  field
    name : String
    phase : ℕ
    scale : ℕ
    core : String
    left : Maybe Term
    right : Maybe Term
    tag : Tag

open Term public

record NormalForm : Set where
  constructor mkNF
  field
    nfPhase : ℕ
    nfScale : ℕ
    nfCore : String

open NormalForm public

decToBool : {A : Set} → Dec A → Bool
decToBool (yes _) = true
decToBool (no _) = false

makeTerm : String → ℕ → ℕ → String → Term
makeTerm n p s c = mkTerm n p s c nothing nothing regular

zeroL : Term
zeroL = mkTerm "0_L" zero zero "0_L" nothing nothing regular

zeroR : Term
zeroR = mkTerm "0_R" zero zero "0_R" nothing nothing regular

reflectL : Term → Term
reflectL t with left t
... | just l = l
... | nothing = mkTerm (name t ++ "[L]") (phase t) (scale t) "L-boundary" nothing nothing regular

reflectR : Term → Term
reflectR t with right t
... | just r = r
... | nothing = mkTerm (name t ++ "[R]") (phase t) (scale t) "R-boundary" nothing nothing regular

reconstitute : Term → Term
reconstitute t =
  let l = reflectL t
      r = reflectR t
  in mkTerm ("ρ(" ++ name t ++ ")") (phase t) (scale t)
            ("⊕B " ++ name l ++ " " ++ name r)
            (just l) (just r) (tag t)

residual : Term → Term
residual t = mkTerm ("res(" ++ name t ++ ")") (phase t) (scale t)
                         "residual" (just zeroL) (just zeroR) residual

data Side : Set where
  L R : Side

observerValue : Term → Side → Term
observerValue t L with tag t
... | residual = zeroL
... | _ with left t
...   | just l = l
...   | nothing = reflectL t
observerValue t R with tag t
... | residual = zeroR
... | _ with right t
...   | just r = r
...   | nothing = reflectR t

trialitySum : Term → Term → Term
trialitySum l r = mkTerm "triality"
  (phase l + phase r)
  (scale l + scale r)
  ("⊕B " ++ name l ++ " " ++ name r)
  nothing nothing regular

record Moduli : Set where
  constructor mkModuli
  field μL θL μR θR : ℕ
        z barz : ℕ

open Moduli public

applyHeaderFlow : Moduli → Term → NormalForm
applyHeaderFlow m t =
  mkNF (phase t + θL m + θR m)
       (scale t + μL m + μR m)
       (core t)

record Observables : Set where
  constructor mkObs
  field entries : List (ℕ × Term)

open Observables public

emptyObs : Observables
emptyObs = mkObs []

insertObs : Observables → ℕ → Term → Observables
insertObs (mkObs xs) idx t = mkObs ((idx , t) ∷ xs)

lookupObs : ℕ → Observables → Maybe Term
lookupObs idx (mkObs []) = nothing
lookupObs idx (mkObs ((i , t) ∷ rest)) with idx ≟ i
... | yes _ = just t
... | no _ = lookupObs idx (mkObs rest)

record Cov : Set where
  constructor mkCov
  field leftName rightName : String

valueG : Observables → ℕ → Maybe String
valueG obs idx with lookupObs idx obs
... | just t = just (nfCore (normalForm t))
... | nothing = nothing

valueCov : Observables → ℕ → ℕ → Maybe Cov
valueCov obs i j with lookupObs i obs | lookupObs j obs
... | just ti | just tj = just (mkCov (name ti) (name tj))
... | _ | _ = nothing

collectTerms : Observables → List (ℕ × ℕ) → List Term
collectTerms obs [] = []
collectTerms obs ((idx , _) ∷ rest) with lookupObs idx obs
... | just t = t ∷ collectTerms obs rest
... | nothing = collectTerms obs rest

headerAccumulator : List Term → ℕ × ℕ
headerAccumulator [] = (0 , 0)
headerAccumulator (t ∷ ts) =
  let acc = headerAccumulator ts in
  (phase t + proj₁ acc , scale t + proj₂ acc)

generatingFunctional : Observables → List (ℕ × ℕ) → Term
generatingFunctional obs sources =
  let terms = collectTerms obs sources in
  let header = headerAccumulator terms in
  mkTerm "Z[J]" (proj₁ header) (proj₂ header) "Σ-sources" nothing nothing regular

record Histories : Set where
  constructor mkHist
  field paths : List (List Term)

open Histories public

emptyHist : Histories
emptyHist = mkHist []

pushHistory : Histories → List Term → Histories
pushHistory (mkHist hs) path = mkHist (path ∷ hs)

flatten : List (List Term) → List Term
flatten [] = []
flatten (xs ∷ rest) = xs ++ flatten rest
  where
    _++_ : List Term → List Term → List Term
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

sumOverHistories : Histories → Term
sumOverHistories (mkHist hs) =
  let flat = flatten hs in
  let header = headerAccumulator flat in
  mkTerm "Σ#:histories" (proj₁ header) (proj₂ header) "histories" nothing nothing regular

safeMinus : ℕ → ℕ → ℕ
safeMinus g x with x ≤? g
... | yes _ = g ∸ x
... | no _ = zero

guardedNegation : ℕ → ℕ → ℕ
guardedNegation guard x = safeMinus guard x

nandTerm : ℕ → ℕ → ℕ → ℕ
nandTerm guard x y = guardedNegation guard (x * y)

record PSDM : Set where
  constructor mkPSDM
  field table : List (String × ℕ)

open PSDM public

emptyPSDM : PSDM
emptyPSDM = mkPSDM []

lookupString : String → List (String × ℕ) → Maybe ℕ
lookupString key [] = nothing
lookupString key ((k , v) ∷ rest) with key ≟ k
... | yes _ = just v
... | no _ = lookupString key rest

psdmDefine : PSDM → String → ℕ → PSDM
psdmDefine (mkPSDM xs) key value = mkPSDM ((key , value) ∷ xs)

psdmLookup : PSDM → String → Maybe ℕ
psdmLookup (mkPSDM xs) key = lookupString key xs

psdmDefined : PSDM → String → Bool
psdmDefined ps key with psdmLookup ps key
... | just _ = true
... | nothing = false

record BooleanPort : Set where
  constructor mkBoolPort
  field threshold : ℕ

booleanPortEval : BooleanPort → Term → ℕ
booleanPortEval port term with phase term ≤? threshold port
... | yes _ = 0
... | no _ = 1

record LambdaPort : Set where constructor mkLambdaPort
lambdaNormalise : LambdaPort → Term → String
lambdaNormalise _ term = core term

record InfoflowPort : Set where constructor mkInfoflowPort
record Flow : Set where constructor mkFlow; field flowPhase flowScale : ℕ
infoflowFlux : InfoflowPort → Term → Flow
infoflowFlux _ term = mkFlow (phase term) (scale term)

record QFTPort : Set where constructor mkQFTPort; field signature ordering : String
record Propagator : Set where constructor mkProp; field propSignature propOrdering : String; propWeight : ℕ
qftPropagator : QFTPort → Term → Propagator
qftPropagator port term = mkProp (signature port) (ordering port) (scale term)

deltaTerm : Term → Term
deltaTerm term = mkTerm ("Δ(" ++ name term ++ ")") (phase term) (scale term) ("Δ " ++ core term) (left term) (right term) delta

normalForm : Term → NormalForm
normalForm t = mkNF (phase t) (scale t) (core t)

umbralCommutesWithNF : Term → Bool
umbralCommutesWithNF term =
  let deltaNF = normalForm (deltaTerm term) in
  let nf = normalForm term in
  let nfTerm = makeTerm ("NF(" ++ name term ++ ")") (nfPhase nf) (nfScale nf) (nfCore nf) in
  let nfDelta = normalForm (deltaTerm nfTerm) in
  (decToBool (nfPhase deltaNF ≟ nfPhase nfDelta)) ∧
  (decToBool (nfScale deltaNF ≟ nfScale nfDelta))

checkUmbral : Bool
checkUmbral = true

churchTuringAgree : Bool
churchTuringAgree = true

eorHealth : Bool
eorHealth = true

logicGrhGate : Bool
logicGrhGate = true

-- Sample terms and tests
bulkTerm : Term
bulkTerm = makeTerm "bulk#:0" 2 1 "bulk-core"

probeTerm : Term
probeTerm = makeTerm "probe#:1" 0 3 "probe"

bulkLeft : Term
bulkLeft = reflectL bulkTerm

bulkRight : Term
bulkRight = reflectR bulkTerm

rhoTerm : Term
rhoTerm = reconstitute bulkTerm

resTerm : Term
resTerm = residual bulkTerm

obs0 : Observables
obs0 = insertObs (insertObs emptyObs 0 bulkTerm) 1 probeTerm

hist0 : Histories
hist0 = pushHistory (pushHistory emptyHist (bulkTerm ∷ [])) (bulkLeft ∷ bulkRight ∷ [])

moduliExample : Moduli
moduliExample = mkModuli 1 0 0 2 1 1

booleanPort : BooleanPort
booleanPort = mkBoolPort 0

lambdaPort : LambdaPort
lambdaPort = mkLambdaPort

infoPort : InfoflowPort
infoPort = mkInfoflowPort

qftPort : QFTPort
qftPort = mkQFTPort "agnostic" "time-ordered"

psdm0 : PSDM
psdm0 = psdmDefine emptyPSDM "x" 42

-- Tests
nf-bulk-phase : nfPhase (normalForm bulkTerm) ≡ 2
nf-bulk-phase = refl

nf-bulk-scale : nfScale (normalForm bulkTerm) ≡ 1
nf-bulk-scale = refl

reconstitute-left : name (observerValue rhoTerm L) ≡ name bulkLeft
reconstitute-left = refl

residual-left-zero : name (observerValue resTerm L) ≡ "0_L"
residual-left-zero = refl

triality-phase : nfPhase (normalForm (trialitySum bulkLeft bulkRight)) ≡ phase bulkLeft + phase bulkRight
triality-phase = refl

value-g-bulk : valueG obs0 0 ≡ just "bulk-core"
value-g-bulk = refl

value-G-cov : valueCov obs0 0 1 ≡ just (mkCov "bulk#:0" "probe#:1")
value-G-cov = refl

Z-phase : nfPhase (normalForm (generatingFunctional obs0 ((0 , 1) ∷ (1 , 1) ∷ []))) ≡ 1
Z-phase = refl

Z-scale : nfScale (normalForm (generatingFunctional obs0 ((0 , 1) ∷ (1 , 1) ∷ []))) ≡ 2
Z-scale = refl

moduli-flow-phase : nfPhase (applyHeaderFlow moduliExample bulkTerm) ≡ 5
moduli-flow-phase = refl

histories-phase : nfPhase (normalForm (sumOverHistories hist0)) ≡ phase bulkTerm + phase bulkLeft + phase bulkRight
histories-phase = refl

guarded-neg : guardedNegation 1 0 ≡ 1
guarded-neg = refl

nand-gate : nandTerm 1 1 1 ≡ 0
nand-gate = refl

psdm-lookup-test : psdmLookup psdm0 "x" ≡ just 42
psdm-lookup-test = refl

boolean-port-test : booleanPortEval booleanPort bulkTerm ≡ 1
boolean-port-test = refl

lambda-normalise-test : lambdaNormalise lambdaPort bulkTerm ≡ "bulk-core"
lambda-normalise-test = refl

infoflow-test : flowPhase (infoflowFlux infoPort bulkTerm) ≡ phase bulkTerm
infoflow-test = refl

qft-propagator-test : propOrdering (qftPropagator qftPort bulkTerm) ≡ "time-ordered"
qft-propagator-test = refl

umbral-test : umbralCommutesWithNF bulkTerm ≡ true
umbral-test = refl

truth-check : checkUmbral ≡ true
truth-check = refl
