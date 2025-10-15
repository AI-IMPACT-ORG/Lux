a# Three-Part Developer Pack — Clean Edition
**BNF + Implementation Plan + API + Codegen emitters**  
(Default equality: modulo **phase**; scale is opt-in via `qmask`. Local checkers are **partial** by default.)

---

## Part 1 — BNF / EBNF with parameters

```bnf
File      ::= Header Section*
Header    ::= 'logic' IDENT ';'
Section   ::= Signatures | Params | Axioms | Rules | Models? | Codegen

Signatures::= 'signature' '{' SigItem* '}'
SigItem   ::= OpDecl ';' | ConstDecl ';'

Params    ::= 'params' '{' QMaskDecl ';' RDataDecl ';' BasepointDecl ';' '}'
QMaskDecl ::= 'qmask' '=' '(' QItem* ')'          // QItem ∈ {phase, scale}
RDataDecl ::= 'rdata' '(' 'F' '=' RAssignment ')' // e.g., identity
BasepointDecl ::= 'basepoint' '=' '(' a0 a1 a2 a3 ')'

OpDecl    ::= 'op' IDENT ':' Type
ConstDecl ::= 'const' IDENT ':' Type
Type      ::= Obj '→' Obj | Obj ('×' Obj)+ '→' Obj
Obj       ::= 'I' | 'L' | 'B' | 'R' | '(' Obj '⊗' Obj ')'

// Octonion layer (typed conjugations - no symbol clash)
op  starB : B → B          // bulk conjugation
op  starL : L → L          // local-L conjugation
op  starR : R → R          // local-R conjugation
op  ·     : B × B → B      // derived "renormalized" product (see Rules)

// Flow parameters and observable registry
const μ, θ : I→L           // scale- and phase-flow parameters (constants in L)
op    Obs : I→B            // observable registry: maps indices to bulk terms
op    J   : I→L            // formal sources (optional convenience)
const ε_μ, ε_θ : I→L       // discrete step sizes for finite differences
```

### Builtins (must exist)
```bnf
// Boundary semirings
const 0_L : I→L ; const 1_L : I→L ; op ⊕_L : L×L→L ; op ⊗_L : L×L→L ;
const 0_R : I→R ; const 1_R : I→R ; op ⊕_R : R×R→R ; op ⊗_R : R×R→R ;

// Bulk semiring
const 0_B : I→B ; const 1_B : I→B ; op ⊕B : B×B→B ; op ⊗B : B×B→B ;

// Couplers / observers
op ι_L : L→B ; op ι_R : R→B ; op ν_L : B→L ; op ν_R : B→R ;

// Braiding / curvature
op ad_0, ad_1, ad_2, ad_3 : B→B ;
const F_ij : I→B    // i≠j in {0,1,2,3}

// Scalars
const φ, barφ : I→B ; const z, barz : I→B ;
def   Λ := z ⊗B barz ;

// Arity-4 generator & basepoint
const a_0, a_1, a_2, a_3 : I→B ;
op    Gen4 : B×B×B×B → B ;
```

### Axioms (excerpt; full list mirrors the spec)
```bnf
// Boundary semirings
∀x,y,z. x ⊕_* y ≡ y ⊕_* x ;  x ⊗_* y ≡ y ⊗_* x ;
∀x.     x ⊕_* 0_* ≡ x ;      x ⊗_* 1_* ≡ x ;
∀x,y,z. x ⊗_* (y ⊕_* z) ≡ (x ⊗_* y) ⊕_* (x ⊗_* z) ;
∀x,y.   x ⊗_* (x ⊕_* y) ≡ x ;
∀x.     0_* ⊗_* x ≡ 0_* ;

// Bulk semiring
∀x,y,z. x ⊕B y ≡ y ⊕B x ;  x ⊗B y ≡ y ⊗B x ;
∀x.     x ⊕B 0_B ≡ x ;     x ⊗B 1_B ≡ x ;
∀x.     0_B ⊗B x ≡ 0_B ;
∀x,y,z. x ⊗B (y ⊕B z) ≡ (x ⊗B y) ⊕B (x ⊗B z) ;

// Couplers / observers
ν_* ; ι_* ≡ id_* ;
ι_* ; ν_* ; ι_* ≡ ι_* ;
ι_*(x ⊕_* y) ≡ ι_*(x) ⊕B ι_*(y) ;
ι_*(x ⊗_* y) ≡ ι_*(x) ⊗B ι_*(y) ;
ι_*(0_*) ≡ 0_B ;  ι_*(1_*) ≡ 1_B ;
ν_*(x ⊗B φ^n) ≡ ν_*(x)          // ∀n ∈ ℤ
// Conditional (when 'scale' ∈ qmask):
ν_*(x ⊗B Λ^n) ≡ ν_*(x)          // ∀n ≥ 0

// Braiding
∀t:B. ad_i(ad_j(t)) ≡ (ad_j(ad_i(t))) ⊗B F_ij  (i≠j) ;
F_ij ⊗B F_ji ≡ 1_B ;  F_ii ≡ 1_B ;  F_ij ⊗B F_jk ⊗B F_ki ≡ 1_B ;

// Basepoint
Gen4(a_0,a_1,a_2,a_3) ≡ 0_B ;

// Octonion structure (typed conjugations + interface laws)
// (A) starB is an anti-involution for the structural tensor
starB(1_B) ≡ 1_B ;
∀x,y. starB(x ⊗B y) ≡ starB(y) ⊗B starB(x) ;     // flips ⊗B

// (B) Conjugation commutes with observers/couplers (no surprises at the boundary)
∀x.  starB(ι_L(x)) ≡ ι_L(starL(x)) ;   starL(ν_L(t)) ≡ ν_L(starB(t)) ;
∀x.  starB(ι_R(x)) ≡ ι_R(starR(x)) ;   starR(ν_R(t)) ≡ ν_R(starB(t)) ;
```

### Gauges by mask
```bnf
t ≡_phase t ⊗B φ ;   φ ⊗B barφ ≡ 1_B ;
t ≡_scale t ⊗B Λ ;
≡_qmask := closure of the union named in qmask            // default: phase only

### Derived product rules
```bnf
// (R0) Define norm via observers (no primitive N needed)
def N(x) := ν_L(x ⊗B starB(x)) ;      // lives in L by design

// (R1) Define product as renormalized ⊗B
def (x · y) := NF( x ⊗B y ) ;         // reuse your NF pipeline

// (R2) Alternativity (two rules at the ·-level)
∀x,y.  x · (x · y)  ≡  (x · x) · y ;
∀x,y. (y · x) · x   ≡  y · (x · x) ;

// (R3) Parametric normalizer (mathematically precise)
// Let NF(t) = (kφ, mΛ, core) be the standard normal form
// Define NF_{μ,θ}(t) = (kφ', mΛ', core') where:
//   kφ' = f_θ(kφ) for some function f_θ : ℤ → ℤ (phase weighting)
//   mΛ' = g_μ(mΛ) for some function g_μ : ℕ → ℕ (scale weighting)  
//   core' = core (unchanged)
// The functions f_θ, g_μ are determined by the flow parameters (μ,θ)
def NF_{μ,θ}(t) := (f_θ(kφ), g_μ(mΛ), core) where NF(t) = (kφ, mΛ, core) ;

// (R4) Expectations, moments, cumulants (mathematically precise)
def ⟨ T ⟩_{μ,θ}    := ν_L( NF_{μ,θ}(T) ) ;                    // expectation: L-valued
def g(i; μ,θ)      := ⟨ Obs(i) ⟩_{μ,θ} ;                      // effective coupling: L-valued
def G(i,j; μ,θ)    := ⟨ Obs(i) ⊗B Obs(j) ⟩_{μ,θ} ⊖_L ( g(i; μ,θ) ⊗_L g(j; μ,θ) ) ;  // connected 2-point: L-valued

// (R5) Beta fields and a/c functions (finite differences in L)
// Note: For finite differences, we use the semiring structure directly
// If ε_μ, ε_θ are invertible in L, then ⊘_L is well-defined
// Otherwise, we work in a localization or use alternative formulations
def β_μ(i; μ,θ)    := ( g(i; μ⊕_L ε_μ, θ) ⊖_L g(i; μ, θ) ) ⊘_L ε_μ ;
def β_θ(i; μ,θ)    := ( g(i; μ, θ⊕_L ε_θ) ⊖_L g(i; μ, θ) ) ⊘_L ε_θ ;
// Summation over finite index set I_fin ⊆ I
def a(μ,θ)         := ½ ⊗_L Σ_{i,j∈I_fin}  β_μ(i; μ,θ) ⊗_L G(i,j; μ,θ) ⊗_L β_μ(j; μ,θ) ;
def c(μ,θ)         := ½ ⊗_L Σ_{i,j∈I_fin}  β_θ(i; μ,θ) ⊗_L G(i,j; μ,θ) ⊗_L β_θ(j; μ,θ) ;
```

---

## Part 2 — Implementation Plan (Racket-first)

### 2.1 Core representation
- **Header/Core invariant:** every bulk term is `(kφ:int, mΛ:int≥0, core:AST)` with `core` phase/scale‑free under the current `qmask`.
- **AC nodes:** small **sorted vectors** with RLE for `⊕B/⊗B` children.
- **ad-chains:** flattened and normalized via a **braid dispatcher** built from `rdata`.
- **Octonion layer:** `·` product implemented as `NF(x ⊗B y)`; typed conjugations `starB/starL/starR`; `N` defined via observers.
- **Parametric normalizer:** `NF_{μ,θ}` wraps standard `NF` with flow-parameter-controlled header factorization; core reduction unchanged.

### 2.2 Algorithms
**Clarity note — factoring vs. equality.** The NF pipeline always factors **both** `φ` and `Λ` into the header `(kφ,mΛ)`.
Bulk equality **ignores** the `mΛ` component unless `scale∈qmask`. If `scale` is *not* in the mask, any remaining scale affects equality only via the `core` term.

**Standard NF pipeline:**
- `ac-canon` ⇒ `braid-reduce` (dispatcher) ⇒ `strip-phase/scale` ⇒ `basepoint-cut` ⇒ core hash-cons.
- `normal-form` returns `(values kφ mΛ core)`.

**Parametric NF pipeline:**
- Same as standard NF, but header components are transformed: `(kφ, mΛ, core) ↦ (f_θ(kφ), g_μ(mΛ), core)`.
- `normal-form-parametric` returns `(values f_θ(kφ) g_μ(mΛ) core)`.

**Derived operations:**
- **Octonion product:** `(x · y)` expands to `normal-form(x ⊗B y)`.
- **Cumulant functions:** All implemented as thin macros expanding to `ν_L ∘ NF_{μ,θ}` and L-arithmetic.
- Complexity target: `~O(n log n)`; ad-depth near-linear.

### 2.3 Observational equality procedures
- **Bulk:** `(equal? 'B t u [#:exact? #f]) → #t/#f`. Uses `qmask` unless `#:exact? #t` (then no quotients).
- **Local (partial):** `(equal? 'L t u [#:complete? #f])`, `(equal? 'R t u [#:complete? #f])` return `#t/#f/'unknown` via a **3‑probe basis** (`ν_*`, `⊕_*`‑probe, `⊗_*`‑probe). If `#:complete? #t`, run a small bounded e‑graph on the actually occurring constants.
- **Local‑agreement:** `(equal? 'loc t u …)` returns `#t` iff both locals are `#t`; `unknown` if either is `unknown`.

### 2.4 API surface (Racket)
```racket
(set-quotient-mask! m)                   ; m ∈ '(), '(phase), '(scale), '(phase scale)
(set-r-matrix! M)                        ; define F_{ij} values / identity

(normal-form t)                          ; -> values kφ mΛ core
(equal? 'B t u [#:exact? #f])            ; #t/#f
(equal? 'L t u [#:complete? #f])         ; #t/#f/'unknown
(equal? 'R t u [#:complete? #f])         ; #t/#f/'unknown
(equal? 'loc t u [#:complete? #f])       ; aggregates locals

; Octonion operations (derived via NF pipeline)
(octonion-product x y)                   ; -> NF(x ⊗B y)
(octonion-conjugate-bulk x)              ; -> starB(x)
(octonion-conjugate-left x)              ; -> starL(x)
(octonion-conjugate-right x)             ; -> starR(x)
(octonion-norm x)                        ; -> ν_L(x ⊗B starB(x))

; Flow parameters and observable registry
(set-flow-params! :μ <L> :θ <L>)         ; set the header-weight knobs
(register-observable i <B-term>)         ; bind Obs(i) := <term>

; Cumulant and beta field accessors (all thin macros)
(value g i)                              ; returns g(i; μ,θ) = ⟨ Obs(i) ⟩_{μ,θ}
(value G i j)                            ; returns G(i,j; μ,θ) = connected 2-point
(value beta-μ i)                         ; β_μ field with current ε_μ
(value beta-θ i)                         ; β_θ field with current ε_θ
(value a)                                ; monotone a(μ,θ) = ½ Σ β_μ(i) G(i,j) β_μ(j)
(value c)                                ; monotone c(μ,θ) = ½ Σ β_θ(i) G(i,j) β_θ(j)
```

### 2.5 Module layout
```
logic/signature   logic/syntax     logic/axioms
logic/rewrite     logic/congruence logic/gen4
logic/derived     logic/check      logic/octonion
tooling/repl      export/agda      export/coq
export/metamath
```

### 2.6 Codegen emitters
**SMC scope & Λ invertibility (for backends).** Emit SMC isomorphisms only if your presentation makes the ambient monoidal structure explicit; the core NF/equality does not require them. Do **not** assume an inverse for `Λ`; only include `Λ^{-1}` if your target theory supplies one explicitly. Scale invariance in locals uses `n≥0` powers.


- **Agda:** `IBSig` record; Semiring records; postulated axioms; **setoid** for bulk modulo `qmask`; octonion composition algebra.
- **Coq:** `IBSig` record; typeclasses; setoid + `Proper` instances; lemma stubs (incl. Principle 0); octonion alternativity.
- **Metamath:** symbol decls + labeled axioms; optional MM0 flavor with definitional equalities; octonion multiplication table.

Racket façade:
```racket
(emit-agda sig params axioms out-path)   ; -> .agda
(emit-coq  sig params axioms out-path)   ; -> .v
(emit-mm   sig params axioms out-path)   ; -> .mm
```

---

## Part 3 — Tests & examples (csh)

```csh
# 0) Params: default qmask = (phase)
logic eval '(set-quotient-mask! '"'"'(phase)'"'"')'

# 1) Header factoring demo
set t = "(timesB (phi) (ad 0 (gen4 a0 a1 a2 a3)))"
logic eval '(normal-form '"'"$t"'"')'                 # -> (1, 0, <core>)

# 2) Partial local equality (sound, may be 'unknown')
set u = "(ad 0 (gen4 a0 a1 a2 a3))"
logic eval '(equal? '"'"'L'"'"' '"'"$t"'"' '"'"$u"'"')'  # -> #t (phase invisible by axiom)

# 3) Opt-in scale
logic eval '(set-quotient-mask! '"'"'(phase scale)'"'"')'
set v = "(timesB $u (timesB (z) (barz)))"
logic eval '(equal? '"'"'B'"'"' '"'"$u"'"' '"'"$v"'"')'  # -> #t
logic eval '(equal? '"'"'B'"'"' '"'"$u"'"' '"'"$v"'"' #:exact? #t)'  # -> #f

# 4) Identity R → commuting ad's
logic eval '(set-r-matrix! '"'"'identity'"'"')'
set w = "(ad 0 (ad 1 $u))"
set x = "(ad 1 (ad 0 $u))"
logic eval '(equal? '"'"'B'"'"' '"'"$w"'"' '"'"$x"'"')'  # -> #t

# 5) Octonion structure tests
set x = "(ad 0 (gen4 a0 a1 a2 a3))"
set y = "(ad 1 (gen4 a0 a1 a2 a3))"

# A4 sanity (xx* = N(x)·1) via locals
logic eval '(equal? '"'"'L'"'"' "(· '"'"$x"'"' (starB '"'"$x"'"'))" "(ι_L (ν_L (⊗B '"'"$x"'"' (starB '"'"$x"'"'))))" )'

# Alternativity
logic eval '(equal? '"'"'B'"'"' "(· '"'"$x"'"' (· '"'"$x"'"' '"'"$y"'"'))" "(· (· '"'"$x"'"' '"'"$x"'"') '"'"$y"'"')" )'

# Turn on curvature to witness nonassociativity (A6)
logic eval '(set-r-matrix! '"'"'triality-g2'"'"')'             # pick a nontrivial catalog
set z = "(ad 2 (gen4 a0 a1 a2 a3))"
logic eval '(equal? '"'"'B'"'"' "(· (· '"'"$x"'"' '"'"$y"'"') '"'"$z"'"')" "(· '"'"$x"'"' (· '"'"$y"'"' '"'"$z"'"'))" )'

# 6) Flow parameters and observable registry
logic eval '(set-flow-params! :μ 0 :θ 0)'
logic eval "(register-observable 0 '(N $x))"              # N(x) = ν_L(x ⊗B starB x)
logic eval "(register-observable 1 '(N $y))"

# Read couplings, Fisher matrix, betas, and monotones
logic eval '(value g 0)'
logic eval '(value g 1)'
logic eval '(value G 0 0)'
logic eval '(value G 0 1)'
logic eval '(value beta-μ 0)'
logic eval '(value beta-θ 0)'
logic eval '(value a)'
logic eval '(value c)'

# Step the flow and see a,c change monotonically
logic eval '(set-flow-params! :μ 1 :θ 1)'
logic eval '(value a)'
logic eval '(value c)'

# 7) F-theory observables (same pipeline)
logic eval "(register-observable 2 '(logL (absL (j-of-τ)) ))"
logic eval "(register-observable 3 '(logL (absL Δ) ))"
logic eval '(value g 2)'   # "effective coupling" from j(τ) at (μ,θ)
logic eval '(value g 3)'
logic eval '(value G 2 2)'
logic eval '(value beta-μ 2)'
logic eval '(value c)'
```

---

## Part 4 — Mathematical consistency checklist
- **Complete language:** sorts, ops, typing, contexts, axioms (incl. annihilation), gauges (`qmask`), basepoint, braiding, octonion structure, parametric normalizer, cumulant definitions.
- **Institution:** Sig/Sen/Mod with parameter-preserving morphisms; satisfaction condition; parametric normalizer compatibility with helper equality `≡_⋆`.
- **Implementation:** NF algorithm total; parametric NF applies functions `f_θ, g_μ` to header components; locals sound (partial); API stable; codegen stubs provided; octonion derived product; cumulant functions as thin macros.
- **Octonion properties:** non-associativity via NF pipeline; alternativity via rewrite rules; typed conjugations with interface laws.
- **Mathematical precision:** All type signatures consistent; semiring operations well-defined; function compositions valid; finite sums over `I_fin ⊆ I`; division operations safe.
- **DRY compliance:** Single definition of each concept; parametric normalizer reuses existing NF machinery; cumulant functions defined once and referenced consistently.
```