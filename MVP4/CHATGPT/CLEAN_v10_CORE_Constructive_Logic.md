
# CLEAN v10 — **Core Constructive Logic** (Triality; Bulk as Two Boundaries)

> Minimal, implementation-ready **global logic**. Triality is explicit and the **bulk decomposes into the two boundaries** (precisely: the bulk observable content equals the sum of boundary images; residual core is invisible to both observers). This file **does not** include guarded negation or domain maps; those live in the CLASS spec. All new features remain **definitions** over the v2 primitives and axioms.

---

## 0) Scope and dependencies

- **Depends on the v2 core**: boundary & bulk semirings, couplers/observers (retractions), braided `ad_i`, central scalars `φ, z, barz`, `Λ := z ⊗B barz`, basepoint `Gen4(a_0,…,a_3)=0_B`, and the **header/core NF** with parametric variant.  
- **Triality layer**: typed conjugations `starB, starL, starR` and triality functors `T_L, T_R, T_B`.  
- **Bulk = Two Boundaries**: formal **reconstitution** by boundary projectors with an interaction residual that is erased by both observers.

*(Everything here is definitional on top of v2; no new axioms are introduced.)*

---

## 1) Signature fragment (recap & additions)

- **Sorts**: `L, B, R, I` (unit).  
- **Couplers/observers**: `ι_L, ι_R, ν_L, ν_R` with `ν_*;ι_* = id_*`.  
- **Braiding**: `ad_0..ad_3 : B→B`, central `F_{ij}:I→B`.  
- **Gauges**: `φ, barφ : I→B`, `z, barz : I→B`, `Λ := z ⊗B barz`.  
- **Basepoint**: `a_0..a_3:I→B`, `Gen4:B^4→B`, axiom `Gen4(a_0,…,a_3)=0_B`.  
- **Triality ops (derived)**: `starB:B→B`, `starL:L→L`, `starR:R→R` (typed conjugations).  
- **Projectors (derived)**: `[L](t):=ι_Lν_L(t)`, `[R](t):=ι_Rν_R(t)`, `[μ,θ](t):=ι_Lν_L(NF_{μ,θ}(t))`.

**Parametric NF (recap)**: if `NF(t)=(kφ:ℤ, mΛ:ℕ, core(t))`, then  
`NF_{μ,θ}(t) := ( f_θ(kφ), g_μ(mΛ), core(t) )` (header-only).

---

## 2) Triality & decomposition

**Triality functors (derived):**
- `T_L(t) := ν_L(t)` (bulk→left), `T_R(t) := ν_R(t)`, `T_B(x_L,x_R) := ι_L(x_L) ⊕B ι_R(x_R)`.

**Conjugations (typed):** `starB` anti-involution on `⊗B`; `starL, starR` compatible with observers:
`starB(ι_L x)=ι_L(starL x)`, `ν_L(starB t)=starL(ν_L t)` and symmetrically for `R`.

**Reconstitution map (bulk = two boundaries):**
\[
\rho(t) \;:=\; [L](t) \;⊕_B\; [R](t) \;\in \; \mathrm{im}(ι_L) ⊕_B \mathrm{im}(ι_R).
\]
**Residual**: `int(t) := t ⊕B ρ(t)` expressed via the canonical NF splitter (no subtraction needed: store the “difference” as a tagged residual).

**Decomposition Theorem (observer form).** For all `t:B`,
\[
ν_L(t) \;=\; ν_L([L](t) ⊕_B [R](t)), \qquad
ν_R(t) \;=\; ν_R([L](t) ⊕_B [R](t)) .
\]
*Hence the **observable bulk** equals the **sum of the two boundaries***; `int(t)` is **invisible to both observers**:
`ν_*(int(t)) = ν_*(t ⊕B ρ(t)) = ν_*(t) ⊕_* ν_*(ρ(t)) = 0_*` by retraction and linearity.

**Equality corollary.** Modulo the active mask `≡_qmask`, if observers are **jointly faithful** on your model class, then `t ≡_qmask ρ(t)` (bulk collapses to its boundary sum in equality tests).

---

## 3) Generating functional & cumulants (recap)

For finite set `I_fin ⊆ I`:
\[
Z[J] := ⟨ \bigotimes_{i∈I_{fin}} (1_B ⊕_B ι_L(J_i) ⊗_B Obs(i)) ⟩_{μ,θ} \in L.
\]
Couplings `g(i)`, connected `G(i,j)`, β-fields, monotones `a,c` as in the v2 spec (definitionally via `ν_L ∘ NF_{μ,θ}`).

---

## 4) Unit tests (core)

```csh
# Masks & triality set-up
logic eval "(set-quotient-mask! '(phase))"
logic eval "(define x '(ad 0 (gen4 a0 a1 a2 a3)))"
logic eval "(define y '(ad 1 (gen4 a0 a1 a2 a3)))"

# RNF idempotence of projectors
logic eval "(equal? 'B '([L] ([L] x)) '([L] x))"      # -> #t
logic eval "(equal? 'B '([R] ([R] y)) '([R] y))"      # -> #t

# Bulk = two boundaries (observer equalities)
logic eval "(equal? 'L '(ν_L x) '(ν_L (⊕B ([L] x) ([R] x))))"   # -> #t
logic eval "(equal? 'R '(ν_R x) '(ν_R (⊕B ([L] x) ([R] x))))"   # -> #t

# Residual invisibility
logic eval "(define intx '(⊕B x (⊕B ([L] x) ([R] x))))"         # tagged residual
logic eval "(equal? 'L '(ν_L intx) '0_L)"                       # -> #t
logic eval "(equal? 'R '(ν_R intx) '0_R)"                       # -> #t

# Conjugation interface
logic eval "(equal? 'B '(starB (ι_L 1_L)) '(ι_L (starL 1_L)))"  # -> #t

# Cumulant sanity
logic eval "(register-observable 0 x)"
logic eval "(value g 0)"
logic eval "(value G 0 0)"
```

---

## 5) Notes

- This core is **constructive** (no global negation). Guarded negations, domain ports, PSDM and Feynman view are layered in the CLASS file.  
- Triality and the boundary sum property are **definitions over** observers and NF and hold in every v2‑model.

*End Core.*
