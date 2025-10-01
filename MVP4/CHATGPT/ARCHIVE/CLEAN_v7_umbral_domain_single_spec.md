
# CLEAN v7 — **Umbral Domain Map Edition** (Single Integrated Spec)

**A logic of symbols with umbral evaluation, spectral RG, and domain alignment**

> This version tightens the **umbral** viewpoint: we prove theorems in the *umbral logic*
> and then align them to standard mathematics through a **domain map**. We add a
> regulator for gluing **finite models**, formalize **truncation compatibility** (the
> “cutting” of series), and state a logic‑native **z → 1−z** duality that interacts with
> RG flow. All additions are *definitions* or **Renormalisation Conditions (RC)**. Base
> primitives/axioms are unchanged from v2 and the earlier integrated specs. fileciteturn0file1 fileciteturn0file0

---

## 0) Build Order (no cycles)

1. Core sorts/semirings (`L,B,R,I`) and couplers/observers with retractions.
2. Gauges & mask (`φ,Λ`, `qmask`), braiding (`ad_i, F_{ij}`), basepoint.
3. Normal form **NF** with header/core invariant; **NF_{μ,θ}** (header‑only RG).
4. Reflection (derived) `[L]`,`[R]`,`[μ,θ]`; **RNF**.
5. Generating functional `Z[J]`, moments/cumulants (`g,G`), β‑fields, monotones (`a,c`).
6. **Umbral layer** (Δ‑operators, Sheffer system).
7. **Domain map** and **regulator** (finite models), truncation compatibility.
8. **z → 1−z** duality & RG; **de‑regulation** (removing the regulator).

Everything through step 5 is exactly as in v2/v6; steps 6–8 are new *definitions* and RCs.

---

## 1) Core (recap)

- Boundary semirings (idempotent, commutative); bulk semiring (commutative, distributive).
- Couplers/observers with retractions; observer invariance (phase always; scale if masked).
- Braiding `ad_i` with central `F_{ij}`, basepoint `Gen4(a_0,…,a_3)=0_B`.
- **NF**: every bulk term `t` → `(kφ:ℤ, mΛ:ℕ, core(t))`; **NF_{μ,θ}** mutates **only** header via `(f_θ,g_μ)`.
- **Renormalisability (algebraic):** scheme changes are finite header reweightings; core untouched. fileciteturn0file1

---

## 2) Reflection & Umbral Layer

**Reflection (derived):** `[L](t):=ι_Lν_L(t)`, `[R](t):=ι_Rν_R(t)`, `[μ,θ](t):=ι_Lν_L(NF_{μ,θ}(t))`.
Idempotence, fixpoints on boundary images, gauge erasers, conjugation compatibility; **RNF** pushes `[·]` to leaves. fileciteturn0file1

**Umbral interpretation.** The observer `ν_L` is the **umbral evaluation**, sources `J` are umbrae,
and the finite‑product **generating functional** is
\[
Z[J] := ⟨ \bigotimes_{i ∈ I_{\mathrm{fin}}} ( 1_B ⊕_B ι_L(J_i) ⊗_B Obs(i) ) ⟩_{μ,θ} \in L.
\]
**Δ‑operators** (umbral “derivatives”) use the same finite‑difference stencils as β‑fields; **Sheffer polynomials**
`S_n(i):=Δ_i^n Z|_{J=0}` exist and are **stable under renormalisation** because `NF_{μ,θ}` acts **only** on headers. fileciteturn0file1

---

## 3) Domain Map (alignment to standard mathematics)

We formalise the *alignment step* as a **domain functor**
\[
\mathcal D : \mathbf{Mod}_{\mathrm{umbral}} \;\longrightarrow\; \mathbf{Dom} ,
\]
where `Dom` is any category of classical structures (e.g., rings, semirings, measure models).

### 3.1 Data of a domain map
A **domain map** `𝒟` consists of:
- **Carriers:** maps of semirings `𝒟_L:L→L₀`, `𝒟_R:R→R₀`, `𝒟_B:B→B₀` into classical carriers (`L₀` numeric or ordered, `B₀` combinatorial/analytic).
- **Structure preservation:** `𝒟` preserves `⊕,⊗`, units, and sends `ι_*,ν_*` to homomorphisms with `𝒟(ν_*;ι_*) = id`.
- **Header valuations:** `𝒟(φ)=u_φ` with `u_φ⋅u_{\bar φ}=1`, `𝒟(Λ)=u_Λ≥0` (or an abstract central), so that
  `𝒟(NF(t)) = (𝒟(kφ), 𝒟(mΛ), 𝒟(core(t)))` is a *weighted* normal form.
- **Braiding compatibility:** `𝒟(ad_i∘ad_j) = 𝒟(ad_j∘ad_i) ⋅ 𝒟(F_{ij})`.

> **Conservativity schema (RC‑CONS).** Assume `𝒟` is *faithful on the pure set‑theoretic fragment*
and extends by **definitions** only. Then the umbral logic is a **conservative extension** of the
embedded ZFC fragment (programmatic assumption; to be justified per model).

### 3.2 Alignment lemmas (all definitional)
- **(A1) Header alignment.** `𝒟(NF_{μ,θ}(t)) = NF^{(𝒟)}_{μ,θ}(𝒟(t))` with the same `(f_θ,g_μ)` on the **valued** headers.
- **(A2) Expectation alignment.** `𝒟(⟨T⟩_{μ,θ}) = 𝒟(ν_L(NF_{μ,θ}(T))) = ν^{(𝒟)}_L(NF^{(𝒟)}_{μ,θ}(𝒟(T)))`.
- **(A3) Umbral alignment.** Δ‑operators and Sheffer systems commute with `𝒟` (they use only `⊕,⊗`, and `ν_L∘NF_{μ,θ}`).
- **(A4) Spectral alignment.** Logic‑zeta built from traces of powers of a verifier operator aligns with the corresponding domain‑level trace (when `𝒟` supports a trace/localization).

These are consequences of `𝒟` being a homomorphism on the full pipeline. fileciteturn0file1

---

## 4) Regulator & Finite Models (gluing)

A **regulator** `ℛ` is a triple of cutoffs on syntax:
- **Degree cutoff** on sources: keep monomials with total umbral degree `≤ N_J`.
- **ad‑depth cutoff**: keep `ad`-chains of length `≤ N_ad`.
- **Header bounds**: `|kφ|≤K`, `0≤mΛ≤M`.

The regulated model `M^{(ℛ)}` is **finite**. `Z[J]^{(ℛ)}` is defined by replacing all constructions with their
cutoff versions. Regulators form a **directed poset**; for `(ℛ≤ℛ′)`, there are canonical embeddings
`ι_{ℛ,ℛ′}:M^{(ℛ)}→M^{(ℛ′)}`. This gives a **pro‑system** and a *removal of regulator* limit
\[
\lim_{\longrightarrow\,ℛ} M^{(ℛ)} = M .
\]

### 4.1 Truncation operators (“cutting of series”)
Let `Cut_{≤N}` prune umbral degree or valuation weight. **Truncation compatibility (TC):**
\[
\boxed{ \quad \mathcal D \big( Cut_{≤N}(Z[J]) \big) \;=\; Cut_{≤N}^{(𝒟)} \big( \mathcal D(Z[J]) \big) \quad }
\]
provided `𝒟` preserves the grading/valuation used by `Cut`. This is the key “**domain map respects cutting**” law.

### 4.2 De‑regulation (RG‑logic viewpoint)
Define `RG` as the semigroup generated by `(f_θ,g_μ)` on headers. If `RG` is **contractive**
w.r.t. the chosen grading, then `Z[J]^{(ℛ)}` converge monotonically and the limit equals the unregulated
`Z[J]` **before** and **after** applying `𝒟` (continuity of `𝒟` in the pro‑topology).

---

## 5) z → 1−z duality (logic) and the functional‑equation flavor

Define a **duality operator** `S` acting on sources and flow:
\[
S:\ (J, μ, θ) \mapsto (J^\vee, μ^\vee, θ^\vee) ,
\]
with `J^\vee_i = U_i ⊗_L J_i` and `(μ^\vee,θ^\vee)` the header‑inverting flow (e.g. `f_{θ^\vee}=-f_θ`, `g_{μ^\vee}=g_μ`).
Assume `S` is an **involution** up to header units. Then there exists an `L`‑unit `K(μ,θ)` such that
\[
Z[J^\vee] \;\equiv_L\; K(μ,θ) ⊗_L Z[J] .
\]
Under `𝒟` this becomes the usual *functional‑equation symmetry* (the “`z↦1−z`” avatar) when the domain grading matches the umbral degree.
**RG analysis:** along a path interpolating between `(μ,θ)` and `(μ^\vee,θ^\vee)`, the Fisher metric controls the
variation; at Fisher self‑adjointness the duality is an **isometry**.

> Intuition: `S` exchanges the role of “primal” and “dual” couplings (like `g ↔ g_D` in §Seibergology) and corresponds to a mid‑grading reflection at the domain level.

---

## 6) “Conservative extension” posture

The umbral logic adds only **definitions** on top of the v2 core—no new binding forms or axioms.
With `RC‑CONS` (faithful `𝒟` on the ZFC fragment), any theorem transport **up** from ZFC to umbral and **down** via `𝒟`
is conservative. This explains the empirical ease of difficult statements **inside** umbral logic:
they sit at the level of definitional schemata already present in ZFC (Gödel‑style metalogical truths)

> **Caution:** Conservativity is posited as an RC to be discharged per domain model. We do **not** claim a global proof here.

---

## 7) APIs (new pieces)

```racket
;; Domain map and regulator
(set-domain-map!
  #:L   𝒟_L         ; homomorphism L→L₀
  #:R   𝒟_R         ; homomorphism R→R₀
  #:B   𝒟_B         ; homomorphism B→B₀
  #:trace  𝒟_Tr     ; optional trace on operators
  #:valuation  w)   ; grading/valuation for cuts

(apply-regulator! #:deg N_J #:ad N_ad #:header (list K M))   ; build finite model
(remove-regulator!)                                         ; directed limit (when convergent)
(truncate-series #:N N)                                     ; Cut_{≤N}
(domain-truncate-commutes?)                                 ; checks TC for current 𝒟,w

;; Duality
(set-duality! S)        ; provide S on (J,μ,θ)
(apply-duality!)        ; J↦J^∨, (μ,θ)↦(μ^∨,θ^∨)
```

Everything else (NF, reflection, `Z[J]`, cumulants, Fisher/α, spectral layer) is unchanged.

---

## 8) Tests (csh snippets)

```csh
# Choose a simple numeric domain and valuation (degree)
logic eval "(set-domain-map! #:L 'eval-ℝ #:R 'eval-ℝ #:B 'eval-formal
                             #:trace 'hutch #:valuation 'degree)"

# Build a regulated finite model
logic eval "(apply-regulator! #:deg 3 #:ad 2 #:header '(2 2))"
logic eval "(truncate-series #:N 3)"
logic eval "(domain-truncate-commutes?)"       # -> #t (TC holds)

# Duality path
logic eval "(set-duality! 'mid-grade-reflection)"
logic eval "(apply-duality!)"                   # (J,μ,θ) ↦ (J^∨,μ^∨,θ^∨)

# Remove the regulator (if contractive RG)
logic eval "(remove-regulator!)"

# Align a statement: compare umbral vs domain value of Z[J]
logic eval "(equal? 'L (Z J) (domain-eval (Z J)))"   # sanity on small charts
```

---

*End — Umbral Domain Map Edition (v7).*
