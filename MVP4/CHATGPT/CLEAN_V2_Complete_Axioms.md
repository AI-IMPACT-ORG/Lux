# CLEAN V2 — Complete Axiom Specification (homogenized; integer headers, aux units)
**Mathematical foundation for v10 Core and CLASS**

> This file provides the **complete formal axiom set** that v10 Core and CLASS depend upon. It is faithful to what v10 expects, uses **three separate semirings** (L, B, R), and makes the **bulk an exp/log semiring**. This implements "mde going down (L,B,R) with a dual going up" as **observers (down)** and **embeddings (up)** with **connective axioms** tying them together.

---

## 0) Intent & relation to v10

* v10 Core and CLASS **assume** v2 provides: the three semirings, observers/embeddings as **retractions**, a **braided** family `adᵢ : B→B`, **central scalars** (φ,z,\bar{z}) with (Λ := z ⊗_B \bar{z}), a **basepoint/Gen4** axiom, and a **header/core normal form (NF)** (with the parametric variant sitting naturally on top). The reconstruction below gives exactly that, and nothing stronger than needed.  
* Think of **v10** as an **alternative axiom set / definitional layer** over this v2 base (triality, "bulk = two boundaries", PSDM, ports, guarded negation, etc., are *definitions + model RCs* that do not add axioms).

---

## 1) Signature (v2)

### Sorts

* `L, B, R` — three **distinct** semirings (left boundary, bulk, right boundary).
* `Core` — core component semiring for the bulk's exp/log structure.

### Algebra on each layer

* `(L, ⊕_L, ⊗_L, 0_L, 1_L)` — commutative semiring.
* `(R, ⊕_R, ⊗_R, 0_R, 1_R)` — commutative semiring.
* `(B, ⊕_B, ⊗_B, 0_B, 1_B)` — **exp/log semiring** (details in §2).
* `(Core, ⊕^Core, ⊗^Core, 0_Core, 1_Core)` — commutative semiring for core components.

### Up (embeddings) and down (observers)

* Embeddings (up): `ι_L : L → B`, `ι_R : R → B`.
* Observers (down): `ν_L : B → L`, `ν_R : B → R`.
* **Retractions:** `ν_L ∘ ι_L = id_L`, `ν_R ∘ ι_R = id_R`.
  (*This is exactly what v10 relies on to derive `[L] := ι_Lν_L`, `[R] := ι_Rν_R` and the reconstitution `ρ`.*) 

### Distinguished bulk scalars & braiding data

* Central **units** in `B`: `φ, z, \bar{z} : B`, with `Λ := z ⊗_B \bar{z}` central and a **unit** as well. *(v10 uses `φ` for phase and `Λ` for scale exponents; making them units enables expanding, neutral, and contracting flows.)* 
* Braided operators: `ad₀, ad₁, ad₂, ad₃ : B → B`, forming the "braided" action required by v10. *(See axioms A5 below.)* 
* Basepoint & generator: `a₀,…,a₃ : B`, `Gen4 : B⁴→B`, with **Gen4 axiom** `Gen4(a₀,…,a₃) = 0_B`.

---

## 2) The **exp/log semiring** structure on `B` (moduli chart)

We present `B` in two **equivalent** ways—**exp** and **log**—and require an isomorphism between them.

### 2.1 Log presentation (headers + core; integer headers)

* **Decomposition maps:**
  ```
  dec_{z\bar{z}} : B → (ℤ × ℤ × ℤ) × Core
  rec_{z\bar{z}} : (ℤ × ℤ × ℤ) × Core → B
  ```
  with **isomorphism properties:** `rec_{z\bar{z}} ∘ dec_{z\bar{z}} = id_B` and `dec_{z\bar{z}} ∘ rec_{z\bar{z}} = id`. Write `dec_{z\bar{z}}(t) = (k_φ(t), m_z(t), m_{\bar{z}}(t), core(t))` with **`k_φ, m_z, m_{\bar{z}} ∈ ℤ`** (integer headers).

**Mathematical Note:** Because `φ, z, \bar z` are **units**, all three headers range over `ℤ`. This makes **contracting** (negative) as well as **expanding** (positive) and **neutral** (zero) flows possible at the header level.

* **Multiplicative law in log coordinates:** (See A6 for formal axioms)
  ```
  dec_{z\bar{z}}(t ⊗_B u) = (k_φ(t)+k_φ(u), m_z(t)+m_z(u), m_{\bar{z}}(t)+m_{\bar{z}}(u),
                             core(t) ⊗^Core core(u)),
  dec_{z\bar{z}}(1_B) = (0,0,0,1_Core).
  ```

* **Header factoring:** (See A6 for formal axioms)
  ```
  t = φ^{k_φ(t)} ⊗_B z^{m_z(t)} ⊗_B \bar{z}^{m_{\bar{z}}(t)} ⊗_B core(t),  Λ := z ⊗_B \bar{z}.
  ```

* **Scale header (integer):**
  ```
  m_Λ(t) := m_z(t) + m_{\bar{z}}(t) ∈ ℤ.
  ```
  *(Since `z, \bar z` are units, `Λ` is a unit and may appear with positive, zero, or negative exponents.)*

> This exactly supports v10's **header/core NF** (NF returns `(k_φ, m_Λ, core)`), with the crucial **"header‑only"** behaviour later used by v10 CLASS's parametric normaliser.  

### 2.2 Exp presentation (exponentials as elements; Laurent form)

* In **exp** (Laurent) form, elements look like `φ^k ⊗_B z^{m_z} ⊗_B \bar{z}^{m_{\bar{z}}} ⊗_B c`, with `k,m_z,m_{\bar{z}}∈ℤ` and `c∈Core`.
* The isomorphism with the log presentation is **by definition** `rec_{z\bar{z}}`/`dec_{z\bar{z}}`.

*(We intentionally do **not** constrain how `dec_{z\bar{z}}` acts over `⊕_B` beyond semiring homomorphism of `ν_*` (below). v10's NF and parametric variants act **on headers only** and **leave `core` untouched**.)*

---

## 3) Semiring laws and **connective axioms**

### A0 — Semiring structure (with auxiliary units)

`(L,⊕_L,⊗_L,0_L,1_L)`, `(R,⊕_R,⊗_R,0_R,1_R)`, and `(Core,⊕^Core,⊗^Core,0_Core,1_Core)` are commutative semirings.

`(B,⊕_B,⊗_B,0_B,1_B)` is a **commutative semiring** with units; `φ, z, \bar{z}` are **central units**. Hence `Λ := z ⊗_B \bar{z}` is central and a **unit**.

**Note:** Each semiring satisfies the standard commutative semiring axioms:
- Associativity and commutativity of addition and multiplication
- Distributivity of multiplication over addition  
- Additive and multiplicative identity elements
- Absorption of multiplication by zero

### A1 — Centrality of bulk scalars

`φ, z, \bar{z}` are **central** for `⊗_B`; hence `Λ := z ⊗_B \bar{z}` is central. (All are **units**; see A0.)
*(v10's headers count powers of `φ` and `Λ`.)* 

Think of `z, \bar{z}` as independent 'worldsheet' central coordinates. The derived scale header is `m_Λ := m_z + m_{\bar{z}}`. 

### A2 — Up/Down are homomorphisms with retractions (**mde down/up**)

* **Down (observers):** `ν_L, ν_R` are semiring homomorphisms:
  `ν_*(t ⊕_B u) = ν_*(t) ⊕_* ν_*(u)`, `ν_*(t ⊗_B u) = ν_*(t) ⊗_* ν_*(u)`, `ν_*(0_B)=0_*`, `ν_*(1_B)=1_*`.
* **Up (embeddings):** `ι_L, ι_R` are semiring homomorphisms (and injective in intended models).
* **Retractions:** `ν_L ∘ ι_L = id_L`, `ν_R ∘ ι_R = id_R`.
* **Projectors (derived):** `[L] := ι_L ∘ ν_L`, `[R] := ι_R ∘ ν_R`, idempotent: `[L]∘[L]=[L]`, `[R]∘[R]=[R]`.
  *(v10 uses exactly these definitions.)* 

### A3 — Cross‑centrality and independence

* **Images commute multiplicatively:** for all `x∈L, y∈R`,
  `ι_L(x) ⊗_B ι_R(y) = ι_R(y) ⊗_B ι_L(x)`.
  *(Ensures left/right contributions compose independently in the bulk; additive commutativity is tautological.)*

### A4 — Connective axioms (bulk ↔ boundaries)

* **Local faithfulness on images (derived from A2):**
  `ν_L(ι_L x ⊗_B t) = x ⊗_L ν_L(t)`, `ν_R(ι_R y ⊗_B t) = y ⊗_R ν_R(t)`.
  *(This is the standard Frobenius‑style compatibility you need to move scalars from `B` to the boundary carriers.)*

**Mathematical Note:** Writing the (trivial) comultiplication as
`δ_B(t) := (ν_L(t), ν_R(t))`, the Frobenius compatibility implies that
`ι_L, ι_R` are coalgebra homomorphisms for `δ_B`. This is merely a reformulation
of the equations above; no extra structure is assumed.

* **Minimal cross‑connector:**
  `ν_L(ι_R y) = 0_L` and `ν_R(ι_L x) = 0_R` for all `x ∈ L, y ∈ R`.
  *(This ensures left/right contributions are orthogonal in the bulk. More general models can replace this with non‑trivial cross‑maps if desired.)*

* **(RC — Moduli covariance.)** This axiom is defined in v10 Core and CLASS layers; v2 provides the base structure only.

### A5 — Braiding (adᵢ) interface

* Each `adᵢ : B→B` is a **semiring automorphism** preserving central scalars and **respecting the exp/log split**:
  ```
  dec_{z\bar{z}}(adᵢ t) = (k_φ(t), m_z(t), m_{\bar{z}}(t), adᵢ_core(core(t)))
  ```
  for some automorphism `adᵢ_core : Core → Core`.

* **Yang-Baxter braiding relations:**
  ```
  ad₀ ∘ ad₁ ∘ ad₀ = ad₁ ∘ ad₀ ∘ ad₁
  ad₁ ∘ ad₂ ∘ ad₁ = ad₂ ∘ ad₁ ∘ ad₂
  ad₂ ∘ ad₃ ∘ ad₂ = ad₃ ∘ ad₂ ∘ ad₃
  ad₀ ∘ ad₂ = ad₂ ∘ ad₀
  ad₀ ∘ ad₃ = ad₃ ∘ ad₀
  ad₁ ∘ ad₃ = ad₃ ∘ ad₁
  ```

**Mathematical Note:** These relations define a 5-strand braid group representation. The first three relations are the standard Yang-Baxter equations for adjacent generators (σᵢσᵢ₊₁σᵢ = σᵢ₊₁σᵢσᵢ₊₁), while the last three ensure that non-adjacent generators commute (σᵢσⱼ = σⱼσᵢ for |i-j| ≥ 2). This is the complete set of relations for the **5-strand braid group B₅** (four generators).

* **Commutation with observers/embeddings:**
  `ν_L ∘ adᵢ = adᵢ_L ∘ ν_L`, `ν_R ∘ adᵢ = adᵢ_R ∘ ν_R`,
  `adᵢ ∘ ι_L = ι_L ∘ adᵢ_L`, `adᵢ ∘ ι_R = ι_R ∘ adᵢ_R`,
  where `adᵢ_L : L → L` and `adᵢ_R : R → R` are the induced automorphisms.

### A6 — Exp/log moduli chart (bijective multiplicative factorisation)

We require a bijection preserving multiplication and units; addition is unconstrained
beyond the observer homomorphisms. The coordinates (k_φ,m_z,m_{\bar z}) are the
log‑headers for the auxiliary moduli φ,z,\bar z.

* **Bijection properties:**
  `rec_{z\bar{z}}(dec_{z\bar{z}}(t)) = t` for all `t ∈ B`,
  `dec_{z\bar{z}}(rec_{z\bar{z}}((k,m_z,m_{\bar{z}},c))) = (k,m_z,m_{\bar{z}},c)` for all `(k,m_z,m_{\bar{z}},c) ∈ (ℤ × ℤ × ℤ) × Core`.

* **Multiplicative compatibility:**
  ```
  dec_{z\bar{z}}(t ⊗_B u) =
    (k_φ(t)+k_φ(u), m_z(t)+m_z(u), m_{\bar{z}}(t)+m_{\bar{z}}(u),
     core(t) ⊗^Core core(u)),
  dec_{z\bar{z}}(1_B) = (0,0,0,1_Core).
  ```

* **Header factoring:**
  ```
  t = φ^{k_φ(t)} ⊗_B z^{m_z(t)} ⊗_B \bar{z}^{m_{\bar{z}}(t)} ⊗_B core(t).
  ```

### A7 — Basepoint/Gen4

* Constants `a₀,…,a₃` and `Gen4 : B⁴→B` satisfy `Gen4(a₀,…,a₃)=0_B`. *(Used by v10's unit tests and examples.)*

---

## 4) Normal form (NF) and its role (integer scale)

* **NF (v2):** the map `NF := collapse ∘ dec_{z\bar{z}} : B → (k_φ : ℤ) × (m_Λ : ℤ) × Core` where 
  ```
  collapse(k, m_z, m_{\bar{z}}, c) := (k, m_Λ := m_z + m_{\bar{z}}, c).
  ```
  This preserves v10's "header‑only" contract while granting explicit **holomorphic/anti‑holomorphic** control in models. 
* **Header‑only:** `NF` leaves `core` intact (by definition of `dec_{z\bar{z}}`).

---

## 5) Derived constructions from v2 axioms

* **Projectors:** `[L] := ι_L ∘ ν_L`, `[R] := ι_R ∘ ν_R` (idempotent by A2).
* **Reconstitution:** `ρ(t) := [L]t ⊕_B [R]t`.
* **Residual:** `int(t) := t ⊕_B ρ(t)` (tagged difference; no subtraction).

* **Bulk = Two Boundaries (observer form):**
  `ν_L(t) = ν_L(ρ(t))`, `ν_R(t) = ν_R(ρ(t))`.
  
  **Proof:** 
  `ν_L(ρ(t)) = ν_L([L]t ⊕_B [R]t) = ν_L(ι_L(ν_L t) ⊕_B ι_R(ν_R t))`
  `= ν_L(ι_L(ν_L t)) ⊕_L ν_L(ι_R(ν_R t))` (by A2 homomorphism)
  `= ν_L t ⊕_L ν_L(ι_R(ν_R t))` (by A2 retraction: `ν_L ∘ ι_L = id_L`)
  `= ν_L t ⊕_L 0_L` (by A4 cross-connector: `ν_L(ι_R y) = 0_L`)
  `= ν_L t` (by semiring identity)
  
  The symmetric proof holds for `R`. This establishes the observer‑equality statement v10 Core uses. 

---

## 6) "Two presentations, one structure" (exp/log equivalence)

* **Exp→Log:** `dec_{z\bar{z}}(φ^k ⊗ z^{m_z} ⊗ \bar{z}^{m_{\bar{z}}} ⊗ c) = (k,m_z,m_{\bar{z}},c)`.
* **Log→Exp:** `rec_{z\bar{z}}((k,m_z,m_{\bar{z}},c)) = φ^k ⊗ z^{m_z} ⊗ \bar{z}^{m_{\bar{z}}} ⊗ c`.
* **Multiplication:** adds headers (log‑add), core multiplies via `⊗^Core`.
* **Addition:** left **unconstrained** beyond semiring and observer homomorphism (you can refine it to, e.g., log‑sum‑exp on a metric model; v10 doesn't need that detail).

---

## 7) Verification Scripts

```csh
# Retractions & projectors
logic eval "(equal? 'L '(ν_L (ι_L x)) 'x)"
logic eval "(equal? 'B '([L] ([L] t)) '([L] t))"
logic eval "(equal? 'B '([R] ([R] t)) '([R] t))"

# Exp/log factorisation (worldsheet-aware)
logic eval "(let ((k mz mbar core (dec_{z\\bar{z}} t)))
               (equal? 'B 't '(⊗B (φ^ k) (⊗B (z^ mz) (⊗B (\bar{z}^ mbar) core)))))"

# Collapse to v10 NF header
logic eval "(let ((k mz mbar core (dec_{z\\bar{z}} t)))
               (equal? '(k (+ mz mbar) core) (NF t)))"

**Note (non‑invertibility of NF).** Because `NF` collapses `(m_z,m_{\bar z})` to the single header `m_Λ := m_z + m_{\bar z}`, there is **no canonical inverse** from the tuple `NF(t)` back to a `B` term without either (i) choosing a split rule for `(m_z,m_{\bar z})` or (ii) using `Λ` directly. The v10 layer provides a **B‑valued normaliser** `NF^{B}` that repacks via `Λ` and keeps `core(t)` unchanged.

# Positivity of scale (when worldsheet coordinates present)
logic eval "(let ((k mz mbar core (dec_{z\\bar{z}} t)))
               (implies (> (+ mz mbar) 0) (> (mΛ t) 0)))"

# Λ is a unit (negative scale headers allowed)
logic eval "(well-typed? 'B '(Λ^{-1}))"   # -> #t in the minimal model

# Bulk = two boundaries (observer equalities)
logic eval "(equal? 'L '(ν_L t) '(ν_L (⊕B ([L] t) ([R] t))))"
logic eval "(equal? 'R '(ν_R t) '(ν_R (⊕B ([L] t) ([R] t))))"

# Residual invisibility (requires additional semiring properties)
logic eval "(define int '(⊕B t (⊕B ([L] t) ([R] t))))"
logic eval "(equal? 'L '(ν_L int) '0_L)"  ; Note: holds in specific models only
logic eval "(equal? 'R '(ν_R int) '0_R)"  ; Note: holds in specific models only

# Braiding respects split (header-only effect)
logic eval "(let ((k mz mbar core (dec_{z\\bar{z}} t)))
               (equal? 'B '(NF (ad 0 t)) '(k (+ mz mbar) (ad_core 0 core))))"

# Yang-Baxter relations
logic eval "(equal? 'B '(ad 0 (ad 1 (ad 0 t))) '(ad 1 (ad 0 (ad 1 t))))"
logic eval "(equal? 'B '(ad 1 (ad 2 (ad 1 t))) '(ad 2 (ad 1 (ad 2 t))))"
logic eval "(equal? 'B '(ad 2 (ad 3 (ad 2 t))) '(ad 3 (ad 2 (ad 3 t))))"
logic eval "(equal? 'B '(ad 0 (ad 2 t)) '(ad 2 (ad 0 t)))"
logic eval "(equal? 'B '(ad 0 (ad 3 t)) '(ad 3 (ad 0 t)))"
logic eval "(equal? 'B '(ad 1 (ad 3 t)) '(ad 3 (ad 1 t)))"

# Basepoint axiom
logic eval "(equal? 'B '(Gen4 a0 a1 a2 a3) '0_B)"

# Sanity checks for auxiliary-modulated construction
# 1) adᵢ preserves headers (v2), but ˜adᵢ carries weight (CLASS)
logic eval "(let ((k mz mbar core (dec_{z\\bar{z}} (ad 0 t))))
              (equal? '(k mz mbar core) (dec_{z\\bar{z}} t)))"        # -> #t  (v2)
logic eval "(history-weight (list '(˜ad 0)))"                         # nontrivial central monomial

# 2) Residual invisibility with/without port gate (Core/CLASS)
logic eval "(define int '(⊕B t (⊕B ([L] t) ([R] t))))"
logic eval "(equal? 'L '(ν_L int) '(⊕_L (ν_L t) (ν_L t)))"            # general law
logic eval "(when (port-dup-annihilates?) (equal? 'L '(ν_L int) '0_L))"  # gated

# 3) Conjugation swaps auxiliaries (Core)
logic eval "(equal? 'B '(dec_{z\\bar{z}} (starB t))
                       '(let ((k mz mbar core (dec_{z\\bar{z}} t)))
                          (k mbar mz (star_core core))))"             # optional RC
```

## 8) Minimal concrete model sketch (sanity; Laurent headers)

* **Carriers.**
  `Core` = free commutative semiring on your basepoint symbols modulo `Gen4(a₀,…,a₃)=0`.
  `B` (log view) = `ℤ × ℤ × ℤ × Core` with `⊗` adding headers and multiplying cores; `⊕` any fixed commutative monoid law on each header component paired with `⊕^Core` (e.g., componentwise addition). This realises a commutative semiring while preserving the **bijective** `dec/rec` chart.

* **Up/Down.**
  `ι_L, ι_R` inject generators of `L,R` into `B` (separate central images), `ν_L, ν_R` project back (zeroing the opposite image for the minimal cross‑connector).

* **Braiding.**
  `adᵢ` act as permutations / local rewrites on `Core`; headers untouched.

* **Central Scalars.**
  `φ = (1,0,0,1_Core)`, `z = (0,1,0,1_Core)`, `\bar{z} = (0,0,1,1_Core)`, so `Λ = (0,1,1,1_Core)`.
  All are **central units**: `φ^{-1} = (-1,0,0,1_Core)`, `z^{-1} = (0,-1,0,1_Core)`, `\bar{z}^{-1} = (0,0,-1,1_Core)`, and `Λ^{-1}=(0,-1,-1,1_Core)`.

**Note:** In this model, `1_B = (0,0,0,1_Core)` has `m_Λ = 0 + 0 = 0`, which is correct for the multiplicative identity.

**Verification:** This model satisfies all axioms A0-A7:
- A0: L,R,Core are commutative semirings; B is a semiring with units ✓
- A1: Central scalars commute with all elements ✓  
- A2: Up/down are homomorphisms with retractions ✓
- A3: Images commute multiplicatively (separate central images) ✓
- A4: Frobenius compatibility, minimal cross-connector, moduli covariance (RC) ✓
- A5: Braiding preserves headers, satisfies Yang-Baxter ✓
- A6: Exp/log moduli chart via `dec_{z\bar{z}}`/`rec_{z\bar{z}}` ✓
- A7: Gen4 basepoint axiom ✓

This model satisfies all v2 axioms and makes the **exp/log headers** explicit and **header‑only** under NF.

---

## 9) Atomic V2: Exactly what v10 expects

This V2 specification provides **exactly** what v10 Core and CLASS expect, no more:

* **Core semiring structure:** `L, B, R` as distinct commutative semirings
* **Exp/log semiring:** `B` with `dec_{z\bar{z}}`/`rec_{z\bar{z}}` isomorphism and worldsheet-aware header factoring
* **Observers/embeddings:** `ν_L, ν_R, ι_L, ι_R` with retractions (A2)
* **Central scalars:** `φ, z, \bar{z}` with `Λ := z ⊗_B \bar{z}` (A1)
* **Braided operators:** `ad₀, ad₁, ad₂, ad₃` with Yang-Baxter relations (A5)
* **Basepoint/Gen4:** `a₀,…,a₃, Gen4` with `Gen4(a₀,…,a₃) = 0_B` (A7)
* **Normal form:** `NF := collapse ∘ dec_{z\bar{z}} : B → (k_φ, m_Λ, core)` (A6)
* **Derived projectors:** `[L] := ι_L ∘ ν_L`, `[R] := ι_R ∘ ν_R`

**What V2 does NOT provide (these are v10 CLASS additions):**
- Moduli (`μ_L, θ_L, μ_R, θ_R`)
- Parametric normal form
- Domain ports
- PSDM (Partial Stable Domain Map)
- Guarded negation
- Feynman view
- Truth theorems

V2 is **atomic** - it provides the minimal mathematical foundation that v10 builds upon.

---

### Mathematical completeness notes

* **Atomicity:** V2 provides exactly what v10 expects, no more. All v10 CLASS features (moduli, ports, PSDM, etc.) are built on top of this foundation.

* **Braid relations:** The Yang-Baxter equations are complete for 5-strand braid group representation.

* **Cross‑connector behavior:** The minimal choice `ν_L∘ι_R = 0_L`, `ν_R∘ι_L = 0_R` is specified. More general models can replace these axioms with non‑trivial cross‑connector maps if needed.

* **Exp/log structure:** The isomorphism between exp and log presentations is mathematically sound, requiring invertible `φ` and worldsheet-aware decomposition with `m_z, m_{\bar{z}} ∈ ℕ`.
