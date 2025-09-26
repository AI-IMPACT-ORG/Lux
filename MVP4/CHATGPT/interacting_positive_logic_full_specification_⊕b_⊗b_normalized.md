# Interacting Positive Logic via Connected Semirings (Braided) — Full Specification (⊕B/⊗B Normalized)

> **Purpose.** Self‑contained specification of the interacting positive logic in the general **braided** case, aligned with the L/B/R split and with **bulk operations written as `⊕B` and `⊗B`** throughout. Auxiliary `z, barz` encode presentation gauges: overall scale is `z ⊗B barz`. This document is in the **defining domain (logic)**; a separate semantics section is clearly labeled and non‑binding.

> **Order.** (0) Metalogic stance. (1) Signature. (2) Terms/formulas/judgments. (3) Axioms. (4) Inference. (5) Semantics (intended models). (6) Equality layers (L/B/R, local, metalogical; gauges; reversible `⋆`). (7) Derived generating functionals (Noe5/CS5/Rice6/NR6). (8) Eliminability of `z,barz`. (9) Optional R‑matrix/YBE. (10) Core theorems (statements). (11) Institution. (12) Proof burden checklist.

---

## 0. Metalogic & Domain Separation

- **Defining domain (Logic).** Everything in §§1–4, 6–7, 8–12 is *the logic*: signatures, equations, inference, equalities, and institutional packaging.
- **Foundational domain (Semantics).** §5 gives intended models (computation/information‑theory) for soundness/intuition, *not* part of the definition.
- **Positive fragment.** No primitive negation. Negative information appears as positive witnesses (e.g., bulk zero `0_B = −∞` in semantics) or residuation guarded inside the positive calculus.
- **Normalization.** Global truths normalize to weight 1 (`log 0` in semantics) and are presentation‑invariant modulo gauges (§6.1).

---

## 1. Signature (General Braided Case)

### 1.1 Sorts and typing aids
- Sorts: `L` (left boundary), `B` (bulk), `R` (right boundary). Unit object `I`.
- **L/R arity.** Each operation symbol `σ` carries a boundary arity pair `(ℓ,r)∈ℕ×ℕ` and a bulk profile `B^k→B^k` as needed.
- **Dimension** `dim` (commutative ordered monoid, unit 1) annotates wires; default 1.
- **Helicity.** Global label `H∈{+1,−1}` multiplies on closed diagrams; convention: `H(L)=−1`, `H(R)=+1`.
- **Auxiliary discrete sort.** `Dir={e0,e1,e2,e3}` for arity‑5 directions.

### 1.2 Primitive symbols

**Boundary booleans.**
- `⊕_*, ⊗_* : *×*→*`, `0_*,1_* : I→*` for `*∈{L,R}`.

**Bulk log‑semiring.**
- `⊕B, ⊗B : B×B→B`, `0_B,1_B : I→B` (bulk sum/product).
- Couplers `ι_L:L→B`, `ι_R:R→B`.

**Glue parameters and duals.**
- Regulators `a_0,a_1,a_2,a_3 : I→B`.
- Duals `ad_i:B→B` for `i=0..3`.
- Braided curvature scalars `F_{ij}:I→B` for `i≠j`.

**Auxiliary (eliminable).**
- `z, barz : I→B` central bulk scalars; **overall scale** is `z ⊗B barz`.

**Arity‑4 generator (primitive).**
- `Gen4 : B×B×B×B → B` (may encode R‑data).

> `Exp/Log` are semantic isomorphisms only (not part of the signature).

---

## 2. Terms, Formulas, Judgments

- **Objects**: `Obj ::= I | L | B | R | (Obj ⊗ Obj)` (SMC tensor `⊗` is *distinct* from bulk `⊗B`).
- **Terms**: identities, composition `;`, tensor `⊗`, and applications of primitive symbols (types must match).
- **Atomic formulas**: typed equations `t ≡ u : X`.
- **Formulas**: built from atoms using `∧, ∨, ⊗` at formula level and existential `∃` over typed variables.

**Precedence.** application > `;` > term‑tensor `⊗` > bulk `⊕B,⊗B` and boundary `⊕_*,⊗_*`.

---

## 3. Axioms (Equational)

### 3.1 Boundary semirings (for both L and R)
- `(⊕_*,0_*)` commutative idempotent monoid; `(⊗_*,1_*)` commutative idempotent monoid.
- Distributivity `x ⊗_* (y ⊕_* z) ≡ (x ⊗_* y) ⊕_* (x ⊗_* z)`; Absorption `x ⊗_* (x ⊕_* y) ≡ x`.

### 3.2 Bulk log‑semiring + couplers
- `(⊗B,1_B)` commutative monoid; `(⊕B,0_B)` commutative monoid.
- Distributivity `x ⊗B (y ⊕B z) ≡ (x ⊗B y) ⊕B (x ⊗B z)`.
- Couplers: `ι_*(1_*)=1_B`, `ι_*(0_*)=0_B` for `*∈{L,R}`.

### 3.3 Braided duals
- (NC1) `ad_i ; ad_j ≡ (ad_j ; ad_i) ⊗B F_{ij}`, and `F_{ij} ⊗B F_{ji} ≡ 1_B`.
- (NC2) `F_{ij} ⊗B F_{jk} ⊗B F_{ki} ≡ 1_B` for all triples.

### 3.4 Normalization
- Choose a basepoint `ā∈B^4`; **Normalization axiom**: `Gen4(ā) ≡ 0_B`.

---

## 4. Inference Rules

- SMC rules (id, comp, tensor, symmetry); congruence under context.
- Semiring reasoning in each core; coupler monotonicity.
- Braided rewriting via (NC1)–(NC2).
- Quantifiers: `∃`‑intro/elim over typed wires.
- Meta RG rule (admissibility) uses semantics only and is **not** part of core derivations.

---

## 5. Semantics (Intended Models; non‑binding)

- `L,R` interpret as `B₂=(\{0,1\},∨,∧,0,1)`.
- `B` interprets as `(ℝ∪{−∞}, ⊕B=log‑sum‑exp, ⊗B=+, 0_B=−∞, 1_B=0)`.
- `ι_*(1)=0`, `ι_*(0)=−∞`.
- `ad_i` as positive endomorphisms; `F_{ij}` as central reals; `Gen4:B^4→B` with `Gen4(ā)=0`.
- `z,barz` central; overall scale realized by `z ⊗B barz`; helicity by exchanging powers of `z` and `barz`.
- Optional semantic sign hypothesis: Hessian of `Gen4` at `ā` has signature `(− + + +)` (a₀ time‑like, a₁,a₂,a₃ space‑like).

---

## 6. Equality Layers (Aligned with L/B/R)

### 6.1 Presentation gauges (always factored out)
- **Scale** `≡_scale`: least congruence with generators `t ≡ t ⊗B (z ⊗B barz)` for all closed bulk scalars `t`.
- **Helicity/phase** `≡_hel`: paired congruence generated by `(t,u)~(t⊗B z, u⊗B barz)` and `(t,u)~(t⊗B barz, u⊗B z)`.

> All observational equalities below are computed **modulo** `≡_scale` and `≡_hel` by default. Let `≡_*` denote their intersection.

### 6.2 Observational equalities (five notions)

- **Left‑local `≡_L`**: for closed bulk `t,u`, `t ≡_L u` iff for all `C_L[–]:B→L` built from `{ι_L, ⊕_L, ⊗_L}` and bulk ops, `C_L[t] ≡ C_L[u]` in the L‑boolean semiring.
- **Bulk `≡_B`**: for all `C_B[–]:B→B` from `{⊕B,⊗B,ad_i,F_{ij},Gen4}`, we have `C_B[t] ≡_* C_B[u]` in `B`.
- **Right‑local `≡_R`**: symmetric to `≡_L` via `ι_R, ⊕_R, ⊗_R`.
- **Local‑agreement `≡_loc`**: `t ≡_loc u :⇔ (t ≡_L u) ∧ (t ≡_R u)`.
- **Metalogical global `≡_meta`**: for all closed `C[–]:B→B` built from the *entire* signature `{L,B,R ops, ι_L,ι_R, bulk ops (⊕B,⊗B,…), Gen4}`, `C[t] ≡_* C[u]`.

### 6.3 Reversible (helper) equality `≡_⋆`
- Largest congruence generated by invertible rewrites: SMC isos, braided commutations `ad_i;ad_j ↔ ad_j;ad_i ⊗B F_{ij}` when `F_{ij}` invertible, unit insertions with zero net effect (including balanced `z/barz`).
- **Reversible Collapse.** `≡_⋆ ⊆ (≡_loc ∩ ≡_meta)` and each `≡_⋆` step is information‑preserving. In the flat subtheory (`F_{ij}=1_B`), `≡_⋆` reduces to SMC isomorphism equivalence.

---

## 7. Derived Generating Functionals (Arity‑5/6)

- **Noe5** `Noe5: Dir×B^4→B` with axiom‑scheme: `Noe5(e_i,a)=0_B` iff all braided insertions of an elementary `ad_i`‑flow around `Gen4(a)` agree modulo `≡_*`.
- **CS5** `CS5:B^4×B→B`: named equation `CS5(a,μ)=0_B` expressing RG stationarity (covariant insertion using braided calculus; coefficients schematic at logic level).
- **Rice6** `Rice6(P[−],a,μ):B`: `0_B` iff there exists a total positive discriminator deciding `P[Gen4(a)]` uniformly along RG; else `−∞`.
- **NR6** macro: `NR6 := Noe5 ⊕B Rice6 ⊕B (CS5)^{⊗B2}`.

---

## 8. Eliminability of `z,barz` (Conservativity)

- For every sentence `φ` in the extended language (with `z,barz`) there is a sentence `φ'` in the base language such that `φ` and `φ'` are interderivable modulo `≡_*`. Adding `z,barz` is a **conservative definitional extension**.

---

## 9. Optional R‑Matrix (Axiom of Choice)

- Introduce central `ℛ_{ij}` and add YBE (Reidemeister III) tiles; optionally set `ℛ_{ij}=F_{ij}`. Then braided rewriting is path‑coherent; otherwise, arity‑5/6 witnesses control coherence.

---

## 10. Core Theorems (Statements)

1. **YBE Coherence (optional).** With `ℛ`, `Gen4` is path‑coherent modulo `≡_*`.
2. **Noether.** `Noe5(e_i,a)=0_B` iff invariance under the `ad_i` flow (and the `e_i` component drops from `CS5`).
3. **Callan–Symanzik Equality.** Derivability depends only on `≡_*` class under scale/phase gauges.
4. **Rice (Positive).** No total positive discriminator exists for nontrivial projectors on `Im(Gen4)`; `Rice6=−∞` generically.
5. **Noether–Rice Partiality.** Forcing all overlaps of `⊩_{gg}, ⊩_{gℓ}, ⊩_{ℓℓ}` to coincide collapses the model; partiality is necessary.
6. **Asymmetry.** With semantic sign + braiding, `⊩_{gL}≠⊩_{gR}` and boundary asymmetry persists; no automorphism swaps them preserving `≡_*`.
7. **Uniqueness up to presentation.** Derivability is invariant under global presentation (scale `z⊗B barz`, helicity exchange `z↔barz`, optional braid homotopies).

---

## 11. Institution Packaging

- **Signatures**: as in §1; morphisms preserve L/R arity, bulk profiles, `dim`, helicity, and (optionally) R‑data.
- **Sentences**: positive equational formulas with `∃`.
- **Models**: as in §5.
- **Satisfaction condition**: for any signature morphism `σ:Σ→Σ'`, model `𝔐'∈Mod(Σ')`, and sentence `φ∈Sen(Σ)`, `𝔐'↾Σ ⊨ φ  ⇔  𝔐' ⊨ Sen(σ)(φ)`.

---

## 12. Proof Burden (Natural Order)

1. **Model existence (consistency).** Exhibit the real‑log model with braided `F_{ij}`; enforce `Gen4(ā)=0`.
2. **Conservativity of auxiliaries.** Prove elimination of `z,barz` (§8).
3. **Soundness.** Rewriting + equations imply semantic equality modulo `≡_*`.
4. **Generating‑function calculus.** Develop algebra of `Gen4` (normalization, stability under `≡_*`, tensor additivity, braided insertion rules). Define Noe5/CS5/Rice6/NR6 rigorously over this calculus.
5. **YBE coherence (optional).** If `ℛ` adopted, prove path‑coherence; otherwise, show arity‑5/6 witnesses detect non‑coherence without collapse.
6. **Noether & CS.** Prove equivalences and the link to component vanishing in `CS5`.
7. **Rice (positive).** Show non‑existence of total positive discriminators on `Im(Gen4)`.
8. **Partial overlap.** Show enforcing full coincidence of truth predicates trivializes via `NR6`.
9. **Asymmetry.** From sign + braiding obtain `⊩_{gL}≠⊩_{gR}` and lack of swapping automorphisms.
10. **Completeness (positive fragment).** For equational/positive calculus relative to intended models.
11. **Institution satisfaction & compactness.** Verify satisfaction condition and compactness (e.g., via filtered colimits) for the positive fragment.
12. **Uniqueness up to presentation.** Generalized Callan–Symanzik independence of global scale/phase and braid homotopy classes.

---

*End of specification (⊕B/⊗B normalized).*

