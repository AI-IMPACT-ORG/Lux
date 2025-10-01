
# CLEAN v7 — **Umbral Domain Map Developer Pack**

Actionable recipes for domain alignment, regulators, truncation, and duality. Base semantics and NF/observer details are inherited from the v2 spec. fileciteturn0file1 fileciteturn0file0

---

## A. Domain map recipes

**Goal:** implement `𝒟_L, 𝒟_R, 𝒟_B` as homomorphisms so the entire pipeline (`NF_{μ,θ}`, `ν_L`, Δ, cumulants, traces) commutes.

- **Numeric carriers:** `L₀=ℝ_{\ge0}` or `ℂ`; send `⊕_L,⊗_L` to `+,×`.  
- **Valuation/grading `w`:** total umbral degree or header‑weighted degree `w(kφ,mΛ,deg_J)=α|kφ|+β mΛ+γ deg_J`.  
- **Trace:** implement Hutchinson‐type randomized trace for `T^n` when `L₀` is numeric; or use exact combinatorial trace when `B₀` is symbolic.

**Checklist (TC/Alignment):**
1. `𝒟` preserves units and semiring ops.  
2. `𝒟` respects retractions: `𝒟(ν_*;ι_*)=id`.  
3. `𝒟(φ), 𝒟(Λ)` central; their valuations match `w`.  
4. Test **Truncation Compatibility**: `domain-truncate-commutes?` must return `#t` on the chosen `w`.

---

## B. Regulators (finite models)

- Degree cutoff `N_J`: prune monomials in the umbral sources beyond degree.  
- ad‑depth cutoff `N_ad`: bound rewrite depth to avoid braid blow‑ups.  
- Header bounds `(K,M)`: keep `|kφ|≤K`, `0≤mΛ≤M`.

Provide canonical embeddings for `ℛ≤ℛ′`. Implement `remove-regulator!` as a **direct limit** routine that checks contractivity of `(f_θ,g_μ)` under `w`.

---

## C. Duality `z ↦ 1−z` (logic upleft)

- Implement `S` as a *mid‑grade reflection* on `w`: `S:deg↦(c−deg)` for fixed center `c`.  
- Choose header flow `(f_θ,g_μ)` so that `S` corresponds to `(θ↦−θ, μ↦μ)` up to units.  
- Verify numerically that `Z[J^∨] ≍ K ⊗_L Z[J]` and, after `𝒟`, that the domain functional equation holds **to truncation order N** (by TC).

---

## D. Conservative extension posture (pragmatic)

- Treat **RC‑CONS** as a switch in your model; it asserts that the ZFC fragment embedded via `𝒟` is **conservative**.  
- Engineering stance: all new constructs are *macros* (definitions) atop v2; no new binders, no new axioms. This keeps the door open for conservativity proofs while you iterate.

---

## E. Failure modes & fixes

- **TC fails:** adjust valuation `w` so header units have degree 0; or extend `𝒟` to record weights explicitly.  
- **Noncontractive RG:** keep regulator on; report dependence on `(f_θ,g_μ)`; do not call `remove-regulator!`.  
- **Trace instability:** increase truncation order gradually; switch to exact combinatorial traces on small charts.  
- **Braiding mismatch:** align `𝒟(F_{ij})` with the chosen R‑data; otherwise alignment lemma (A4) can fail.

---

## F. Minimal test plan

1. **Alignment smoke:** `domain-truncate-commutes?` true for `N=1..4`.  
2. **Duality:** `Z[J^∨] / Z[J]` is header‑unit to `O(N)` after domain map.  
3. **RG limit:** with contractive `(f_θ,g_μ)`, `Z^{(ℛ)}→Z` in umbral and in domain.  
4. **Spectral:** first 6 coefficients of `ζ_logic` match domain traces to truncation order.

---

*End — Developer Pack (v7).*
