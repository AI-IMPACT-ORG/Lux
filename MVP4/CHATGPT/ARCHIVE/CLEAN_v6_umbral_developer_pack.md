
# CLEAN v6 — **Umbral Developer Pack** (BNF + Plan + Recipes)

This pack concretises the v6 Umbral Spec with grammar hints, algorithms, and “vacuum cookbook.” It is DRY: all semantics route through `NF`, `NF_{μ,θ}`, observers, and L‑arithmetic. Sources: v2 plan/spec. fileciteturn0file0 fileciteturn0file1

---

## A. BNF Adjunct (derived, no new primitives)

- **Reflection (defs):** `[L](t)=ι_L(ν_L t)`, `[R](t)=ι_R(ν_R t)`, `[μ,θ](t)=ι_L(ν_L(NF_{μ,θ} t))`.
- **Generating functional:** `Z[J]=⟨ ⊗B_{i∈I_fin}(1_B ⊕B ι_L(J_i)⊗B Obs(i)) ⟩_{μ,θ}`.
- **Umbral Δ and Sheffer:** `Δ_i` realised by the finite‑difference stencil in L; `S_n(i)=Δ_i^n Z|_{0}`.
- **Spectral objects:** `build-T`, `kernel-weight`, `cokernel-weight`, `trace-power`, `ζ_logic` (formal).

---

## B. Algorithms (right order)

1) **NF / NF_{μ,θ}.** As in v2; header‑only reweighting for the parametric step.
2) **Reflection → RNF.** Push `[·]` down; apply NF; eliminate gauges per `qmask`.
3) **Cumulants / Fisher / β.** Expand `Z[J]` (finite); run `ν_L∘NF_{μ,θ}`; build `G`, `T`, `β`, `a`, `c`.
4) **Umbral Δ.** Use forward or symmetric stencil; cache Δ‑tables per chart.
5) **Spectral layer.**
   - `T_x`: partial evaluate `V(x,•)`; wrap as L‑linear op on distributions.  
   - `ker/coker` weights: idempotent Gaussian over localized L; return monotone size.
   - `Tr_L(T^n)`: stochastic trace if numeric; exact if symbolic; truncate `ζ_logic`.
6) **Moduli.** `build-moduli!` runs M0..M2; `integrate-prepotential!` (when curls vanish); `discriminant`; `alpha-connection`; `ricci/scalar`.  
7) **Einstein–CLEAN & dS.** Compute `I_dS` at fixed points; set `Λ_mod`; monitor `E_{ij}`.

---

## C. Vacuum Cookbook

- **Tropical L (max,+).** Great for internal NP≠coNP via kernel–cokernel asymmetry. Fisher is degenerate; skip logic‑GRH runs here.
- **Log‑sum‑exp L (ℝ_{\u22650}, +,×).** Use for Fisher, α‑connections, logic‑GRH experiments; enable RC‑U5 self‑adjointness (metric‑compatible RG step).
- **Boolean L.** Diagnostic only (too coarse for geometry).

*Choice of `qmask`:* start with `(phase)`; include `scale` iff you want VEVs core‑only.  
*R‑data presets:* `'identity` (flat), `'triality-g2` (curved, octonionic flavor), `'quat`/`'complex` (degenerations).

---

## D. API Surface (delta from v5)

```racket
(choose-vacuum! #:L Lcar #:qmask m #:rdata M #:basepoint (list a0 a1 a2 a3)
                #:mu μ #:theta θ #:eps-mu εμ #:eps-theta εθ)
(set-observables! I_fin obs-list)

(delta i) (sheffer i n)

(build-T x) (kernel-weight T) (cokernel-weight T)
(trace-power T n) (zeta-logic T s #:order k)

(build-moduli!) (prepotential-exists!) (integrate-prepotential!)
(discriminant) (monodromy-step loop)
(alpha-connection α) (ricci) (scalar-curvature)
(desitter-invariant) (moduli-cosmological-constant)
```

---

## E. Missing‑detail traps & fixes

- **Integrability failures.** Use α‑connections directly; `Ψ` is optional. If curls are small but nonzero (numeric L), project to the closest integrable metric (least‑squares symmetrisation).
- **Localization failures.** Fall back to pseudo‑inverse rules local to a chart; signal “localized” status in the API.
- **Witness explosion in `T_x`.** Use sketching: random sparse `ρ` probes (Hutchinson) for `Tr(T^n)`; bound variance with Δ‑tables.
- **Threshold selection `τ`.** Calibrate with null instances; export `(calibrate-threshold! x-set)` helper.
- **Self‑adjointness (RC‑U5).** Enforce symmetric header updates: choose `f_θ,g_μ` s.t. step is the midpoint map; verify numerically `(⟨u,ℋv⟩−⟨ℋu,v⟩)≈0` under `g^F`.

---

## F. Sanity Tests (csh)

```csh
# Vacuum + chart
logic eval "(choose-vacuum! #:L 'logsumexp #:qmask '(phase) #:rdata 'identity
                            #:basepoint (list a0 a1 a2 a3) #:mu 0 #:theta 0
                            #:eps-mu 1e-3 #:eps-theta 1e-3)"
logic eval "(set-observables! '(0 1) (list '(ad 0 (gen4 a0 a1 a2 a3))
                                           '(ad 1 (gen4 a0 a1 a2 a3))))"
logic eval "(build-moduli!)"
logic eval "(fisher-matrix)"
logic eval "(prepotential-exists?)"
logic eval "(integrate-prepotential!)"
logic eval "(desitter-invariant)"

# Spectral zeta (toy)
logic eval "(define-verifier Vtoy)"
logic eval "(define Tx (build-T 'x0))"
logic eval "(trace-power Tx 1)"
logic eval "(zeta-logic Tx 's #:order 8)"
```

---

*End — Umbral Developer Pack (v6).*
