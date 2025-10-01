
# CLEAN v10 — **CLASS** (Complete Language Spec)
**Dependent on four core moduli and two auxiliary moduli**

> A programming-language style specification layered on the v10 Core.  
> **Four core moduli:** \( μ_L, θ_L, μ_R, θ_R \) (left/right scale & phase flows).  
> **Two auxiliary moduli:** \( z, \bar z \) (define \(Λ := z ⊗_B \bar z\)).  
> This file adds: **guarded negation**, **domain ports** (Boolean/RAM, λ‑calc, info‑flow, non‑susy QFT), **PSDM** (irreversibility), **Feynman** view, and **integration tests** (“truth theorems”).

---

## 0) Dependencies & minimality

- Builds on **v10 Core** (triality, boundary sum, cumulants) and thus on the **v2 base** (no new axioms; all additions are **definitions** or **model RCs**).  
- Minimal to **internalise its own compiler generator**: encodings TM↔λ via the generating functional; PSDM yields partial/irreversible semantics; guarded negation yields local NAND.  
- Avoids collapse to known models: irreversibility is confined to PSDM/domain; global logic remains constructive.

---

## 1) Moduli, parameters, and flows

**Core moduli (4):** \( μ_L, θ_L, μ_R, θ_R \in L \).  
**Auxiliary (2):** \( z, \bar z \in B \) with \(Λ := z ⊗_B \bar z\).  
**Other parameters:** `qmask` (default `(phase)`), R‑data preset (e.g., `identity`, `triality-g2`).

### 1.1 Boundary‑aware parametric NF
Let `NF(t)=(kφ, mΛ, core)`. Define local headers:
\[
k^L_\phi := \mathrm{phase}(\mathrm{NF}([L]t)), \quad
k^R_\phi := \mathrm{phase}(\mathrm{NF}([R]t)), \quad
m^L_\Lambda := \mathrm{scale}(\mathrm{NF}([L]t)), \quad
m^R_\Lambda := \mathrm{scale}(\mathrm{NF}([R]t)).
\]
Then the **four‑moduli parametric normaliser** is
\[
NF_{μ_L,θ_L, μ_R,θ_R}(t) := \big( f_{θ_L}(k^L_\phi) ⊕ f_{θ_R}(k^R_\phi),\; g_{μ_L}(m^L_\Lambda) ⊕ g_{μ_R}(m^R_\Lambda),\; core(t) \big)
\]
with `⊕` the header recombination (default = integer addition for phase exponent, natural addition for scale).

**Flow compatibility (RC):** \( f_{θ_1⊕θ_2}=f_{θ_2}\circ f_{θ_1} \) and \( g_{μ_1⊕μ_2}=g_{μ_2}\circ g_{μ_1} \) for each boundary (semigroup law).

---

## 2) Guarded negation (local NAND; global constructivity)

For any **guard** \(g\in L\) define the principal ideal \(↓g=\{x\le g\}\).  
**RC‑GN:** a **relative complement** \(g⊖_L x\) exists on \(↓g\). Define guarded negation \(¬^g(x):=g⊖_L x\).  
Then \( \mathrm{NAND}(x,y) := ¬^g(x ⊗_L y) \) gives **local computational universality** without global classical negation.

---

## 3) Domain ports (internally maximally coherent)

A **domain port** \( \mathsf{Port} \) is a (partial) interpretation of carriers & constructors that **commutes** with core definitional machinery (NF, observers, cumulants, Δ) and respects truncation and regulator limits.

### 3.1 Boolean/RAM port (irreversible computing)
- **Carrier:** \(L_0 = \{0,1\}\) or \( \mathbb R_{\ge 0}\) with threshold.  
- **Encoding:** programs as `Obs` and transitions as micro‑steps; acceptance via \(ν_L ∘ NF\).  
- **PSDM:** partial, stable; defined iff program halts within regulator window; otherwise **undefined**.
- **Coherence:** TM and λ encodings produce identical \(Z[J]\) upstairs; port sees the same Boolean outcome (Church–Turing inside).

### 3.2 λ‑calculus port
- **Carrier:** normal forms in a typed λ‑fragment; β‑steps as micro‑steps; evaluation via expectations.  
- **PSDM:** defined iff β‑normalises in the regulator; undefined otherwise.

### 3.3 Info‑flow port (irreversible information)
- **Carrier:** preorders/lattices; `⊕_L` joins, `⊗_L` flows; guarded negation yields relative complement; PSDM drops non‑flow paths.

### 3.4 Non‑susy QFT port (Euclidean/Minkowski)
- **Carrier:** \(L_E=\mathbb R_{\ge0}\) (Euclidean) or \(L_M=\mathbb C\) (Minkowski).  
- **Feynman view:** histories from micro‑steps; action = product of header weights; amplitudes via domain evaluation; propagator = inverse Fisher; vertices = cumulants.

All ports **reuse the same core pipeline**; coherence is by construction.

- **Minimal obligation (definitional).** A port \(\mathsf{Port}\) fixes a **carrier** and supplies a **transition** \(\llbracket K \rrbracket_{\mathsf{Port}}\) for its kernel on that carrier. It must respect header‑only \(NF_{μ_*,θ_*}\) and **RC–ME** (residual invisibility); no identification of bulk residual with boundary data is permitted.

---

## 4) PSDM (Partial Stable Domain Map) — irreversible semantics

A **PSDM** \( \mathcal D^\sharp \) is:
1) **total** on each regulated fragment; commutes with NF/Δ/cumulants to truncation,  
2) **stable** under regulator inclusions,  
3) **partial** in the direct limit (undefined on non‑total instances),  
4) **continuous** when RG is contractive.

This realizes **irreversible computation** cleanly while the **global logic remains constructive**.

*A practical hook:* each **domain port** furnishes the kernel's **transition** via its PSDM instance on the chosen carrier; totality/partiality and regulator behaviour remain exactly as specified here.

---

## 5) Feynman / Sum‑over‑Histories (class façade)

- **Histories:** sequences of allowed micro‑steps (ad‑rewrites) consistent with sources.  
- **Step weight:** header change at each step; **action** = product along the path.  
- **Partition function:** `Z[J] = ⊕_{H} S(H)` equals the core `Z[J]` by definition.  
- **Schwinger–Dyson:** \( ⟨Δ_i F⟩ = 0 \) (umbral integration by parts).  
- **Duality:** mid‑grade reflection implements the `z↦1−z` flavor along boundary flows.

- **Equivalence (definitional).** With \(K\) the micro‑step kernel, the "sum over histories" is the **truncated Green's sum** \(G_N=\bigoplus_{n=0}^N K^n\); cumulants and Schwinger–Dyson identities are unchanged and evaluate observers of \(G_N\) exactly as in the core layer.

---

## 6) Truth theorems (integration tests)

1) **Bulk = Two Boundaries (observer equality).** For all `t`,
   \( ν_*(t) = ν_*([L]t ⊕_B [R]t) \) for `*∈{L,R}` (core theorem; already unit‑tested).

2) **Umbral–Renormalisation (Δ commutes with NF).** Δ‑operators generated by finite differences commute with `NF_{μ_*,θ_*}`; cumulants are scheme‑stable.

3) **Church↔Turing inside CLEAN.** TM and λ encodings yield the same `Z[J]` and hence identical expectations; under any PSDM the halting/normalising outputs agree (partial equality).

4) **EOR (each object represented once).** With header/core/ braid faithfulness, the (P)SDM/domain map is injective on objects modulo mask; no aliasing.

5) **logic‑ζ critical‑line equivalence (internal).** Fisher self‑adjoint RG generator ⇔ kernel–cokernel balance at stationary moduli ⇔ zeros on the Fisher‑critical line. (Ported to QFT port as functional‑equation symmetry to truncation order.)

---

## 7) Racket folder structure (suggested)

```
clean/
  core/
    signature.rkt          ; sorts, ops, params, qmask, R-data
    axioms.rkt             ; v2 axioms (equational)
    nf.rkt                 ; header/core normaliser
    observers.rkt          ; ι, ν, [L],[R], reconstitution ρ
    triality.rkt           ; starB/starL/starR; triality functors
    cumulants.rkt          ; Z[J], g, G, β, a, c; Δ-ops
    tests/
      unit-core.rkt        ; the csh-style tests below translated
  class/
    moduli.rkt             ; μ_L, θ_L, μ_R, θ_R, z, barz; NF_{…}
    guarded.rkt            ; guarded negation & NAND library
    psdm.rkt               ; partial stable domain map machinery
    feynman.rkt            ; histories, weights, sum, SD identities
    domain/
      boolean/port.rkt
      lambda/port.rkt
      infoflow/port.rkt
      qft/port.rkt
    tests/
      integ-truths.rkt     ; the 5 “truth theorems” checks
  tooling/
    repl.rkt
    codegen/
      agda.rkt coq.rkt metamath.rkt
```

---

## 8) Public API (Racket‑style façade)

```racket
;; --- core (re-exported) ---
(set-quotient-mask! m)
(set-r-matrix! M)
(normal-form t)                         ; -> kφ mΛ core
(reflect 'L t) (reflect 'R t)
(reconstitute t)                        ; -> ρ(t) = [L]t ⊕B [R]t
(register-observable i term)
(value g i) (value G i j) (value beta-μ i) (value beta-θ i) (value a) (value c)

;; --- moduli & flows (four core + two aux) ---
(set-moduli! #:μL μL #:θL θL #:μR μR #:θR θR #:z z #:barz barz)
(normal-form-4mod t)                    ; NF_{μL,θL,μR,θR}

;; --- guarded negation (local NAND) ---
(set-guard! g)                          ; choose guard g ∈ L
(gn-not x)                              ; ¬^g(x)
(gn-nand x y)                           ; NAND

;; --- PSDM ---
(define-psdm! #:L-map DL #:B-map DB #:R-map DR
              #:totality halts? #:valuation w #:minkowski? #f)
(psdm-apply t) (psdm-defined? t)

;; --- Feynman façade ---
(histories J) (history-weight H) (sum-over-histories J)
(schwinger-dyson i F)

;; --- domain ports ---
(port-boolean) (port-lambda) (port-infoflow) (port-qft)
```

---

## 9) Unit tests (CLASS, a selection)

```csh
# -- Moduli setup (four core + two aux) --
logic eval "(set-moduli! #:μL 0 #:θL 0 #:μR 0 #:θR 0 #:z z0 #:barz zb0)"

# Boundary-aware NF acts header-only, per side
logic eval "(define t '(⊗B (ad 0 (gen4 a0 a1 a2 a3)) (ad 1 (gen4 a0 a1 a2 a3))))"
logic eval "(normal-form-4mod t)"

# Guarded NAND yields XOR via 3 NAND gates (local universality smoke)
logic eval "(set-guard! 1_L)"
logic eval "(define X '(ι_L 1_L)) (define Y '(ι_L 1_L))"
logic eval "(gn-nand X (gn-nand X Y))"   # etc. — check truth table by a PSDM boolean port

# PSDM partiality: undefined on non-halting
logic eval "(define-psdm! #:L-map 'bool #:B-map 'circuits #:R-map 'bool #:totality 'halts? #:valuation 'degree)"
logic eval "(psdm-defined? '(encode-nonhalting))"       # -> #f

# Feynman = cumulant expansion
logic eval "(sum-over-histories '(J0))"
logic eval "(value g 0)"

# Truth theorem checks
; (1) bulk = two boundaries (already in core tests)
; (2) Δ commutes with NF (scheme stability)
logic eval "(check-umbral-renormalisation?)"             # should pass on chart
; (3) Church↔Turing inside
logic eval "(church-turing-agree? 'progP 'inputX #:truncate 6)"  # -> #t
; (4) EOR
logic eval "(eor-health? #:header #t #:core #t #:braid #t #:symbols #t)"      # -> #t
; (5) logic-ζ critical-line (internal)
logic eval "(logic-grh-gate? #:fisher-self-adjoint? #t #:truncate 8)"         # -> #t

# Non-normative: Feynman == Green's sum to truncation
logic eval "(equal? 'L '(sum-over-histories J :N 4) '(observer-L (greens-sum K 4)))"  # -> #t
```

---

## 10) Minimality & non-collapse

- **Minimal:** only the four core moduli & two auxiliaries are added to v10 Core; guarded negation lives in **locals** only; PSDM carries irreversibility; Feynman is a definitional façade.  
- **Non‑collapse:** each domain port is a map, not an identification; **EOR** prevents aliasing; global logic remains constructive and triality‑based; Boolean/QFT/info‑flow semantics live **in the ports**, not in the core.

*End CLASS.*
