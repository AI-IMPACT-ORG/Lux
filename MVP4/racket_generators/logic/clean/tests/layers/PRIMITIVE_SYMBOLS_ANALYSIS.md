# CLEAN Framework: Primitive Symbols and Axioms Analysis

**Date:** $(date)  
**Purpose:** Comprehensive analysis of what is defined in terms of what in the CLEAN framework

## 🎯 **Primitive Symbols (v2 Base)**

### **1. Sorts/Objects:**
- `I` (unit)
- `L` (left boundary)  
- `B` (bulk)
- `R` (right boundary)

### **2. Boundary Semiring Operations:**
- `⊕_L, ⊗_L : L×L→L` (left boundary operations)
- `⊕_R, ⊗_R : R×R→R` (right boundary operations)
- `0_L, 1_L : I→L` (left boundary constants)
- `0_R, 1_R : I→R` (right boundary constants)

### **3. Bulk Semiring Operations:**
- `⊕B, ⊗B : B×B→B` (bulk operations)
- `0_B, 1_B : I→B` (bulk constants)

### **4. Couplers/Observers:**
- `ι_L : L→B` (left injection)
- `ι_R : R→B` (right injection)
- `ν_L : B→L` (left projection)
- `ν_R : B→R` (right projection)

### **5. Braiding/Curvature:**
- `ad_0, ad_1, ad_2, ad_3 : B→B` (braiding operations)
- `F_{ij} : I→B` (central scalars for i≠j)

### **6. Central Scalars (Gauges):**
- `φ, barφ : I→B` (phase gauges)
- `z, barz : I→B` (scale gauges)

### **7. Arity-4 Generator + Basepoint:**
- `a_0, a_1, a_2, a_3 : I→B` (basepoint constants)
- `Gen4 : B×B×B×B→B` (arity-4 generator)

## 🔬 **Core Axioms (v2 Base)**

### **1. Boundary Semiring Axioms:**
```
(⊕_L, 0_L) forms a commutative idempotent monoid
(⊕_R, 0_R) forms a commutative idempotent monoid
(⊗_L, 1_L) forms a commutative idempotent monoid  
(⊗_R, 1_R) forms a commutative idempotent monoid
```

### **2. Bulk Semiring Axioms:**
```
(⊕B, 0_B) forms a commutative monoid with annihilating 0_B
(⊗B, 1_B) forms a commutative monoid
⊗B distributes over ⊕B
```

### **3. Observer Axioms:**
```
ν_L;ι_L = id_L (left observer retracts left injection)
ν_R;ι_R = id_R (right observer retracts right injection)
```

### **4. Basepoint Axiom:**
```
Gen4(a_0, a_1, a_2, a_3) = 0_B
```

### **5. Braiding Axioms:**
```
ad_i commute up to central F_{ij}
```

### **6. Gauge Axioms:**
```
φ ⊗B barφ ≡ 1_B (phase gauge)
Λ := z ⊗B barz (scale gauge)
```

### **7. Residual Invisibility:**
```
Residual bulk is invisible to observers
```

## 🎯 **Derived Operations (v10 Core)**

### **1. Triality Operations (Derived):**
- `starB : B→B` (bulk conjugation)
- `starL : L→L` (left conjugation)  
- `starR : R→R` (right conjugation)

### **2. Projectors (Derived):**
- `[L](t) := ι_Lν_L(t)` (left projector)
- `[R](t) := ι_Rν_R(t)` (right projector)
- `[μ,θ](t) := ι_Lν_L(NF_{μ,θ}(t))` (parametric projector)

### **3. Triality Functors (Derived):**
- `T_L(t) := ν_L(t)` (bulk→left)
- `T_R(t) := ν_R(t)` (bulk→right)
- `T_B(x_L,x_R) := ι_L(x_L) ⊕B ι_R(x_R)` (boundaries→bulk)

### **4. Normal Form (Derived):**
- `NF(t) = (kφ:ℤ, mΛ:ℕ, core(t))` (header/core decomposition)
- `NF_{μ,θ}(t) := (f_θ(kφ), g_μ(mΛ), core(t))` (parametric NF)

## 🔬 **Guarded Negation (CLASS Extension)**

### **1. Primitive Notion:**
- **Guard**: `g ∈ L` (element of left boundary)
- **Principal Ideal**: `↓g = {x ∈ L | x ≤ g}` (domain of guarded negation)

### **2. Definition (Not Primitive):**
```
¬^g(x) := g ⊖_L x  (relative complement on ↓g)
```

### **3. NAND Definition (Not Primitive):**
```
NAND(x,y) := ¬^g(x ⊗_L y)
```

### **4. Regularity Condition (RC-GN):**
```
A relative complement g ⊖_L x exists on ↓g
```

### **5. Implementation Details:**
- **Partial Map**: `¬^g(x)` is undefined for `x > g`
- **Guard Selection**: `g = max{n ∈ ℕ : n² ≤ Λ}` (framework-native)
- **Universality**: Through guard selection, not guard constraint

## 🔬 **Domain Maps (CLASS Extension)**

### **1. Definition (Not Primitive):**
A **domain map** `𝒟 = (𝒟_L, 𝒟_B, 𝒟_R)` is a family of semiring homomorphisms to classical carriers.

### **2. Regularity Conditions (RC-D):**
- **RC-D0**: `𝒟_B∘ι_* = ι_*^0∘𝒟_*`, `ν_*^0∘𝒟_B = 𝒟_*∘ν_*`
- **RC-D1**: Headers map to central units compatible with valuation `w`
- **RC-D2**: `𝒟(ad_i∘ad_j) = 𝒟(ad_j∘ad_i)⋅𝒟(F_{ij})`
- **RC-D3**: Observers erase phase (and masked scale) after mapping
- **RC-D4**: `𝒟(Cut_{≤N} Z) = Cut_{≤N}^{(0)}(𝒟(Z))`
- **RC-D5**: `𝒟` is continuous along regulator limits

### **3. PSDM (Partial Stable Domain Maps):**
- **Definition**: Partial domain maps supporting irreversible computation
- **Implementation**: `psdm-legacy` struct with hash table
- **Operations**: `psdm-apply`, `psdm-defined?`, `psdm-lookup`

## 🎯 **Moduli System (CLASS Extension)**

### **1. Core Moduli (4):**
- `μ_L, θ_L, μ_R, θ_R ∈ L` (left/right scale & phase flows)

### **2. Auxiliary Moduli (2):**
- `z, barz ∈ B` with `Λ := z ⊗_B barz`

### **3. Flow Compatibility (RC):**
```
f_{θ_1⊕θ_2} = f_{θ_2}∘f_{θ_1}
g_{μ_1⊕μ_2} = g_{μ_2}∘g_{μ_1}
```

## 🔬 **What is Defined in Terms of What**

### **1. Primitive (v2 Base):**
- **Boundary semiring operations**: `⊕_L`, `⊗_L`, `⊕_R`, `⊗_R`
- **Bulk semiring operations**: `⊕B`, `⊗B`
- **Couplers/observers**: `ι_L`, `ι_R`, `ν_L`, `ν_R`
- **Braiding**: `ad_0`, `ad_1`, `ad_2`, `ad_3`
- **Central scalars**: `φ`, `barφ`, `z`, `barz`
- **Basepoint**: `a_0`, `a_1`, `a_2`, `a_3`, `Gen4`

### **2. Derived (v10 Core):**
- **Triality operations**: Defined in terms of boundary operations
- **Projectors**: Defined in terms of couplers/observers
- **Normal form**: Defined in terms of header/core decomposition
- **Triality functors**: Defined in terms of observers and injections

### **3. Extended (CLASS):**
- **Guarded negation**: Defined in terms of relative complement `⊖_L`
- **Domain maps**: Defined in terms of semiring homomorphisms
- **PSDM**: Defined in terms of partial domain maps
- **Moduli system**: Defined in terms of flow parameters

## 🎯 **Minimal Axiom Set - CORRECTED ANALYSIS**

### **The 9 Axioms Break Down As:**

#### **Semiring Axioms (8 total - 2 copies of 4 semiring axioms):**

**Left Boundary Semiring (4 axioms):**
1. `⊕_L` forms a commutative idempotent monoid
2. `⊗_L` forms a commutative idempotent monoid  
3. `⊗_L` distributes over `⊕_L`
4. `⊗_L` has absorption: `x ⊗_L (x ⊕_L y) ≡ x`

**Right Boundary Semiring (4 axioms):**
5. `⊕_R` forms a commutative idempotent monoid
6. `⊗_R` forms a commutative idempotent monoid
7. `⊗_R` distributes over `⊕_R`  
8. `⊗_R` has absorption: `x ⊗_R (x ⊕_R y) ≡ x`

**Bulk Semiring (4 axioms):**
9. `⊕B` forms a commutative monoid with annihilating `0_B`
10. `⊗B` distributes over `⊕B` and has unit `1_B`
11. `⊗B` has annihilation: `0_B ⊗B x ≡ 0_B`
12. `⊗B` has distributivity: `x ⊗B (y ⊕B z) ≡ (x ⊗B y) ⊕B (x ⊗B z)`

#### **Limited Omniscience Axiom (1 axiom):**
13. **"Residual bulk is invisible to observers"** - This is the **limited omniscience axiom**

### **Additional Structural Axioms (4 total):**
14. Observers `ν_*` retract `ι_*` (coupler structure)
15. Basepoint `Gen4(a_0,a_1,a_2,a_3) = 0_B` (normalization)
16. Braids `ad_i` commute up to central `F_{ij}` (braiding structure)
17. Triality conjugations are typed anti-involutions (conjugation structure)

### **2. Regularity Conditions (Extensions):**
- **RC-GN**: Relative complement exists on principal ideals
- **RC-D**: Domain map compatibility conditions
- **RC**: Flow compatibility for moduli

## 🎯 **Key Insights**

### **1. Minimality:**
- **Only 9 core axioms** define the entire framework
- **All extensions are definitions** over v2 primitives
- **No new axioms** introduced in v10 Core or CLASS

### **2. Guarded Negation:**
- **Not primitive**: Defined in terms of relative complement `⊖_L`
- **Partial map**: Undefined outside principal ideal `↓g`
- **Universality**: Achieved through guard selection, not constraint

### **3. Domain Maps:**
- **Not primitive**: Defined as semiring homomorphisms
- **Regularity conditions**: Ensure compatibility with framework
- **PSDM**: Partial version supporting irreversible computation

### **4. Framework Structure:**
- **v2 Base**: Minimal primitive symbols and axioms
- **v10 Core**: Definitions over v2 (triality, projectors, NF)
- **CLASS**: Extensions over v10 (guarded negation, domain maps, moduli)

---

**Status:** ✅ **COMPREHENSIVE ANALYSIS COMPLETE**  
**Key Finding:** CLEAN framework has remarkably few primitives (9 axioms) with all extensions being definitions
