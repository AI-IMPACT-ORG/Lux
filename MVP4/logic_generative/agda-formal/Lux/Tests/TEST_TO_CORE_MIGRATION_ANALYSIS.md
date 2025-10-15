<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# CLEAN Logic System - Test-to-Core Migration Analysis

## 🔍 **ANALYSIS: What Should Be Migrated from Tests to Core**

### **🎯 CRITICAL FINDINGS**

After analyzing the test suite, I've identified several **fundamental mathematical operations and structures** that are currently only referenced in tests but should be **core functionality** in the Agda presentation of the CLEAN logic system.

## **📊 MIGRATION PRIORITY MATRIX**

### **🔴 HIGH PRIORITY - Essential Core Operations**

#### **1. Triality Operations (V10 Core)**
**Current Status**: Only referenced in tests, not implemented in core
**Should Be Core Because**: These are fundamental mathematical operations

**Operations to Migrate:**
- **Projectors**: `P(P(x)) = P(x)` - idempotent projection operations
- **Boundary Sum**: `ρ(t) = [L]t ⊕_B [R]t` - reconstitution operation
- **Bulk Equals Boundaries**: `ν_L(t) = ν_L(ρ(t)), ν_R(t) = ν_R(ρ(t))`
- **Triality Functors**: `T_L, T_R, T_B` - fundamental functors
- **Residual Properties**: Core mathematical properties
- **Bulk Two Boundaries**: `Bulk = Two Boundaries` theorem

#### **2. Moduli System Operations (V10 Core)**
**Current Status**: Only referenced in tests, not implemented in core
**Should Be Core Because**: These are essential for parametric normal forms

**Operations to Migrate:**
- **Moduli System**: `μ_L, θ_L, μ_R, θ_R` - moduli operations
- **Central Scalars**: `z, z̄` - extended central scalars
- **Parametric Normal Forms**: `NF, NF^B` - normal form operations
- **Header Endomorphisms**: `f_θ:ℤ→ℤ, g_μ:ℤ→ℤ` - header operations
- **Modulated Projectors**: `[μ,θ](t)` - modulated projection
- **Auxiliary Transporter**: `M_{Δk,Δm_z,Δm_{z̄}}(t)` - transport operations

#### **3. Advanced Mathematical Operations**
**Current Status**: Only referenced in tests, not implemented in core
**Should Be Core Because**: These are fundamental mathematical tools

**Operations to Migrate:**
- **Cumulants and Generating Functionals**: `Z[J]` - statistical mechanics
- **Δ-Operators**: Finite difference operators
- **Green's Sum and Kernel Operations**: Green's function operations

### **🟡 MEDIUM PRIORITY - Important Core Operations**

#### **4. Guarded Negation Operations (V10 CLASS)**
**Current Status**: Only referenced in tests, not implemented in core
**Should Be Core Because**: These are essential for computational universality

**Operations to Migrate:**
- **Guarded Negation**: `¬^g(x) := g⊖_L x` - local negation
- **NAND Operations**: `NAND(x,y) := ¬^g(x ⊗_L y)` - local NAND
- **gn-and, gn-or, gn-xor**: Guarded logical operations

#### **5. Domain Port Operations (V10 CLASS)**
**Current Status**: Only referenced in tests, not implemented in core
**Should Be Core Because**: These are essential for domain-specific computation

**Operations to Migrate:**
- **PSDM (Partial Stable Domain Map)**: Domain mapping operations
- **Domain Port Evaluation**: Port evaluation operations
- **Feynman Path Integral**: Path integral operations
- **Partition Function**: `Z` - statistical mechanics

### **🟢 LOW PRIORITY - Specialized Operations**

#### **6. Truth Theorems**
**Current Status**: Only referenced in tests, not implemented in core
**Should Be Core Because**: These are fundamental theoretical results

**Operations to Migrate:**
- **Church-Turing Equivalence**: Computational equivalence
- **EOR Health**: Health properties
- **Logic-ζ Critical Line**: Critical line properties
- **Umbral-Renormalization**: Renormalization operations
- **Mathematical Consistency**: Internal consistency system
- **Diagonal Properties**: Self-reference properties
- **Internal Compiler Generator**: Code generation

## **🏗️ PROPOSED CORE ARCHITECTURE**

### **New Core Modules to Create**

#### **1. `CLEAN.Core.TrialityOperations.agda`**
```agda
-- Triality operations and functors
-- Projectors, boundary sum, reconstitution
-- Bulk equals boundaries theorem
-- Residual properties
```

#### **2. `CLEAN.Core.ModuliSystem.agda`**
```agda
-- Moduli system operations
-- Parametric normal forms
-- Header endomorphisms
-- Modulated projectors
-- Auxiliary transporter
```

#### **3. `CLEAN.Core.AdvancedOperations.agda`**
```agda
-- Cumulants and generating functionals
-- Δ-operators (finite differences)
-- Green's sum and kernel operations
```

#### **4. `CLEAN.Core.GuardedNegation.agda`**
```agda
-- Guarded negation operations
-- NAND operations
-- Guarded logical operations
```

#### **5. `CLEAN.Core.DomainPorts.agda`**
```agda
-- PSDM operations
-- Domain port evaluation
-- Feynman path integral
-- Partition function
```

#### **6. `CLEAN.Core.TruthTheorems.agda`**
```agda
-- Truth theorems
-- Mathematical consistency
-- Diagonal lemma
-- Internal compiler generator
```

## **📋 MIGRATION STRATEGY**

### **Phase 1: Core Mathematical Operations**
1. **Migrate Triality Operations** from `V10Core/TrialityOperations.agda` tests
2. **Migrate Moduli System** from `V10Core/ModuliSystem.agda` tests
3. **Update Core Kernel** to include these operations

### **Phase 2: Advanced Operations**
1. **Migrate Advanced Operations** (cumulants, Δ-operators, Green's functions)
2. **Migrate Guarded Negation** from `V10Class/GuardedNegation.agda` tests
3. **Migrate Domain Ports** from `V10Class/DomainPorts.agda` tests

### **Phase 3: Truth Theorems**
1. **Migrate Truth Theorems** from `TruthTheorems/CoreTheorems.agda` tests
2. **Integrate Mathematical Consistency** into core
3. **Integrate Diagonal Lemma** into core

## **🎯 BENEFITS OF MIGRATION**

### **1. Mathematical Completeness**
- **Core operations** become first-class citizens in the logic
- **Mathematical rigor** is maintained at the core level
- **Specification compliance** is ensured at the core level

### **2. Architectural Integrity**
- **Onion architecture** is properly implemented
- **Core functionality** is separated from test infrastructure
- **Dependency management** is improved

### **3. Test Quality**
- **Tests become validation** of core operations rather than definitions
- **Test coverage** becomes more meaningful
- **Test maintenance** becomes easier

## **🚀 RECOMMENDED IMMEDIATE ACTIONS**

### **1. Create Core Triality Operations Module**
- Extract projector operations from tests
- Implement boundary sum and reconstitution
- Implement triality functors

### **2. Create Core Moduli System Module**
- Extract moduli operations from tests
- Implement parametric normal forms
- Implement header endomorphisms

### **3. Update Core Kernel**
- Integrate new core operations
- Maintain architectural consistency
- Ensure proper dependencies

## **🎉 CONCLUSION**

**The test suite reveals that significant mathematical operations are currently only referenced in tests but should be core functionality.**

**Priority Migration:**
1. **Triality Operations** (projectors, boundary sum, functors)
2. **Moduli System** (parametric normal forms, header operations)
3. **Advanced Operations** (cumulants, Δ-operators, Green's functions)
4. **Guarded Negation** (local negation, NAND operations)
5. **Domain Ports** (PSDM, path integrals, partition functions)
6. **Truth Theorems** (Mathematical consistency, diagonal properties)

**This migration will transform the CLEAN logic system from a test-driven architecture to a mathematically complete core architecture with comprehensive test validation.**

**Migration Status: READY TO PROCEED - Core Operations Identified! 🎯**

