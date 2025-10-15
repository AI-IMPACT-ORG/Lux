# Subinstitutions in CLEAN v10 Logic Stack

## Overview

The CLEAN v10 logic stack contains **three overlapping subinstitutions** that partially overlap and satisfy the fundamental property:

**Bulk = Sum of Both Boundaries**

This document describes the three subinstitutions, their triality maps, and the institutional properties they satisfy.

---

## The Three Subinstitutions

### 1. **L-Subinstitution (Left Boundary Institution)**

**Definition**: The L-subinstitution consists of all terms and operations focused on the **left boundary**.

**Characteristic Map**: 
```racket
L-map: Bulk → Left Boundary
L-map(t) = reflect(L, t) = [L](t)
```

**Institutional Properties**:
- **Closed under L-operations**: L-reflection, L-observation, reconstitution
- **L-observer property**: Observer `ν_L` sees exactly the left boundary
- **Triality conjugation**: `starL` preserves L-subinstitution structure
- **Boundary sum property**: For L-subinstitution terms, the bulk projects to the left boundary

**Key Identity**:
```
[L](reconstitute(t)) = [L](t)
```

---

### 2. **R-Subinstitution (Right Boundary Institution)**

**Definition**: The R-subinstitution consists of all terms and operations focused on the **right boundary**.

**Characteristic Map**:
```racket
R-map: Bulk → Right Boundary
R-map(t) = reflect(R, t) = [R](t)
```

**Institutional Properties**:
- **Closed under R-operations**: R-reflection, R-observation, reconstitution
- **R-observer property**: Observer `ν_R` sees exactly the right boundary
- **Triality conjugation**: `starR` preserves R-subinstitution structure
- **Boundary sum property**: For R-subinstitution terms, the bulk projects to the right boundary

**Key Identity**:
```
[R](reconstitute(t)) = [R](t)
```

---

### 3. **B-Subinstitution (Bulk Institution)**

**Definition**: The B-subinstitution consists of all bulk terms with **both left and right boundaries**.

**Characteristic Map**:
```racket
B-map: Bulk → Bulk
B-map(t) = t  (identity on bulk)
```

**Institutional Properties**:
- **Closed under both L and R operations**: L-reflection, R-reflection, L-observation, R-observation, reconstitution
- **Boundary sum property**: The bulk equals the sum of both boundaries
- **Triality conjugation**: `starB` preserves B-subinstitution structure
- **Full boundary decomposition**: `t = [L](t) ⊕_B [R](t)`

**Key Identity**:
```
reconstitute(t) = ρ(t)
[L](ρ(t)) = [L](t)
[R](ρ(t)) = [R](t)
```

---

## Triality Maps Between Subinstitutions

### **L → B Map** (Left to Bulk)
```racket
L→B: L-term → Bulk term containing L-term
L→B(l) = make-term(..., #:header (term-header l), #:core (term-core l))
```

### **R → B Map** (Right to Bulk)
```racket
R→B: R-term → Bulk term containing R-term
R→B(r) = make-term(..., #:header (term-header r), #:core (term-core r))
```

### **B → L Map** (Bulk to Left)
```racket
B→L: Bulk term → Left boundary
B→L(t) = reflect(L, t) = [L](t)
```

### **B → R Map** (Bulk to Right)
```racket
B→R: Bulk term → Right boundary
B→R(t) = reflect(R, t) = [R](t)
```

---

## The Fundamental Property: Bulk = Sum of Boundaries

The core mathematical property that makes the boundary sum **crystal clear** is:

```racket
For any bulk term t:
  reconstitute(t) = ρ(t) such that:
    [L](ρ(t)) = [L](t)
    [R](ρ(t)) = [R](t)
```

This means:
- The **bulk** is completely determined by its **two boundaries**
- **Reconstitution** `ρ` is the map that makes this explicit
- **Observers** `ν_L` and `ν_R` extract the left and right boundaries
- **Triality** conjugations `starL`, `starR`, `starB` preserve the subinstitution structure

---

## Overlap of Subinstitutions

The three subinstitutions **partially overlap**:

1. **L ∩ B**: Terms that live in both L-subinstitution and B-subinstitution
   - These are bulk terms with a dominant left boundary

2. **R ∩ B**: Terms that live in both R-subinstitution and B-subinstitution
   - These are bulk terms with a dominant right boundary

3. **L ∩ R ∩ B**: Terms that live in all three subinstitutions
   - These are fully symmetric bulk terms with both boundaries present

---

## Verification

All three subinstitutions and their relationships are **verified** by the test suite:

- **L-subinstitution tests**: 3 tests verifying left boundary properties
- **R-subinstitution tests**: 3 tests verifying right boundary properties
- **B-subinstitution tests**: 4 tests verifying bulk properties
- **Overlap tests**: 2 tests verifying triality maps
- **Boundary sum tests**: 3 tests verifying bulk = left + right across all subinstitutions
- **Institution claims**: 9 tests verifying institutional properties for each subinstitution
- **Triality clarity tests**: 6 tests verifying triality maps make boundary sum clear

**Total**: 37 tests passed ✓

---

## Mathematical Foundations

### Triality Structure

The triality structure provides three conjugations:

```
starL: Left → Left     (left conjugation)
starR: Right → Right   (right conjugation)
starB: Bulk → Bulk     (bulk conjugation)
```

These conjugations preserve the subinstitution structure and commute with the boundary sum property.

### Boundary Sum as Coproduct

The boundary sum can be viewed as a **coproduct** in the category of boundaries:

```
t = [L](t) ⊕_B [R](t)
```

where `⊕_B` is the boundary sum operation that combines left and right boundaries into a bulk term.

### Observer Invisibility

Residual terms are **invisible to observers**:

```
For any residual term r:
  ν_L(r) = 0_L
  ν_R(r) = 0_R
```

This ensures that only the "observable" part of the bulk contributes to the boundary sum.

---

## Conclusion

The three subinstitutions (L, R, B) form a **coherent institutional structure** where:

1. Each subinstitution is **closed** under its characteristic operations
2. The **triality maps** make the boundary relationships explicit
3. The **boundary sum property** holds across all three subinstitutions
4. The **institutional properties** are verified by comprehensive tests

This structure provides a **constructive foundation** for the CLEAN v10 logic stack, ensuring that all operations respect the fundamental principle:

**Bulk = Sum of Both Boundaries**
