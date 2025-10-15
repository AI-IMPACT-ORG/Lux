# Three-Part Developer Pack

> This canvas provides (1) **BNF of the logic core**, (2) an **MDE‑style pyramid** implementation plan in Racket with L (top) / B (middle) / R (bottom), and (3) two explicit **APIs**: a *Logic Library API* (for Racket and codegen to Agda/Coq/Metamath/…) and a separate *Domain API* for semantics. Everything below is in explicit markdown code blocks for copy‑paste into repos.

---

## Part 1 — BNF (Logic Core)

```bnf
File      ::= Header Section*
Header    ::= 'logic' IDENT ';'
Section   ::= Signatures | Axioms | Rules | Theorems | (Models?)  // 'Models' optional, non-binding semantics

Signatures::= 'signature' '{' SigItem* '}'
SigItem   ::= OpDecl ';'
OpDecl    ::= 'op' IDENT ':' Type ( 'arity' '(' INT ',' INT ')' )?
            | 'const' IDENT ':' Type
Type      ::= Obj '→' Obj | Obj ('×' Obj)+ '→' Obj
Obj       ::= 'I' | 'L' | 'B' | 'R' | '(' Obj '⊗' Obj ')'

Axioms    ::= 'axioms' '{' Equation* '}'
Equation  ::= Term '≡' Term '.'

Rules     ::= 'rules' '{' Rule* '}'
Rule      ::= 'infer' IDENT ':' Premises '⇒' Conclusion '.'
Premises  ::= (Judgment (',' Judgment)*)?
Conclusion::= Judgment
Judgment  ::= Context '⊢' Equation | Context '⊢' Typing
Context   ::= '[' (Var ':' Type (',' Var ':' Type)*)? ']'
Typing    ::= Term ':' Type
Var       ::= IDENT

Term      ::= IDENT                               // variable or constant
           | IDENT '(' ArgList ')'                 // application
           | Term '⊗' Term                        // tensor
           | Term ';' Term                        // composition
ArgList   ::= Term (',' Term)* | ε

Theorems  ::= 'theorems' '{' Thm* '}'
Thm       ::= IDENT ':' Formula '.'
Formula   ::= Atom
           | Formula '∧' Formula
           | Formula '∨' Formula
           | Formula '⊗' Formula
           | '∃' Var ':' Obj '.' Formula
Atom      ::= Term '≡' Term
```

**Primitive Symbols (must exist in every signature):**

```bnf
// Boundary (boolean semirings)
const 0_L : I→L ; const 1_L : I→L ; op ⊕_L : L×L→L ; op ⊗_L : L×L→L ;
const 0_R : I→R ; const 1_R : I→R ; op ⊕_R : R×R→R ; op ⊗_R : R×R→R ;

// Bulk (log-semiring) & couplers
const 0_B : I→B ; const 1_B : I→B ; op ⊕B : B×B→B ; op ⊗B : B×B→B ;
op ι_L : L→B ; op ι_R : R→B ;

// Glue: regulators, duals, braiding, auxiliaries
const a_0,a_1,a_2,a_3 : I→B ;
op ad_0,ad_1,ad_2,ad_3 : B→B ;
const F_ij : I→B   // for all i≠j in {0,1,2,3}
const z, barz : I→B // auxiliaries (eliminable); overall scale = z ⊗B barz

// Arity-4 generator (primitive)
op Gen4 : B×B×B×B → B ;
```

**Axiom Schemas (equational):**

```bnf
// Boundary semirings (both sides)
axiom L-monoid-⊕:   ⊕_L is commutative idempotent with unit 0_L.
axiom L-monoid-⊗:   ⊗_L is commutative idempotent with unit 1_L.
axiom L-dist:       x ⊗_L (y ⊕_L z) ≡ (x ⊗_L y) ⊕_L (x ⊗_L z).
axiom L-absorb:     x ⊗_L (x ⊕_L y) ≡ x.
axiom R-monoid-⊕:   ⊕_R is commutative idempotent with unit 0_R.
axiom R-monoid-⊗:   ⊗_R is commutative idempotent with unit 1_R.
axiom R-dist:       x ⊗_R (y ⊕_R z) ≡ (x ⊗_R y) ⊕_R (x ⊗_R z).
axiom R-absorb:     x ⊗_R (x ⊕_R y) ≡ x.

// Bulk semiring + couplers
axiom B-monoid-⊗B:   ⊗B is commutative monoid with unit 1_B.
axiom B-monoid-⊕B:  ⊕B is commutative monoid with unit 0_B.
axiom B-dist:       x ⊗B (y ⊕B z) ≡ (x ⊗B y) ⊕B (x ⊗B z).
axiom Coupler:      ι_*(1_*)=1_B and ι_*(0_*)=0_B for *=L,R.

// Braided duals (general case)
axiom NC1:          ad_i ; ad_j ≡ (ad_j ; ad_i) ⊗B F_ij,   F_ij ⊗B F_ji ≡ 1_B.
axiom NC2:          F_ij ⊗B F_jk ⊗B F_ki ≡ 1_B for all triples (i,j,k).

// Normalization (basepoint)
axiom Norm:         Gen4(a_0,a_1,a_2,a_3) ≡ 0_B at a fixed basepoint ā.
```

**Notation hygiene & context grammars**

- *Overload convention*: **reserve** `⊗` for the SMC tensor only; **bulk multiplication is written `⊗B` everywhere** (operation symbol inside `B`). Types disambiguate usage automatically.
- *Precedence*: application > `;` (composition) > `⊗` (tensor) > bulk `⊕B,⊗B` and boundary `⊕_*,⊗_*`.

```bnf
// Context grammars (well-typed, single-hole)
C_L[–] ::=  ι_L ; C_B[–]                       // lift bulk to L via coupler
         |  ⊕_L( C_L[–] , t_L ) | ⊕_L( t_L , C_L[–] )
         |  ⊗_L( C_L[–] , t_L ) | ⊗_L( t_L , C_L[–] )
         |  C_L[–] ; id_L  |  id_L ; C_L[–]

C_R[–] ::=  ι_R ; C_B[–]
         |  ⊕_R( C_R[–] , t_R ) | ⊕_R( t_R , C_R[–] )
         |  ⊗_R( C_R[–] , t_R ) | ⊗_R( t_R , C_R[–] )
         |  C_R[–] ; id_R  |  id_R ; C_R[–]

C_B[–] ::=  ⊕B( C_B[–] , t_B ) |  ⊕B( t_B , C_B[–] )
         |  ⊗B( C_B[–] , t_B ) | ⊗B( t_B , C_B[–] )
         |  ad_i( C_B[–] )
         |  Gen4( u,u,u, C_B[–] )  |  Gen4( u,u, C_B[–], u ) | …  // one-hole placement
         |  ( C_B[–] ) ; id_B  |  id_B ; ( C_B[–] )

// t_L,t_R,t_B,u range over closed terms of the corresponding sorts.
```
**Equality Layer Stack (aligned with L/B/R split):**

```bnf
// Gauge equalities (presentation-only; always factored out internally)
//   ≡_scale : quotient by powers of (z ⊗B barz)
//   ≡_hel   : balanced exchange of z ↔ barz (no net scale)
// The engine computes all observational equalities *modulo* these gauges by default.
```

**Observational equalities (five notions):**

```bnf
// Three sublogic equalities (contextual)
// 1) Left-local equality ≡_L on closed bulk scalars t,u:
//    t ≡_L u  :⇔  for all L-contexts C_L[−]: B→L built from {ι_L, ⊕_L, ⊗_L} and bulk ops,
//                 C_L[t] ≡ C_L[u] holds in the L-boolean semiring.
//
// 2) Bulk equality ≡_B on closed bulk scalars t,u:
//    t ≡_B u  :⇔  for all bulk contexts C_B[−]: B→B built from bulk ops {⊕B,⊗B,ad_i,F_ij,Gen4},
//                 C_B[t] ≡_* C_B[u] holds in B (mod gauge).
//
// 3) Right-local equality ≡_R on closed bulk scalars t,u:
//    t ≡_R u  :⇔  for all R-contexts C_R[−]: B→R built from {ι_R, ⊕_R, ⊗_R} and bulk ops,
//                 C_R[t] ≡ C_R[u] holds in the R-boolean semiring.
```

```bnf
// 4) Local-agreement equality ≡_loc : conjunction of boundary views
//    t ≡_loc u  :⇔  (t ≡_L u) ∧ (t ≡_R u).
```

```bnf
// 5) Metalogical global equality ≡_meta : full-context equivalence
//    t ≡_meta u :⇔ for all closed contexts C[−]: B→B built from the *entire* signature
//                 {L,B,R ops, ι_L,ι_R, bulk ops (⊕B,⊗B,…), Gen4},  C[t] ≡_* C[u] in B (mod gauge).
```

```bnf
// Helper (“star”) equality ≡_⋆ : reversible, information-preserving core
//    ≡_⋆ is the *largest* congruence generated by invertible rewrites only:
//      • SMC structural isos (associativity/unit/symmetry),
//      • braided commutations ad_i;ad_j ↔ ad_j;ad_i ⊗B F_ij when F_ij has an inverse,
//      • elimination/insertions of 1_B and of paired z/barz with *zero* net effect.
//    Theorem (Reversible Collapse):  ≡_⋆ ⊆ (≡_loc ∩ ≡_meta), and every ≡_⋆-step is
//    computationally reversible (no information loss). In flat subtheory (F_ij=1_B),
//    ≡_⋆ coincides with SMC isomorphism equivalence.
```

> **Notes.** (i) All five observational equalities are computed modulo the gauge equalities `≡_scale` and `≡_hel` by default. (ii) If an R‑matrix is adopted, one may strengthen `≡_B`/`≡_meta` by also quotienting by YBE tiles; otherwise coherence is tracked by the arity‑5/6 witnesses.

---

## Part 2 — Implementation Plan (MDE‑like Pyramid; Racket‑first)

```markdown
Layering (top→bottom):   L (Left boundary)  →  B (Bulk core)  →  R (Right boundary)
Goal: balance **atomicity** (small kernels) with **saturation** (useful closures/indices).

LAYER L — Presentation & Boundary DSLs (atomic, light saturation)
- Provide two minimal boundary DSLs: L-DSL and R-DSL (boolean semirings with ⊕_*, ⊗_*).
- Parsing/pretty-printing for L/R formulas; explicit L/R arity checks.
- Thin wrappers for couplers ι_L, ι_R into bulk terms.
- Optional: developer REPL helpers (tactics) that build bulk diagrams from boundary data.

LAYER B — Core Engine (atomic kernel + selective saturation)
- Atomic kernel:
  • Term data types (SMC), type checker (objects, L/R arity), symbol table.
  • Equational kernel for bulk & boundaries, braided rewriting (NC1, NC2).
  • Congruence engines for ≡_scale, ≡_hel, with combined ≡_*.
  • Primitive Gen4, plus macros Noe5/CS5/Rice6/NR6.
- Saturation services (opt-in):
  • AC canon for ⊕B; monomial canon for ⊗B.
  • Braiding normalizer (bubble ad_i to a chosen total order; accumulate F_ij; reduce 3-cycles).
  • Memoized normalization (hash-consing) and critical-pair checker (if ℛ is enabled, enforce YBE tiles).

LAYER R — Backends & Exporters (saturated views)
- Pretty printers/emitters for: Agda, Coq, Metamath (.mm), Lean, plain LaTeX.
- Model stubs (non-binding): numerics, logging hooks (to demo semantics without coupling into logic core).
- Packaging: codegen scaffolds (project templates) for proofs in each target.

Build & CI
- Unit tests per layer; golden files for exporters; property tests for congruences.
- Performance budgets for normalization and braiding (O(n log n) on term size with hash-consing).
```

**Racket structure (suggested modules):**

```racket
(module logic/signature       …)  ; ops, profiles, L/R arity, registry
(module logic/syntax          …)  ; terms (SMC), typing, contexts
(module logic/axioms          …)  ; equational axioms as rewrite rules
(module logic/rewrite         …)  ; core rewriting + AC canon + braiding (NC1,NC2)
(module logic/congruence      …)  ; ≡_scale, ≡_hel, and observational equalities ≡_L,≡_B,≡_R,≡_loc,≡_meta,≡_⋆
(module logic/gen4            …)  ; primitive Gen4 + normalization basepoint
(module logic/derived         …)  ; macros: Noe5, CS5, Rice6, NR6
(module logic/check           …)  ; well-formedness, symbol hygiene, arity checks
(module dsl/left              …)  ; L-DSL
(module dsl/right             …)  ; R-DSL
(module export/agda           …)  ; emit .agda
(module export/coq            …)  ; emit .v
(module export/metamath       …)  ; emit .mm
(module export/lean           …)  ; optional
(module tooling/repl          …)  ; dev REPL commands & tactics
(module tooling/tests         …)  ; unit and property tests
```

## Part 3 — APIs

### 3A. Logic Library API (Racket; codegen to Agda/Coq/Metamath/…)

```racket
;; -------------------------------
;; Signature and Symbols
;; -------------------------------
(define-type Obj (U 'I 'L 'B 'R (Pairof Obj Obj))) ; ⊗ as pair-catenation
(struct op   ([name : Symbol] [dom : (Listof Obj)] [cod : Obj] [larity : (Pairof Natural Natural)]) #:transparent)
(struct konst([name : Symbol] [cod : Obj]) #:transparent)

(define (make-signature) …) ; -> signature-handle
(add-const!   sig (konst '0_B 'B))
(add-op!      sig (op '⊕B (list 'B 'B) 'B (cons 0 0)))
(add-op!      sig (op '⊗B (list 'B 'B) 'B (cons 0 0)))
(add-axiom!   sig term-eq) ; term-eq: (→ Equation)

;; -------------------------------
;; Terms, Typing, and Equalities
;; -------------------------------
(struct var  ([name : Symbol] [type : Obj]) #:transparent)
(struct app  ([op : op] [args : (Listof term)]) #:transparent)
(struct tens ([l : term] [r : term]) #:transparent)
(struct comp ([f : term] [g : term]) #:transparent)
(define-type term (U var app tens comp))

(type-check      : signature term -> (Option Obj))

;; Gauge equalities (presentation)
(equal-scale?    : signature term term -> Boolean)  ; ≡_scale (z⊗barz)
(equal-hel?      : signature term term -> Boolean)  ; ≡_hel (z ↔ barz, balanced)

;; Observational equalities (L/B/R + local + metalogical + reversible)
(equal-L?        : signature term term -> Boolean)  ; ≡_L
(equal-B?        : signature term term -> Boolean)  ; ≡_B
(equal-R?        : signature term term -> Boolean)  ; ≡_R
(equal-loc?      : signature term term -> Boolean)  ; ≡_loc = ≡_L ∧ ≡_R
(equal-meta?     : signature term term -> Boolean)  ; ≡_meta (full contexts)
(equal-star?     : signature term term -> Boolean)  ; ≡_⋆ (reversible core)

;; Feature toggles
(set-braiding!   : signature Boolean)               ; NC1/NC2 rewriting
(set-r-matrix!   : signature Boolean)               ; enable YBE tiles in contexts
(set-rg-quotient!: signature Boolean)               ; allow CS5-guarded RG quotient in ≡_meta

;; -------------------------------
;; Generators and Derived Operators
;; -------------------------------
(gen4           : term term term term -> term)      ; Gen4 primitive
(noe5           : Symbol term term term term -> term) ; dir ∈ {e0,e1,e2,e3}
(cs5            : term term term term term -> term)
(rice6          : (term -> term) term term -> term) ; P[−] as a term-context
(nr6            : … -> term)

;; -------------------------------
;; Normalization & Proof
;; -------------------------------
(normalize/raw  : signature term -> term)           ; core axioms only
(normalize/gauge: signature term -> term)           ; modulo ≡_scale, ≡_hel
(normalize/L    : signature term -> term)           ; canonical rep for ≡_L
(normalize/B    : signature term -> term)           ; canonical rep for ≡_B
(normalize/R    : signature term -> term)           ; canonical rep for ≡_R

(prove/L        : signature term term -> (U 'ok 'fail))
(prove/B        : signature term term -> (U 'ok 'fail))
(prove/R        : signature term term -> (U 'ok 'fail))
(prove/loc      : signature term term -> (U 'ok 'fail))
(prove/meta     : signature term term -> (U 'ok 'fail))
(prove/star     : signature term term -> (U 'ok 'fail))

;; -------------------------------
;; Exporters (codegen)
;; -------------------------------
(export-agda     : signature (Listof theorem) path-string -> Void)
(export-coq      : signature (Listof theorem) path-string -> Void)
(export-metamath : signature (Listof theorem) path-string -> Void)
(export-lean     : signature (Listof theorem) path-string -> Void)
```

### 3B. Domain API (Foundational Semantics; optional add‑on)

**Separation of domains:** The Domain API never feeds back into the logic kernel’s derivability; it’s for execution, numerics, and intuition.

```markdown
Transpilers and Provers:
- Use Logic API to generate Agda/Coq/Metamath artifacts.
- Optionally, bind Domain API for property testing (QuickCheck‑style) and counterexamples.
```

