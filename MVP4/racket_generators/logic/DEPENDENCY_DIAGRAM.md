# CLEAN v10 Dependency Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                        CLEAN v10 SYSTEM                        │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│    TOOLING      │    │      ROOT       │    │   ANALYSIS      │
│                 │    │                 │    │                 │
│ • metamath.rkt  │───▶│   api.rkt       │    │ • deps.rkt     │
│ • coq.rkt       │    │                 │    │ • analysis.rkt  │
│ • agda.rkt      │    │                 │    │                 │
│ • repl.rkt      │    │                 │    │                 │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                        │
         │                        ▼
         │              ┌─────────────────┐
         │              │   TEST LAYER    │
         │              │                 │
         │              │ • core-tests    │
         │              │ • domain-tests  │
         │              │ • integration   │
         │              │ • test-runner   │
         │              │ • utilities     │
         │              └─────────────────┘
         │                        │
         │                        ▼
         │              ┌─────────────────┐
         │              │  CLASS LAYER    │
         │              │                 │
         │              │ • DomainPortAPI │
         │              │ • unified-port  │
         │              │ • institution   │
         │              │ • truth-system   │
         │              │ • feynman       │
         │              │ • psdm          │
         │              │ • guarded       │
         │              │ • moduli        │
         │              └─────────────────┘
         │                        │
         │                        ▼
         │              ┌─────────────────┐
         │              │   CORE LAYER    │
         │              │                 │
         │              │ • header        │
         │              │ • kernel        │
         │              │ • signature     │
         │              │ • nf            │
         │              │ • observers     │
         │              │ • cumulants     │
         │              │ • delta         │
         │              │ • triality      │
         │              │ • axioms        │
         │              └─────────────────┘
         │
         └─────────────────────────────────┐
                                           │
                                           ▼
                              ┌─────────────────┐
                              │  MATHEMATICAL   │
                              │   FOUNDATIONS   │
                              │                 │
                              │ • CLEAN v10     │
                              │ • Constructive  │
                              │   Logic         │
                              │ • RG Blocking   │
                              │ • Triality      │
                              │ • Boundary Sum  │
                              └─────────────────┘
```

## Dependency Flow Analysis

### Layer Dependencies (Top → Bottom)
1. **Tooling** → **Root API** → **Test Layer** → **Class Layer** → **Core Layer**
2. **Tests** → **DomainPortAPI** → **Core Modules**
3. **Domain Ports** → **DomainPortAPI** → **Core Modules**

### Key Dependencies
- **Most Imported:** `signature.rkt` (7 imports)
- **API Gateway:** `api.rkt` (4 imports)
- **Core Foundation:** `header.rkt`, `kernel.rkt`, `observers.rkt`

### Architectural Patterns
- ✅ **Onion Architecture:** Dependencies flow inward
- ✅ **No Circular Dependencies:** Clean dependency graph
- ✅ **Layered Testing:** Tests mirror implementation layers
- ✅ **Domain Isolation:** DomainPortAPI provides clean boundaries

### File Count by Layer
- **Core:** 11 files (mathematical foundations)
- **Class:** 10 files (domain extensions)
- **Tests:** 7 files (comprehensive testing)
- **Tooling:** 4 files (code generation)
- **Root:** 4 files (API and analysis)

## Quality Metrics
- **Total Files:** 36
- **Circular Dependencies:** 0 ✅
- **Architectural Layers:** 4
- **Test Coverage:** Comprehensive (all layers)
- **Domain Support:** 4+ computational paradigms

