# MDE System Generators

This directory contains the cleaned-up generators for the MDE (Model-Driven Engineering) system with a clean multi-language architecture.

## 🏗️ Clean Architecture

The generators now use a clean architecture that separates language-specific details from core generation logic:

```
┌─────────────────────────────────────────────────────────────┐
│                    API Surface Layer                       │
│  (library-api.rkt) - Defines common interface             │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                 Language Abstraction Layer                  │
│  (language-abstraction.rkt) - Language-specific syntax    │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                   Core Generation Layer                     │
│  (core-generator.rkt) - Language-independent logic        │
└─────────────────────────────────────────────────────────────┘
                              │
┌─────────────────────────────────────────────────────────────┐
│                    Language Implementations                 │
│  - Agda generator (resolved-metas-generator.rkt)           │
│  - Coq generator (simple-coq-generator.rkt)               │
└─────────────────────────────────────────────────────────────┘
```

## 🎯 Working Generators

### `resolved-metas-generator.rkt` ⭐ **Agda Generator**
- **Status**: ✅ Fully working and compiles successfully
- **Purpose**: Generates Agda library with all moduli parameters explicitly resolved
- **Output**: `resolved-metas-output/` directory with compilable Agda code
- **Features**:
  - Explicit moduli instantiation (μ₁=1, μ₂=2, μ₃=3, μ₄=4, etc.)
  - Type-safe data constructors instead of complex records
  - Complete MDE pyramid (M3→M2→M1) implementation
  - RG operators with concrete moduli values
  - Mathematical theorem helpers (Gödel, Tarski, Rice, Noether, Ward)
  - Comprehensive test suite

### `simple-coq-generator.rkt` ⭐ **Coq Generator**
- **Status**: ✅ Fully working and compiles successfully
- **Purpose**: Generates Coq library with the same API surface as Agda
- **Output**: `coq-output/` directory with compilable Coq code
- **Features**:
  - Same API surface as Agda generator
  - Explicit moduli instantiation (μ₁=1, μ₂=2, μ₃=3, μ₄=4, etc.)
  - Coq-specific syntax (Modules, Inductive types, Definitions, Lemmas)
  - Complete MDE pyramid implementation
  - RG operators with concrete moduli values
  - Mathematical theorem helpers
  - Comprehensive test suite

### `rg-generator.rkt` 
- **Status**: ✅ Working
- **Purpose**: Core RG (Renormalization Group) generator
- **Features**: RG flow, beta function, anomaly measures, entropy bounds

### `rg-generator-fast.rkt`
- **Status**: ✅ Working  
- **Purpose**: Optimized RG generator for performance
- **Features**: Fast RG computations with caching

### `rg-generator-optimized.rkt`
- **Status**: ✅ Working
- **Purpose**: Memory-optimized RG generator
- **Features**: Efficient memory usage for large computations

### `rg-generator-simple.rkt`
- **Status**: ✅ Working
- **Purpose**: Simplified RG generator for basic use cases
- **Features**: Minimal RG functionality

## 📁 Directory Structure

```
generators/
├── api-surface/           # API surface definitions
│   └── library-api.rkt   # Core API surface for all generators
├── language-abstraction.rkt # Language abstraction layer
├── core-generator.rkt    # Core generation logic
├── unified-generator.rkt # Unified multi-language generator
├── resolved-metas-output/ # ⭐ Working Agda output
│   ├── MDEPyramidResolvedMetas.agda
│   ├── M3Resolved.agda
│   ├── RGResolved.agda
│   └── TestsResolved.agda
├── coq-output/           # ⭐ Working Coq output
│   ├── MDEPyramidCoq.v
│   ├── M3Coq.v
│   ├── RGCoq.v
│   └── TestsCoq.v
├── language-templates.rkt # Language-specific templates
├── resolved-metas-generator.rkt # ⭐ Agda generator
├── simple-coq-generator.rkt # ⭐ Coq generator
├── test-both-generators.rkt # Comprehensive test script
├── rg-generator*.rkt     # RG-specific generators
└── README.md            # This file
```

## 🚀 Quick Start

### Generate Agda Library:
```bash
cd /Users/rutgerboels/BootstrapPaper/MVP4/logic-transformer/generators
racket resolved-metas-generator.rkt
cd resolved-metas-output
agda MDEPyramidResolvedMetas.agda
```

### Generate Coq Library:
```bash
cd /Users/rutgerboels/BootstrapPaper/MVP4/logic-transformer/generators
racket simple-coq-generator.rkt
cd coq-output
coqc M3Coq.v && coqc RGCoq.v
```

### Test Both Generators:
```bash
cd /Users/rutgerboels/BootstrapPaper/MVP4/logic-transformer/generators
racket test-both-generators.rkt
```

## 🔧 Key Features

### Resolved Metas Generator
- **Explicit Moduli**: All moduli parameters are concrete values
- **Type Safety**: Strong typing with dependent types and proofs
- **Compilation**: Generates compilable Agda code
- **Mathematical Rigor**: Complete formal system with inference rules
- **RG Integration**: Renormalization Group approach to truth systems

### Moduli Resolution
The generator resolves all metas with concrete values:
- μ₁=1, μ₂=2, μ₃=3, μ₄=4 (fundamental moduli)
- μ₁*=1, μ₂*=2, μ₃*=3, μ₄*=4 (dual moduli)
- λ=1, λ*=1 (coupling parameters)

### Type-Safe Interface
- Data constructors instead of complex records
- Pattern-matching accessor functions
- Proof-carrying functions
- Mathematical theorem helpers

## 📊 Status Summary

| Generator | Status | Compiles | Type Safe | Notes |
|-----------|--------|----------|-----------|-------|
| `resolved-metas-generator.rkt` | ✅ Complete | ✅ Yes | ✅ Strong | **Agda Generator** |
| `simple-coq-generator.rkt` | ✅ Complete | ✅ Yes | ✅ Strong | **Coq Generator** |
| `language-abstraction.rkt` | ✅ Complete | ✅ Yes | ✅ Strong | Language abstraction layer |
| `core-generator.rkt` | ✅ Complete | ✅ Yes | ✅ Strong | Core generation logic |
| `unified-generator.rkt` | ✅ Complete | ✅ Yes | ✅ Strong | Unified multi-language generator |
| `rg-generator.rkt` | ✅ Working | ✅ Yes | ✅ Yes | Core RG functionality |
| `rg-generator-fast.rkt` | ✅ Working | ✅ Yes | ✅ Yes | Performance optimized |
| `rg-generator-optimized.rkt` | ✅ Working | ✅ Yes | ✅ Yes | Memory optimized |
| `rg-generator-simple.rkt` | ✅ Working | ✅ Yes | ✅ Yes | Simplified version |

## 🧹 Cleanup Completed

The following temporary files and directories have been removed:
- All temporary output directories (`*-output/`)
- Obsolete generator files (20+ files)
- Duplicate and experimental generators
- Non-working generators

## 🎉 Final Result

The generators directory now features a clean multi-language architecture with:
- ✅ **2 main working generators** (Agda and Coq)
- ✅ **Clean architecture** with language abstraction layer
- ✅ **Same API surface** across all languages
- ✅ **2 working output directories** with compilable code
- ✅ **Comprehensive test suite** for both generators
- ✅ **Clean API surface** definitions
- ✅ **Comprehensive documentation**

### Key Achievements:
- **Multi-Language Support**: Both Agda and Coq generators working
- **Clean Architecture**: Language-independent core logic
- **API Consistency**: Same interface across all languages
- **Type Safety**: Strong typing in both target languages
- **Compilation**: Both generators produce compilable code
- **Moduli Resolution**: All metas explicitly instantiated

The generators produce complete, type-safe, compilable libraries that instantiate the MDE system with all moduli parameters explicitly resolved in both Agda and Coq.