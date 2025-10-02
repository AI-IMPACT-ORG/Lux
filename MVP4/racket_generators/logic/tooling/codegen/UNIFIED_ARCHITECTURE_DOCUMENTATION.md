# Unified Library Generator Architecture

## Overview

The Unified Library Generator Architecture provides a sophisticated, generalized approach to generating formal verification libraries across multiple target languages (Coq, Agda, Lean, Isabelle) from a single CLEAN v10 signature. This architecture builds on the sophisticated Coq generator pattern but abstracts it to be reusable across different formal systems.

## Architecture Benefits

### 🎯 **Consistency Across Languages**
- Unified module structure (Core, Observers, Kernels, Main)
- Consistent naming conventions and API design
- Single source of truth for CLEAN v10 signature

### 🔧 **Maintainability**
- Single codebase for all target languages
- Language-specific optimizations where needed
- Easy to extend to new formal verification languages

### 🚀 **Reusability**
- Template-based generation system
- Configurable language-specific syntax
- Modular architecture for easy extension

## Architecture Components

### Core Components

1. **Language Configuration (`language-config`)**
   - Defines language-specific syntax and conventions
   - Handles file extensions, module systems, keywords
   - Manages symbols and operators

2. **Generator State (`generator-state`)**
   - Maintains generation context
   - Tracks dependencies and generated modules
   - Manages output directory structure

3. **Module Definition (`module-def`)**
   - Represents generated modules
   - Tracks dependencies and imports
   - Manages content and metadata

### Language Support

#### Coq Configuration
```racket
(define coq-config
  (language-config 'coq ".v" 'require "(* ~a *)" "Require Import" "Axiom" "Definition" 
                   "Inductive" "->" "forall" "=" "/\\"))
```

#### Agda Configuration
```racket
(define agda-config
  (language-config 'agda ".agda" 'open "-- ~a" "open import" "postulate" "" "data" 
                   "→" "∀" "≡" "×"))
```

#### Lean Configuration
```racket
(define lean-config
  (language-config 'lean ".lean" 'import "-- ~a" "import" "axiom" "def" "inductive" 
                   "→" "∀" "=" "∧"))
```

#### Isabelle Configuration
```racket
(define isabelle-config
  (language-config 'isabelle ".thy" 'theory "(* ~a *)" "imports" "axiomatization" "definition" 
                   "datatype" "⇒" "∀" "=" "∧"))
```

## Generated Library Structure

All languages follow the same modular structure:

```
output-directory/
├── lib/
│   ├── Core.{v,agda,lean}      # Core types, operations, constants, axioms
│   ├── Observers.{v,agda,lean} # Observer functions (project_L, inject_L, etc.)
│   └── Kernels.{v,agda,lean}   # Kernel functions (compose, apply, identity)
└── CLEAN.{v,agda,lean}         # Main library with convenience definitions
```

### Core Module Contents

1. **Sorts**: Basic type hierarchy (L, B, R, I)
2. **Operations**: Algebraic operations (PlusB, MultB, Inject_L, etc.)
3. **Constants**: Fundamental constants (0_B, 1_B, φ, etc.)
4. **Terms**: Inductive term constructors
5. **Axioms**: Complete axiom set for each language

### Observer Module Contents

- `project_L`: Project bulk terms to left boundary
- `project_R`: Project bulk terms to right boundary  
- `inject_L`: Inject left boundary terms to bulk
- `inject_R`: Inject right boundary terms to bulk
- `reconstitute`: Reconstruct bulk from boundaries
- `residual`: Compute residual terms

### Kernel Module Contents

- `kernel_compose`: Compose kernel functions
- `kernel_apply`: Apply kernel to terms
- `kernel_identity`: Identity kernel function

## Usage Examples

### Generate All Libraries

```racket
#lang racket
(require "unified-library-generator.rkt")

;; Generate libraries for all supported languages
(generate-all-libraries-unified "output-directory")
```

### Generate Specific Language

```racket
#lang racket
(require "unified-library-generator.rkt")

;; Generate Coq library
(generate-coq-library-unified "coq-output")

;; Generate Agda library  
(generate-agda-library-unified "agda-output")

;; Generate Lean library
(generate-lean-library-unified "lean-output")
```

### Using Individual Generators

```racket
#lang racket
(require "agda.rkt" "coq.rkt" "lean.rkt")

;; Generate using individual generators
(emit-coq-library "coq-output")
(emit-agda-library "agda-output") 
(emit-lean-library "lean-output")
```

## Language-Specific Features

### Coq Features
- Sophisticated dependent types
- Comprehensive import system
- Rich axiom set with complex proofs
- Type classes and instances

### Agda Features
- Unicode symbols (→, ∀, ≡, ×)
- Module system with `open import`
- Postulate-based axiom system
- Clean functional syntax

### Lean Features
- Modern functional syntax
- Mathlib integration
- Axiom-based system
- Type-safe definitions

## Compilation Instructions

### Coq
```bash
cd output-directory && coqc lib/Core.v
cd output-directory && coqc lib/Observers.v
cd output-directory && coqc lib/Kernels.v
cd output-directory && coqc CLEAN.v
```

### Agda
```bash
cd output-directory && agda lib/Core.agda
cd output-directory && agda lib/Observers.agda
cd output-directory && agda lib/Kernels.agda
cd output-directory && agda CLEAN.agda
```

### Lean
```bash
cd output-directory && lean lib/Core.lean
cd output-directory && lean lib/Observers.lean
cd output-directory && lean lib/Kernels.lean
cd output-directory && lean CLEAN.lean
```

## Extension Guide

### Adding New Languages

1. **Define Language Configuration**
```racket
(define new-lang-config
  (language-config 'new-lang ".ext" 'import "-- ~a" "import" "axiom" "def" "inductive" 
                   "→" "∀" "=" "∧"))
```

2. **Add Language-Specific Templates**
```racket
(define (generate-new-lang-axioms)
  (list
   "axiom plus_comm : ∀ x y, plus x y = plus y x"
   "axiom plus_assoc : ∀ x y z, plus (plus x y) z = plus x (plus y z)"))
```

3. **Update Main Generator**
```racket
(define (generate-new-lang-library-unified output-dir)
  (generate-unified-library 'new-lang output-dir))
```

### Customizing Generated Code

The architecture supports extensive customization through:

- **Language configurations**: Modify syntax and conventions
- **Template functions**: Customize code generation patterns
- **Axiom sets**: Add language-specific axioms
- **Module structure**: Modify generated module organization

## Technical Implementation

### Template System

The generator uses a sophisticated template system that:

- Adapts syntax to target language conventions
- Handles Unicode symbols appropriately
- Manages module imports and dependencies
- Generates type-safe constructors

### Signature Analysis

The system analyzes the CLEAN v10 signature to:

- Extract sorts, operations, and constants
- Generate appropriate term constructors
- Create comprehensive axiom sets
- Manage type dependencies

### Output Management

The output system:

- Creates proper directory structures
- Manages file dependencies
- Handles language-specific file extensions
- Provides compilation instructions

## Comparison with Previous Architecture

### Before (Fragmented)
- Different patterns for each language
- Code duplication across generators
- Inconsistent module structures
- Hard to maintain and extend

### After (Unified)
- Single architecture for all languages
- Consistent patterns and structures
- Easy to maintain and extend
- Language-specific optimizations where needed

## Future Enhancements

### Planned Features
- Support for additional formal verification languages
- Enhanced template customization
- Integration with proof assistants
- Automated testing of generated libraries

### Extensibility Points
- Language configuration system
- Template engine
- Signature analysis
- Output management

## Conclusion

The Unified Library Generator Architecture provides a robust, maintainable, and extensible foundation for generating formal verification libraries across multiple target languages. By building on the sophisticated Coq generator pattern and abstracting it appropriately, we achieve consistency, maintainability, and reusability while preserving language-specific optimizations.

The architecture successfully addresses the original requirements:
- ✅ Extends Agda and Lean generators beyond stubs
- ✅ Generalizes the Coq generator pattern
- ✅ Provides consistent structure across languages
- ✅ Maintains language-specific optimizations
- ✅ Enables easy extension to new languages
