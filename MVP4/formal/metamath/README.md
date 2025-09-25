# Metamath Formal Library

This directory contains the Metamath formal verification library for BootstrapPaper.

## Structure

```
metamath/
├── README.md                    # This file
└── Generated_Library/           # Generated Metamath files (DO NOT EDIT)
    ├── M3Metamath.mm           # Foundation layer
    ├── RGMetamath.mm           # Renormalization group operators
    ├── TestsMetamath.mm        # Test suite
    └── MDEPyramidMetamath.mm   # Main library
```

## Usage

### Prerequisites
- Metamath verifier installed
- Access to Metamath set.mm database

### Verification
```bash
# Verify individual modules
metamath 'read "Generated_Library/M3Metamath.mm"' 'verify proof *'

# Verify all modules
metamath 'read "Generated_Library/MDEPyramidMetamath.mm"' 'verify proof *'
```

## Generated vs Manual Files

⚠️ **IMPORTANT**: All files in `Generated_Library/` are automatically generated. 
Do not edit them manually as they will be overwritten.

To modify the library:
1. Edit the generator: `../../logic-transformer/generators/metamath-generator.rkt`
2. Regenerate: `racket metamath-generator.rkt`

## Mathematical Content

The Metamath library implements:
- **M3 Foundation**: Moduli spaces, type graphs, anomaly functionals
- **RG Operators**: Renormalization group flows, beta functions, entropy measures
- **Test Suite**: Consistency, completeness, soundness theorems
- **Integration**: Complete MDE pyramid with resolved metas

## Integration

This library is part of the BootstrapPaper formal verification suite alongside:
- Agda (`../agda/`)
- Coq (`../coq/`)
- Isabelle (`../isabelle/`)

All libraries implement the same mathematical content across different formal systems.

