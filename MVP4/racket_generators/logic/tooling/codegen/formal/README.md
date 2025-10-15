# CLEAN v10 Generated Libraries

This directory contains generated formal verification libraries for the CLEAN v10 mathematical system, created from the Racket logic implementation.

## Structure

Each language has its own subdirectory with the following structure:

```
{language}/
├── generated_CLEAN.{ext}     # Main library file
├── lib/                      # Core library modules
│   ├── generated_Core.{ext}
│   ├── generated_Observers.{ext}
│   ├── generated_Kernels.{ext}
│   └── generated_NormalForms.{ext}
└── tests/                    # Test harness
    ├── generated_CoreTests.{ext}
    ├── generated_PropertyTests.{ext}
    ├── generated_IntegrationTests.{ext}
    └── generated_TestRunner.{ext}
```

## Languages

- **Coq** (`.v`): Uses underscore naming convention (`generated_Core.v`)
- **Agda** (`.agda`): Uses hyphen naming convention (`generated-Core.agda`)
- **Lean** (`.lean`): Uses hyphen naming convention (`generated-Core.lean`)
- **Isabelle** (`.thy`): Uses underscore naming convention (`generated_Core.thy`)

## Generated Content

All libraries are generated from the real CLEAN v10 signature defined in the Racket logic:

- **Sorts**: L, B, R, I
- **Operations**: ⊕B, ⊗B, ⊕_L, ⊕_R, ι_L, ι_R, ν_L, ν_R, ad_0-ad_3, starB, starL, starR
- **Constants**: 0_B, 1_B, 0_L, 1_L, 0_R, 1_R, φ, barφ, z, barz, Λ, Gen4

## Test Harnesses

Each language includes a comprehensive test harness with:
- Core mathematical tests
- Property-based tests
- Integration tests
- Test runner

## Generation

Libraries are generated using:
```bash
racket main-generator.rkt --target {language} --tests --verbose
```

## Status

- ✅ Coq: Fully working
- ✅ Agda: Generated correctly, minor syntax issues
- ✅ Lean: Fully working  
- ✅ Isabelle: Generated correctly, minor formatting issues
