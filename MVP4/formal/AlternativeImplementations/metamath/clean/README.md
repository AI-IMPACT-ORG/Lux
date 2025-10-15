# CLEAN Metamath Skeleton

This directory houses a minimal Metamath mirror of the CLEAN v10 project.
Only the scaffolding required to load and verify the hierarchy is present;
concrete derivations will be added incrementally.

```
metamath/
  clean/
    core/      basic signatures and rewrite interfaces
    app/       placeholder bridges and services
    ports/     domain adapters (Boolean, analytic, etc.)
    library.mm umbrella include for downstream users
```

## Current status

- Each core file declares the relevant symbols and axioms but omits the
  unfinished derived lemmas from earlier drafts.
- Application and port directories contain documentation-only stubs so the
  layer structure is visible without forcing unproved content into Knife.
- `Makefile` (in `formal/AlternativeImplementations/`) exposes an
  `mm-verify` target that runs `metamath-knife -v` across the stack plus the
  aggregate specifications in `../metamath/`.

## Conventions

- Documentation and comments stay ASCII-only to keep Knife’s renderer happy.
- When a module is still a stub, state that fact in the header comment rather
  than listing outlines that no longer match the file.
- New theorems should be accompanied by Knife-proof obligations before they
  are added to the repository layers.

These notes are intentionally short; consult the Agda or other backends for
full definitions until the Metamath port is populated.
