# CLEAN v10 Logic Stack (Racket)

This directory reorganises the logic runtime around the **CLEAN v10** specifications.  The tree intentionally mirrors the “core/class/tooling” split outlined in the spec:

```
clean/
  core/      ; constructive core + triality + bulk decomposition
  class/     ; guarded negation, PSDM, domain ports, Feynman layer
  tooling/   ; lightweight REPL + export stubs (Agda/Coq/Metamath)
```

Only a minimal, implementation-ready constructive kernel is provided.  Everything else (guarded negation, PSDM/domain ports, Feynman view) is layered, so downstream code can opt-in progressively.

Run the core sanity tests with:

```
raco test racket_generators/logic/clean/core/tests/unit-core.rkt
raco test racket_generators/logic/clean/class/tests/integ-truths.rkt
```

The `api.rkt` file re-exports the assembled façade for convenience.
