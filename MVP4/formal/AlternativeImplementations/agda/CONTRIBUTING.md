# CLEAN v10 Contribution Guidelines

To keep the onion/hexagonal architecture intact, follow these rules when adding or modifying Agda modules.

## Layer boundaries

The code is split into four layers with strict dependencies:

1. **Core** (`CLEAN/Core`, re-exported via `CLEAN/Core.agda`)
   - Contains the domain logic: sorts, signature, diagrams, rewrite system, normal forms, concrete system, guard witness, PSDM proofs, renormalisability.
   - May import only other modules inside `CLEAN/Core` and the Agda standard library.
   - Must never import `CLEAN/Application`, `CLEAN/Ports`, `CLEAN/Library`, or `CLEAN/Tests`.

2. **Application** (`CLEAN/Application`, re-exported via `CLEAN/Application.agda`)
   - Provides logic-facing services (e.g. PL bridge, stratification, complexity, kernel bundles, pipelines).
   - May import `CLEAN/Core` and other modules within `CLEAN/Application`.
   - Must not import `CLEAN/Ports`, `CLEAN/Library`, or `CLEAN/Tests`.

3. **Ports** (`CLEAN/Ports`, re-exported via `CLEAN/Ports.agda`)
   - Expose domain adapters/decision procedures. Treat ports as the outer boundary to real-world consumers.
   - May import `CLEAN/Core` or `CLEAN/Application`, but never the other way around.

4. **Library / Tests** (`CLEAN/Library`, `CLEAN/Tests`)
   - Aggregate exports and documentation/examples.
   - May import any of the above layers but introduce no new dependencies back into them.

## Naming & imports

- Every new module should live under the appropriate namespace (`CLEAN/Core/...`, `CLEAN/Application/...`, etc.).
- Prefer explicit `open import ... using (...)` lists; avoid `open ... public` unless you are inside an aggregator module.
- When creating new services, expose them via a record/interface in the application layer and consume that from ports/tests.

## Adapters (ports)

- Ports should make domain limitations explicit (e.g. by exposing the subset of logic they cover via a predicate or witness).
- Keep domain-specific logic outside the core; the core should remain unaware of concrete ports.

## Tooling

- Use the provided `CLEAN-v10.agda-lib` to load the project.
- Before submitting changes, ensure the following targets type-check:
  - `agda -i formal/AlternativeImplementations/agda CLEAN/Core/System.agda`
  - `agda -i formal/AlternativeImplementations/agda CLEAN/Application.agda`
  - `agda -i formal/AlternativeImplementations/agda CLEAN/Ports.agda`
  - `agda -i formal/AlternativeImplementations/agda CLEAN/Tests/All.agda`

Adhering to these rules keeps the domain logic isolated (onion center), allows application services to evolve independently, and forces all external integrations through explicit adapters.
