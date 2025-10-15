<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->
# Lux — Racket Formal 2 (racket_formal_2)

## Overview

This directory introduces a clearer, modular architecture and a language-oriented layout for the Lux system. It provides a self-contained implementation under the name "Lux", structuring components into coherent layers and preparing for a full `#lang` language definition.

Goals:
- Strong separation of concerns (AST, algebra, observers, exp/log, braiding, ports, physics, generators, tools)
- Clean public API surface (`src/main.rkt`) that re-exports stable capabilities
- Backward compatibility via wrappers so existing spec-aligned tests still run
- Ready path to a complete `#lang` (`lang/reader.rkt`) for programmatic use

## Layout

- `src/`
  - `base/`: AST, constants, abstract symbolic ops
  - `algebra/`: semiring types, observers/embeddings, exp/log, braids, NF, auxiliary ops
  - `core/`: generator/kernel utilities
  - `logic/`: guarded negation
  - `ports/`: complete domain ports
  - `physics/`: Feynman-view components
  - `compat/`: thin wrappers to original modules where needed
  - `main.rkt`: unified re-exports; stable API
- `lang/reader.rkt`: minimal reader scaffolding for future `#lang racket_formal_2`
- `tests/`: compatibility shims and two primary suites
- `run-tests.sh`: simple runner matching the original workflow

## API Compatibility

`src/main.rkt` re-exports the original capabilities (semiring structs/ops, observers, exp/log, braids, NF, guards, ports, feynman view, etc.) by composing the modular `algebra/*` and `logic/*` layers.

Foundations are fully self-contained: the previous external dependency has been removed. The local module `src/foundations/abstract-core.rkt` provides the abstract expression layer (constants, operators, evaluation helpers), keeping multiple truth systems first-class.

This allows:
- Existing tests to run unmodified (through local wrappers in `tests/`)
- Gradual replacement of old implementations with new ones without breaking the public API

## Moving Toward a Language Definition

The language for this system is named `Lux`.

- A minimal reader for `#lang Lux` (alias) can be provided when installed as a Racket collection; this repo includes `lang/reader.rkt` used internally by tests.
- `racket_formal_2/lang/reader.rkt` remains as a convenience shim during transition.

In next iterations, we can:
- Add surface syntax for semiring expressions and proofs
- Provide macro-based typed constructs for observers and exp/log forms
- Integrate a definitional interpreter and normalization-by-evaluation for Core

## Running Tests

From this folder:

- Clean suite:
  `racket -e '(require "tests/clean-test-suite.rkt") (run-clean-test-suite)'

- Spec-aligned comprehensive:
  `racket -e '(require "tests/spec-aligned-comprehensive-tests.rkt") (run-spec-aligned-comprehensive-test-suite)'

Or use `./run-tests.sh`.

## Abstract Semantics

Lux operates in a fully abstract style by default:
- Values that look numeric (e.g., `0`, `1`) are abstract constants — tokens in the syntax, not commitments to arithmetic. We avoid any numeric codings of naturals.
- Operations like `add`, `mul`, `exp`, `log`, `≤`, `≥` remain symbolic unless both sides are ground numerics. Most verifications compare abstract expressions for structural equality instead of evaluating numbers.
- Verification checks are designed to avoid numeric evaluation. When an inequality is reflexive (e.g., `x ≤ x`), it is accepted symbolically.
- Distances and metrics are uninterpreted operators (e.g., `Bdist`), not computed numbers.

This follows MVP4/chatgpt Lux*’s “abstract first” spec: proofs and witnesses are expressed as abstract terms; observers and normal forms preserve structure without injecting numeric computation.

## Equality And Truth Notions

To avoid collapsing different “truths”, we keep four distinct, complementary layers. Each layer is formalized explicitly in code and used in the appropriate place.

- Definitional (algebraic) equality
  - What: Raw equality in the algebra, modulo ACU + distributivity on `B` (and the usual laws on `L/R/Core`). Constructors return canonical representatives (e.g., flattened/sorted products for `⊗`, n‑ary nodes for `⊕`).
  - Where: Axioms A0–A7, rewrite laws, exp/log (`dec∘rec`), projector idempotence.
  - Code: `abstract-semiring-equal?` (and helper `eq-def?`). No gauge/normalisation here.

- Observational equality (port/gauge)
  - What: Equality after observing and (optionally) normalising headers: typically compare `ν_* (NF^B x)` with `ν_* (NF^B y)`.
  - Where: Port invariance, reconstitution at observer level, renormalisation identities (Callan–Symanzik, Ward).
  - Code: helpers `eq-obs-L?` / `eq-obs-R?` (with optional NF), `eq-NF?` for B‑gauge equality.

- L‑level logical truth
  - What: Truth as `L`‑valued witnesses and sequents; kernel/sequent checker steps.
  - Where: Guarded negation, lifting/transport proofs, completeness/consistency‑style theorems.
  - Code: sequent/kernal modules; not an equality on `B`.

- Model/assumption truth (port‑level)
  - What: Symbolic L‑witnesses recording model assumptions (e.g., QFT allows dagger/metric; ANT dagger at model level). Not algebraic equality and not L‑level derivations.
  - Where: Gates specific packs/evidence without affecting algebraic laws.

This separation lets axioms remain purely algebraic, while ports/verification use observational and model truths where appropriate.

## Runner Options

- Env vars:
  - `LUX_FAST=1` speeds up regulator defaults (safe; avoids any unintended heavy loops).
  - `LUX_SUMMARY_HEAVY=1` includes heavyweight domain checks in the summary.
  - `LUX_VERBOSE=1` enables optional informational prints in some evidence modules.
- CLI flags (see `tests/verification-runner.rkt`):
  - `--json` emits a machine-readable summary.
  - `--strict` exits non‑zero on any failure.
  - `--heavy-scan` enumerates heavyweight checks one‑by‑one under timeouts.
  - `--timeout <secs>` sets per‑check timeout (default 60s) for heavy‑scan.

## Design Notes (Closer to Lux*)

- Non‑expansive checks (e.g., `d(Rx,Ry) ≤ d(x,y)`) are preferred over numeric contraction factors; this avoids committing to concrete metrics.
- RG and dagger invariance are modeled on Core components where possible, keeping header flows abstract and observation‑neutral.
- Dynamic requires use robust relative paths; heavyweight modules only load when invoked.
- Central scalars default to symbolic values (`φ`, `z`, `z̄`, `Λ`) by default; no integer codings are used.

## Runtime Modes

You can toggle small, optional behaviors via environment variables:

- `LUX_FAST=1`
  - Uses small regulator defaults for port samplers; avoids any long loops.
- `LUX_SUMMARY_HEAVY=1`
  - Includes heavyweight domain checks in the summary.
- `LUX_VERBOSE=1`
  - Enables optional informational prints in evidence modules (e.g., ANT counts).
- `LUX_B_SELECT=1`
  - Enables a selective/idempotent addition on `B` with a simple dominance order (`ι_L > ι_R > mixed > unknown`). Idempotence on identical values is always enabled.
- `LUX_HEADER_MODEL=Z3`
  - Demonstration header model: `rec` represents headers as `φ^k z^mz z̄^mzb × core` and `dec` parses that product back to `(k,mz,mzb,core)`. Default remains abstract (headers elided, payload to Core).

- `LUX_PORT_VERBOSE=1`
  - Prints timing summaries for professional port runs (see Port Run API).

Port/provenance controls:
- Origin grade policy is explicit by default (`'unknown` tags are kept). You can change it at runtime via `(set-grade-unknown-policy! 'none)` to elide unknown tags, or `(set-grade-unknown-policy! 'keep)` to emit them explicitly. Helpers: `origin-tag?`, `pretty-b`.

## Gap Kernel and Port Propagation

The core “logic gap” is represented explicitly and propagated through ports:

- Core invariants (runner: “Gap properties (core)”): non‑expansive NF, DNF idempotence and transport invariance, rewrite roundtrip, rewrite monotonicity, reduction non‑invertibility.
- Port consequences (runner: “Gap propagation (by port)”):
  - ANT: RC and ξ tags; Hilbert–Pólya definition, self‑adjointness, and resolvent–ξ link.
  - Complexity: regime/lens tags; P≠NP and NP≠coNP manifestations at observer‑level.
  - QFT: reflection positivity, spectral condition, cluster decomposition; mass‑gap from Lipschitz and exponential decay tags.

The verification runner prints both sections by default; heavy‑scan lists heavyweight checks with per‑item timeouts.

Heavy integration JSON:
- Summary JSON: `racket tests/verification-runner.rkt --json > tests/tools/verification-summary.json`
- Heavy scan JSON: `racket tests/verification-runner.rkt --heavy-scan --timeout 60 --heavy-json tests/tools/heavy-scan.json`
  - You can set `LUX_B_SELECT=1` and/or `LUX_HEADER_MODEL=Z3` to exercise selective addition and Z3 header parsing.

## Port Run API (Professional Wrappers)

Every port returned by `get-domain-port` is wrapped to be reconstitution‑invariant and normalized:
- Encoder wrapper: if the input is a `B` element, it first applies `reconstitute` to enforce “bulk = two boundaries”.
- Normalizer wrapper: if the normalized output is a `B` element, it applies `B-normalize` (header‑only NF) before decoding.
- Decoder wrapper: ensures the result is always a `semiring-element` (defaulting to `Core`).

Convenience helpers:
- `(run-port 'qft (semiring-element 1 B))` → runs with timings and returns a `domain-port-result`.
- `(domain-port-run/print (get-domain-port 'lambda) (semiring-element 2 Core))` → prints stage timings when `LUX_PORT_VERBOSE=1`.

Result structure (`domain-port-result`):
- `ok?` boolean, `value` (a `semiring-element`), `error` (or `#f`), `timings` (alist for encode/eval/norm/decode), `meta` (name/carrier/q‑vector).

## Notes

- External dependency note: the foundational abstract framework is no longer imported from a sibling repo; everything needed is in this folder.
- As modules are migrated, the wrappers in `src/compat/` can be removed and `src/algebra/*` can provide fully native implementations.
- The test harness has been sharpened to actually run checks (rather than just list suites) and to avoid model-dependent brittle assertions.
