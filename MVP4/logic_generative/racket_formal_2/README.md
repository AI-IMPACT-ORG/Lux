# CLEAN V2/V10 — Racket Formal 2 (racket_formal_2)

## Overview

This directory introduces a clearer, modular architecture and a language-oriented layout for the CLEAN V2/V10 system. It provides a self-contained implementation under the name “Lux”, structuring components into coherent layers and preparing for a full `#lang` language definition.

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

## Notes

- External dependency note: the foundational abstract framework is no longer imported from a sibling repo; everything needed is in this folder.
- As modules are migrated, the wrappers in `src/compat/` can be removed and `src/algebra/*` can provide fully native implementations.
- The test harness has been sharpened to actually run checks (rather than just list suites) and to avoid model-dependent brittle assertions.
