# CLEAN v10 — Agda Graph-Rewriting Model

This directory contains an independent Agda presentation of the CLEAN v10 ruleset
summarised in `CHATGPT/CLEAN_v10_CLASS_Full_Spec.md` and the constructive core notes in
`CHATGPT/CLEAN_v10_CORE_Constructive_Logic.md`.  The code is organised as a layered
onion/hexagonal stack:

**Core (`CLEAN/Core` and `CLEAN/Core.agda`)** — domain logic only.  The modules `Sorts`,
`Signature`, `Diagram`, `Rewrite`, `NormalForm`, `System`, `Guard`, `Proofs/PSDM`, and
`Renormalisability` capture the CLEAN PROP, its rewrite system, and the renormalisability
witnesses.  Nothing in this layer depends on application adapters or ports.

**Application (`CLEAN/Application` and `CLEAN/Application.agda`)** — logic-facing services
that elaborate the core.  `PLBridge` supplies the lambda surface, `Classification`
stratifies logics by order/complexity, `Complexity` builds NP/coNP decision ports,
`KernelRenormalisability` recasts the renormalisability theorem via a kernel/CCC bundle, and
`GuardedPipeline` ties the guarded rewrite, kernel data, and decision port together.

**Ports (`CLEAN/Ports` and `CLEAN/Ports.agda`)** — adapters that expose the logic to domain
consumers.  `Ports/Boolean.agda` is the current example; additional domain maps should live
here and act as the boundary between logic and environment.
`Ports/Analytic.agda` sketches the analytic number theory adapter (number fields, ζ-kernel,
and a Gödel-style dichotomy yielding either inconsistency or the critical line property). The
port also carries an explicit caution value to emphasise that a logic analogue of GRH is not
proved; external consumers must supply their own analytic justification.
`Ports/Analytic/ZetaProperties.agda` records ten standard ζ-properties (parametrisation identities,
Δ/κ commutation, distribution over the bulk sum, renormalisation witnesses) using the existing
normal-form and rewrite lemmas, and proves that the constant extracted from the logic does not
depend on any of the six moduli—ready for future analytic refinements.
`CLEAN/Core/Dirichlet.agda` introduces a lightweight Dirichlet-series algebra over normal forms,
and `Ports/Analytic/DirichletSeries.agda` shows how the analytic port instantiates symmetric
weights, setting up regulated Euler products and their duals.
`LambdaPipeline.md` sketches how λ-deformations, Dirichlet/Euler constructions, and the analytic
port compose into a single flow from logical witnesses to boundary adapters.

**Libraries & tests** — `CLEAN/Library/` re-exports the layers for downstream users, while
`CLEAN/Tests/` hosts type-checkable documentation.  These modules may depend on the layers
above but never the other way around.
`CLEAN/Library/CriticalLine.agda` compares undeformed vs. λ-deformed truth, providing a
library-level derivation of the critical line witness that mirrors the analytic port.

Ports deliberately provide partial domain maps (Gödel’s first incompleteness viewed as
architecture): the logic works with self-referential witnesses, while each adapter exposes
only the tractable slice needed by its target domain.

## Usage

1. Ensure Agda 2.7 (or newer) is on your PATH.
2. Type-check the full development with:

   ```sh
   agda -i formal/AlternativeImplementations/agda \
        formal/AlternativeImplementations/agda/CLEAN/Core/System.agda
   ```

   Loading `CLEAN/Tests/All.agda` will transitively check the supporting modules as well.

## Extending the model

To add a new axiom, extend `RuleId` in `CLEAN/Core/System.agda`, provide the aligned `mkRule`
witness, and expose any useful derived lemmas following the existing patterns (cf.
`retractLId`, `guardNANDDerived`).  Additional domain-specific ports belong in
`CLEAN/Ports/` and can reuse the existing decision-port interfaces.

Architectural rules (layer boundaries, naming conventions, required Agda targets) are
documented in `CONTRIBUTING.md` alongside this README.
