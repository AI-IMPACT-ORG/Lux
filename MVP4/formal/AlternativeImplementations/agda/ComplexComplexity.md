# Computational Complexity Thread Inside CLEAN

This note collects the ingredients that already live in the Agda stack and shows how they combine into the miniature complexity theory that drives the analytic port.  Nothing new is introduced here; the goal is to keep the architecture easy to audit when we layer more examples on top.

## Stratified logics and complexity tags

The modules under `CLEAN/Application` provide the classification spine:

- `CLEAN.Application.Classification` defines the three renormalisation strata
  (`TierSuper`, `TierRen`, `TierNon`) together with their logic-order and
  complexity tags (`Decidable`, `NPClass`, `coNPClass`).
- `CLEAN.Application.Complexity` packages those strata into decision ports.  The
  NP port (`NPDecisionPort`) uses the Boolean evaluation infrastructure, while
  the coNP port (`CoNPDecisionPort`) delegates to the higher-order encoding.
- `CLEAN.Application.GuardedPipeline` ties the guarded negative witness,
  kernel bundle, NP port, and renormalisation witness together.  This is the
  place where the logic/complexity boundary meets the analytic world.

These pieces ensure that every `StratifiedLogic` carries both a logic-order tag
and a complexity tag, and that we have evidence separating the tags:
`renVsNonRenComplexity`, `superVsNonRenComplexity`, and `np≠coNP`.

## Five normalisation conditions

When the analytic port is instantiated the following equalities keep the logic
and the boundary aligned:

1. `ζ-normalisation₁` and `ζ-normalisation₂` (in
   `CLEAN.Ports.Analytic.ZetaProperties`) guarantee that parametrisation with
   identity flows returns the original normal forms.
2. `ζ-hecke-infinity` identifies the Hecke character’s infinity type with the
   base normal form chosen for the logical L-series.
3. `ζ-artin-determinant` aligns the Artin determinant with the same base form.
4. `ζ-local-delta` states that applying `DeltaNF` to the Hecke coefficient
   produces the Artin local Euler factor.
5. `ζ-delta-agreement` packages the previous statements with the renormalisation
   witness to show that the evaluated Dirichlet series and Euler product agree
   after a single Δ step.

Because these conditions are exported as lemmas, they can be referenced by any
future example (Riemann, quadratic, or otherwise) without restating the proofs.

## Complexity story in the analytic port

Putting the classification spine and the five normalisation equalities together:

- The coNP port obtained from the higher-order encoding feeds directly into the
  analytic port (`CLEAN.Ports.Analytic`).  The Gödel-style dichotomy (`logicOutcome`,
  `godelCriticalLine`) is therefore stated at the coNP stratum.
- The NP port remains available to express “positive” complexity results; the
  guarded pipeline exhibits both ports simultaneously.
- The regulator growth/decay control stored in `GrowthDecayControl` keeps the
  λ-budget bounded in both examples (`riemannGrowthDecay`, `quadraticGrowthDecay`).

This is enough structure to reason about complexity-induced divergences: if the
normalisation equalities hold but the Δ–Euler agreement fails, the culprit must
be either a growth/decay violation or a logic/complexity mismatch, not missing
witnesses.

## Where to extend next

1. **Richer characters.**  Supply non-trivial Hecke/Artin data (quadratic,
   CM, or Artin two-dimensional) together with their Δ-compatibility proofs.
2. **Multiple strata.**  Instantiate `LogicalZeta` at the NP and super-renormalisable
   levels by selecting different encoded witnesses; the existing lemmas already
   lift across the stratification.
3. **Cross-checks.**  Use `CLEAN.Application.KernelRenormalisability` to derive
   renormalisation witnesses via the kernel CCC and compare them against the
   analytic port to gain automated sanity checks.

With these points in place, the complexity story stays compact: every new example
adds arithmetic data to `LogicalZeta`, while the rest of the architecture—the
classification spine, the five normalisation conditions, and the guarded
pipeline—remains unchanged.
