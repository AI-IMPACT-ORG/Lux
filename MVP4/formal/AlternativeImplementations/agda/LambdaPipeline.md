# Lambda–Dirichlet Pipeline

This short note records how the λ-deformation, Dirichlet/Euler constructions, and the analytic
port interact after the recent refactor.

1. **LambdaDeformation** (`CLEAN/Library/CriticalLine.agda`) packages a baseline normal form and its
   λ-shift via `DeltaNF`.  The helper `lambdaRegulator` turns any deformation into a regulator, and
   `lambdaDirichlet` produces a regulated Dirichlet series using the new core API.

2. **Core Dirichlet/Euler algebra** (`CLEAN/Core/Dirichlet.agda`, `CLEAN/Core/EulerProduct.agda`)
   provides generic Dirichlet series, a functorial `mapSeries`, and the Euler-style product derived
   from the logical delta flow.  These are lightweight, regulator-aware building blocks.

3. **Analytic port alignment** (`CLEAN/Ports/Analytic/DirichletSeries.agda`,
   `CLEAN/Ports/Analytic/EulerProperties.agda`, `CLEAN/Ports/Analytic/Conjugation.agda`)
   shows that the analytic adaptor instantiates symmetric Dirichlet weights, that applying the
   logical star coincides with classical conjugation, and that mapping the Dirichlet series along
   `DeltaNF` reproduces the Euler product.

4. **Zeta properties** (`CLEAN/Ports/Analytic/ZetaProperties.agda`) now prove ten standard ζ-style
   identities (functional equation, Δ distribution, renormalisation witnesses) directly from the
   core lemmas and note that the extracted constant is independent of all six moduli.

Taken together, the pipeline starts with a λ-deformation of truth, feeds it through the regulated
Dirichlet algebra, relates the resulting series to the Euler product via the logical delta flow, and
shows that the star/conjugation symmetry is preserved on the analytic boundary.  This sets the stage
for future work where the classical analytic data (actual Euler factors, spectral estimates) can be
plugged in while keeping the logic semantics intact.
