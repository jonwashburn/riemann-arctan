# VK-First Completion Checklist

## Annular Energy / Schur Step
- ☐ Prove the cross-term Schur bound `annular_balayage_L2` using the CR–Green / Schur machinery (needs the actual kernel estimates, not a placeholder).

## Carleson Budget from RvM
- ☐ Replace the `Kξ := 0` witness with a concrete constant derived from the diagonal + cross-term bounds.
- ☐ Thread the new constant through `ConcreteHalfPlaneCarleson` and re-export `KxiBound α c`.

## VK / Short-Interval Counts (A/N/T Layer)
- ☐ Replace the thin re-export in `VinogradovKorobov.lean` with an actual proof (or clearly justified sealed delegation) that produces the VK partial-sum budget from short-interval counts.

### VK Integration Plan (keep build green)
1. **Stage gate: isolate a sandbox target**
   - Add a temporary lean target `rh.analytic_number_theory.VinogradovKorobov` to the CI script so failures stay local.
   - Keep `VKPartialSumBudget_from_counts_default` exported from the sealed wedge core until the new proof is ready.
2. **Port the classical bounds**
   - Recreate the short-interval VK inequality: restate the dyadic annular counts, set up the constants `ν_k`, and prove the linear partial-sum bound using mathlib’s Dirichlet kernel / partial summation facts.
   - Tie the analytic lemmas to the RS layer via `WhitneyInterval` and the existing `phi_of_nu`.
3. **Bridge to budgets**
   - Construct `VKPartialSumBudget` directly from the new counts lemma and show it is definitionally equal to the one used in RS.
   - Add a lemma comparing the new proof to the sealed export so downstream files can swap without code churn.
4. **Flip the imports**
   - Update RS modules (`BoundaryWedgeProof`, `VinogradovKorobov`) to depend on the new lemmas.
   - Remove or quarantine the sealed fallback once the CI run is green.
5. **Clean-up checkpoint**
   - Delete any temporary namespace aliases, re-run the Route B minimal CI, document the exact constants in `VK_PLAN.md`.

## CR-Green Identity & Whitney Embedding (RS Layer)
- ☐ Audit and fill the pairing L² / CR-Green pipeline (using `PoissonKernelAnalysis`, `PoissonKernelDyadic`, `CRGreenOuter`).
- ☐ Ensure Whitney separation and tent-geometry lemmas line up with the hypotheses needed for the diagonal/Schur bounds.

## Hygiene & CI Clean-up
- ☐ Deduplicate the multiple “no-zeros” directories and nested `lakefile.lean` files; enforce a single top-level Lake configuration.
- ☐ Add a standard mathlib-style GitHub workflow alongside the Route-B minimal CI.
- ☐ After the above stabilizes, bump Lean/mathlib to the current releases and re-green the project under the standard workflow.

## Documentation
- ☐ Confirm the sealed boundary-wedge core exports are fully axiom-free, documenting assumptions explicitly.
- ☐ (Optional) Produce a lean-blueprint that maps the manuscript formulas to the implemented declarations once the VK and Carleson pieces are solid.

