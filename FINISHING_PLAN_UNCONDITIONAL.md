# Unconditional Proof Finishing Plan: Riemann-Arctan (Route B)

This plan breaks down the remaining work to achieve an unconditional proof of the Boundary Wedge (`P+`) property into isolated, verifiable tasks. Each section provides a **Standalone Prompt** designed to be pasted into a fresh AI session.

## Current Status
- **Analytic Logic:** Scaffolded but contains `sorry` (axioms) in `ZetaRectangleBounds`, `LittlewoodJensen`, and `VinogradovKorobov`.
- **Build:** Failing in `VKExplicitExpSums.lean` due to algebraic proof errors.
- **Numerics:** `VKStandalone.lean` uses placeholder constants (0s).

---

## Task 1: Fix Algebraic Build Errors (High Priority)

**Target File:** `rh/analytic_number_theory/VKExplicitExpSums.lean`
**Goal:** Make `lake build rh.analytic_number_theory.VKExplicitExpSums` pass.

### Standalone Prompt 1
```text
Role: Lean 4 Proof Engineer
Goal: Fix build errors in the exponential sum bounds module.

Context:
You are working on the `riemann-arctan` repository. The file `rh/analytic_number_theory/VKExplicitExpSums.lean` is failing to compile. It defines Vinogradov-Korobov exponent pairs and bounds.

Current Errors:
1. `Complex.abs (n^s)` vs `n^(Re s)`: The proof uses a lemma name `Complex.norm_cpow_eq_rpow_re_of_pos` which appears to be incorrect or missing. You need to find the correct Mathlib lemma (likely involving `Complex.abs_cpow_eq_rpow_re_of_pos` or `Complex.abs_cpow_real`).
2. `processA` / `processB` Induction Steps: The algebraic rearrangement of the inequalities in `expSum_bound_uniform` fails to unify. The goal is to show that the inductive step preserves the exponent pair bound structure.

Instructions:
1. Read `rh/analytic_number_theory/VKExplicitExpSums.lean`.
2. Fix the `atomic_bound_trivial` proof by using the correct lemma for `|n^s|`.
3. Fix the `processA` and `processB` cases in `expSum_bound_uniform`. You may need to be more explicit with `apply mul_le_mul` steps or use `ring_nf` / `field_simp` to align the terms before applying the induction hypothesis.
4. Verify by running: `lake build rh.analytic_number_theory.VKExplicitExpSums`.

Deliverable: The file compiles without errors.
```

---

## Task 2: Prove Borel-Carathéodory Bounds

**Target File:** `rh/analytic_number_theory/ZetaRectangleBounds.lean`
**Goal:** Eliminate `sorry` in the Borel-Carathéodory lemma and Zeta log-derivative bounds.

### Standalone Prompt 2
```text
Role: Complex Analysis Formalizer (Lean 4)
Goal: Prove the Borel-Carathéodory lemma and its application to Zeta.

Context:
The file `rh/analytic_number_theory/ZetaRectangleBounds.lean` contains a scaffold for bounding `|ζ'/ζ|` using the Borel-Carathéodory lemma. Currently, the core proofs are `sorry`.

Task:
1. Read `rh/analytic_number_theory/ZetaRectangleBounds.lean`.
2. Prove `borel_caratheodory_log_deriv`.
   - Strategy: This is a standard complex analysis result. You may use the Maximum Modulus Principle (if available in Mathlib) or Schwarz Lemma logic.
   - The statement bounds `|f'(s)|` given a bound on `Re(f)`.
3. Prove `zeta_bound_from_expsum`.
   - Use the `VKExplicitExpSums` module (assume it compiles or mock it if needed, but prefer using the existing imports).
   - Connect the exponential sum bound to `|ζ(s)|` via the Approximate Functional Equation (AFE) or a simplified partial sum bound if the AFE is too heavy. *Note: If a full AFE proof is too large, implement a standard partial-sum bound for σ close to 1.*
4. Prove `logDeriv_zeta_bound`.
   - Combine the results: ExpSums -> Zeta Bound -> Log Zeta Bound -> Log Deriv Bound.

Constraint:
- Eliminate all `sorry`s in this file.
- Do not introduce new axioms.

Verification:
- `lake build rh.analytic_number_theory.ZetaRectangleBounds`
```

---

## Task 3: Littlewood-Jensen & Residue Theorem

**Target File:** `rh/analytic_number_theory/LittlewoodJensen.lean`
**Goal:** Prove the Littlewood identity and the counting bound.

### Standalone Prompt 3
```text
Role: Analytic Number Theory Specialist (Lean 4)
Goal: Formalize Littlewood's Lemma for counting zeros.

Context:
`rh/analytic_number_theory/LittlewoodJensen.lean` asserts that the number of zeros in a strip is bounded by the integral of `log|ζ|`.

Task:
1. Read `rh/analytic_number_theory/LittlewoodJensen.lean`.
2. Prove `littlewood_identity`.
   - This requires applying the Residue Theorem to the function `(z - σ_start) * ζ'(z)/ζ(z)` on a rectangle.
   - Check `Mathlib.Analysis.Complex.CauchyIntegral` for rectangle integration and residue theorem support.
3. Prove `littlewood_jensen_bound`.
   - Estimate the contour integrals from `littlewood_identity`.
   - Use the bounds from `ZetaRectangleBounds` (assume they are proved) to handle the horizontal and right-hand edges.
   - The left-hand edge is the main term `∫ log|ζ|`.

Constraints:
- This is the hardest analytic step. If full formalization is blocked by missing Mathlib counting-integral API, explicitly document the gap and provide a rigorous paper-proof sketch in comments, but aim for a Lean proof using `CauchyIntegral`.

Verification:
- `lake build rh.analytic_number_theory.LittlewoodJensen`
```

---

## Task 4: Numeric Constants & Final Wiring

**Target Files:** `rh/analytic_number_theory/VKStandalone.lean`, `rh/analytic_number_theory/VinogradovKorobov.lean`
**Goal:** Verify `Kξ ≤ 0.16` and wire the proved theorems.

### Standalone Prompt 4
```text
Role: Integration & Quality Assurance
Goal: Finalize numeric constants and wire up the unconditional proof.

Context:
We have an analytic stack (VK bounds -> Zeta bounds -> Littlewood). We need to ensure the numerical constants satisfy the Route B requirements (`Kξ ≤ 0.16`).

Task 1: Numerics in `VKStandalone.lean`
- Read `rh/analytic_number_theory/VKStandalone.lean`.
- Replace `placeholderNearField` and `placeholderSmallHeight` with *actual* numerical values derived from the analytic bounds (e.g., using Ford/Khale explicit constants).
- Create a test lemma `theorem Kxi_le_0_16 : lockedKxiPaper ... ≤ 0.16`. Use `norm_num` to prove it.

Task 2: Wiring in `VinogradovKorobov.lean`
- Read `rh/analytic_number_theory/VinogradovKorobov.lean`.
- Remove the `sorry` in `hJ_analytic` and `hI_analytic` by applying the theorems from `LittlewoodJensen` and `ZetaRectangleBounds`.
- Remove the `sorry` in `partial_sum_bound` by applying the bounds from `VKExplicitExpSums`.

Task 3: Final Build
- Run `./ci_routeB_minimal.sh`.
- Ensure all steps pass and no `sorry` remains in the `rh/analytic_number_theory/` directory.

Deliverable: Green CI and a completed numeric check.
```

