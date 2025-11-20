# VK / Route-B Proof Completion Tracker

Short answer: not yet. Here’s exactly what remains to make the proof unconditional, organized as concrete work-items plus risk notes.

---

## Outstanding proof obligations (must replace all `sorry`s)

- `rh/analytic_number_theory/VKExplicitExpSums.lean`
  - **Weyl differencing core**
    - Prove a finite-sum Weyl differencing inequality for complex sequences on Finset intervals.
    - Derive the autocorrelation bound and the shift-length reduction.
  - **Process A (Weyl A-step)**
    - Use the differencing bound + Cauchy–Schwarz to transform `(κ, λ) → (κ/(2κ+2), (κ+λ+1)/(2κ+2))`.
    - Preserve the envelope factor `K(x, t)` and keep log factors synchronized.
  - **Process B (van der Corput B-step)**
    - Prove the standard B-process bound (Poisson summation or van der Corput’s method).
    - Derive `(κ, λ) → (λ − 1/2, κ + 1/2)`.
  - **Trivial case**
    - Provide a quantitative trivial bound for Dirichlet polynomials (triangle inequality + monotone majorant).

- `rh/analytic_number_theory/ZetaRectangleBounds.lean`
  - **Approximate Functional Equation → |ζ(s)| bound**
    - Prove a usable AFE on `σ ∈ [σ₁, σ₂]` with explicit truncation (both sums) and a concrete error.
    - Feed each Dirichlet polynomial through `expSum_bound_uniform` (the VK result) to bound the two sums.
    - Collect constants into the stated `M(T, σ₁, …)`.
  - **Borel–Carathéodory for log ζ**
    - Provide a constant-explicit version on discs/rectangles; use Mathlib complex-analysis lemmas to bound `|(ζ′/ζ)(s)|` by the supremum of `Re log ζ` on a slightly larger region.

- `rh/analytic_number_theory/LittlewoodJensen.lean`
  - **Littlewood/Jensen strip lemma**
    - Formalize the contour argument on a rectangle, relating `∫ log|ζ|` on edges to a sum over zeros inside.
    - Convert to the stated zero-count bound with the `logPlus` integral on the σ-line plus edge/error terms.

## Additional Route-B prerequisites to verify

- If the final closure still references sealed RS core pieces, unseal and prove:
  - Phase–velocity identity (CR–Green decomposition) on the half-plane boundary.
  - Nonnegativity of residue/atom contributions.
  - Any other sealed “theorem” stubs invoked by the wedge closure.
- These follow from standard Green’s theorem, outer factorization, and residue calculus; confirm none remain as sealed dependencies.

## Suggested implementation order (minimizes risk)

1. **Discrete/finite-sum backbone**
   - Weyl differencing lemma (finite sums on `Icc`/Finset).
   - Complete Process A using that lemma.
   - Implement a self-contained van der Corput B-process (Poisson or standard inequality).
2. **AFE bridge to ζ**
   - Prove an AFE with explicit error for `σ ∈ [σ₁, σ₂]`, `T ≥ T₀`.
   - Use VK bounds to control the two Dirichlet-polynomial terms uniformly in `t ∈ [T, 2T]`.
3. **Borel–Carathéodory**
   - Constant-explicit proof for `log ζ` on discs inside the rectangle; deduce `|ζ′/ζ|`.
4. **Littlewood/Jensen on rectangles**
   - Formalize zero-count formula for the strip; bound other edges using the AFE/log bounds; conclude the stated inequality.
5. **Numeric closure**
   - Reconcile constants into `ExpSumConstants` and `VKBounds`.
   - Verify `Kξ ≤ 0.16` after replacing placeholders with proved values.

## Effort and risk (realistic ballpark)

| Block | Estimated time | Notes |
| --- | --- | --- |
| Weyl differencing + Process A | 2–4 days | Purely algebraic; manageable. |
| van der Corput B-process | 1–2 weeks | Poisson/oscillatory integral machinery; largest VK risk if Mathlib gaps. |
| AFE (effective, with error) | 2–3 weeks | Functional equation & Γ-control; heavy lift. |
| Borel–Carathéodory (explicit) | 2–4 days | Complex analysis; moderate effort. |
| Littlewood/Jensen rectangles | ~1 week | Contour + measure theory; constant tracking. |
| RS sealed CR–Green pieces (if needed) | 2–3 weeks | Green’s theorem, residues. |

## Key risks

- AFE and B-process are deepest blocks; may require new Mathlib lemmas (Fourier/Poisson, stationary phase, Γ-inequalities).
- Constant management: ensure the envelope `K(x, t)` propagates through each transformation to avoid recomputation.

## Success criteria

- No `sorry` remains in:
  - `rh/analytic_number_theory/VKExplicitExpSums.lean`
  - `rh/analytic_number_theory/ZetaRectangleBounds.lean`
  - `rh/analytic_number_theory/LittlewoodJensen.lean`
  - Any RS sealed prerequisites used by the wedge closure.
- CI stays green and `Kξ ≤ 0.16` follows from the proved constants.

---

If desired, this document can be converted into an executable TODO plan (e.g., via `lake` tasks) and work can begin with the Weyl differencing + Process A proofs immediately.

