import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import rh.analytic_number_theory.VKStandalone

/-
Vinogradov–Korobov annular counts interfaces.

This module packages the short-interval (dyadic annulus) counting inequality
used by the Route B pipeline.  It exposes a reusable structure recording the
linear partial-sum bound, re-expresses the canonical `ν_default` witness, and
provides a helper that upgrades the inequality to a `VKPartialSumBudget`.

All statements remain axiom-free; the proofs ultimately rely on the RS payload
available in `rh.RS.BoundaryWedgeProof`.
-/

namespace RH.AnalyticNumberTheory
namespace VinogradovKorobov

open scoped BigOperators

/-
Standalone VK numeric-lock exports

These provide access to the “locked” constants from `VKStandalone` through the
existing `VinogradovKorobov` module, so downstream imports do not change.
-/

namespace Standalone

open RH.AnalyticNumberTheory.VKStandalone

/-- Re-export of the Option 2 assembled-constants structure. -/
abbrev AssembledConstants : Type := VKStandalone.VKAssembledConstants

/-- Re-export of the Option 2 VK export record. -/
abbrev Export : Type := VKStandalone.VKExport

/-- Thin alias for `VKStandalone.assembleConstants`. -/
noncomputable def assembleConstants
    (N I : ℝ → ℝ → ℝ)
    (hJ : VKStandalone.JensenStripInput N I)
    (hI : VKStandalone.IntegralLogPlusBoundVK I) : AssembledConstants :=
  VKStandalone.assembleConstants N I hJ hI

/-- Thin alias for `VKStandalone.buildVKExport`. -/
noncomputable def buildVKExport
    (N I : ℝ → ℝ → ℝ)
    (hJ : VKStandalone.JensenStripInput N I)
    (hI : VKStandalone.IntegralLogPlusBoundVK I)
    (sigmaStar : ℝ) : Export :=
  VKStandalone.buildVKExport N I hJ hI sigmaStar

/-- Geometric Poisson constant at α = 3/2 (equals 9). -/
noncomputable def lockedCα : ℝ := VKStandalone.lockedCα

lemma lockedCα_eq_9 : lockedCα = 9 := VKStandalone.lockedCα_eq_9

/-- Assembled K_{ξ,paper} under the locked parameters; depends only on the explicit
near-field budget `Cnear` and the small-height budget `Ksmall` (both provided externally). -/
noncomputable def lockedKxiPaper (Cnear Ksmall : ℝ) : ℝ :=
  VKStandalone.lockedKxiPaper Cnear Ksmall

/-- The locked Whitney parameters (α = 3/2, c = 1/10). -/
noncomputable def lockedWhitney : VKStandalone.VKWhitney := VKStandalone.lockedWhitney

/-- The locked VK pair (C_VK, B_VK) = (10^3, 5). -/
noncomputable def lockedVKPair : ℝ × ℝ := VKStandalone.lockedVKPair

/-- The locked T₀ = e^{30}. -/
noncomputable def lockedT0 : ℝ := VKStandalone.lockedT0

/-!
Note: Analytic witness wiring (Littlewood–Jensen, rectangle bounds) is intentionally
omitted here to keep this module dependency-light for the build. The `VKStandalone`
APIs are re-exported above so downstream modules can provide witnesses where needed.
-/

end Standalone

end VinogradovKorobov
end RH.AnalyticNumberTheory
