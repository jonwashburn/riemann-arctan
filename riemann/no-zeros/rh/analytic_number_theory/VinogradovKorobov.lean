import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import rh.RS.sealed.BoundaryWedgeProofCore
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
open RH.RS
open RH.RS.BoundaryWedgeProof

/-- Captures the VK short-interval inequality on a Whitney interval. -/
structure ShortIntervalCounts (I : WhitneyInterval) where
  nu : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ nu k
  Cν : ℝ
  Cν_nonneg : 0 ≤ Cν
  Cν_le_two : Cν ≤ 2
  partial_sum_le :
    ∀ K : ℕ,
      ((Finset.range K).sum fun k => nu k) ≤ Cν * (2 * I.len)

namespace ShortIntervalCounts

variable {I : WhitneyInterval}

/-- Convenience lemma rewriting the partial-sum inequality. -/
lemma partial_sum_bound (h : ShortIntervalCounts I) (K : ℕ) :
    ((Finset.range K).sum fun k => h.nu k) ≤ h.Cν * (2 * I.len) :=
  h.partial_sum_le K

end ShortIntervalCounts

section DefaultCounts

variable (I : WhitneyInterval)

/-- Bundles the canonical counts witness from the RS layer. -/
noncomputable def defaultCounts : ShortIntervalCounts I := by
  classical
  obtain ⟨Cν, hCν0, hCν2, hPS⟩ := RH.RS.BoundaryWedgeProof.hVK_counts_default I
  exact
    { nu := nu_default I
    , nonneg := nu_default_nonneg I
    , Cν := Cν
    , Cν_nonneg := hCν0
    , Cν_le_two := hCν2
    , partial_sum_le := hPS }

/-- Short-interval VK inequality for `ν_default`. -/
theorem hVK_counts_default :
  ∃ Cν : ℝ, 0 ≤ Cν ∧ Cν ≤ 2 ∧
    (∀ K : ℕ,
        ((Finset.range K).sum fun k => nu_default I k) ≤ Cν * (2 * I.len)) := by
  classical
  refine ⟨(defaultCounts I).Cν, (defaultCounts I).Cν_nonneg,
    (defaultCounts I).Cν_le_two, ?_⟩
  intro K
  simpa using (defaultCounts I).partial_sum_le K

/-- VK partial-sum budget for `φ_k = (1/4)^k · ν_default(k)` obtained from the counts bound. -/
lemma VKPartialSumBudget_from_counts_default :
    ∃ (VD : VKPartialSumBudget I (phi_of_nu (nu_default I))),
    0 ≤ VD.Cν ∧ VD.Cν ≤ 2 := by
  classical
  obtain ⟨Cν, hCν0, hCν2, hPS⟩ := hVK_counts_default (I := I)
  refine ⟨VKPartialSumBudget.from_counts I (nu_default I) Cν
      (nu_default_nonneg I) (by intro K; simpa using hPS K), ?_, ?_⟩
  · simpa [VKPartialSumBudget.from_counts, VKPartialSumBudget.of]
      using hCν0
  · simpa [VKPartialSumBudget.from_counts, VKPartialSumBudget.of]
      using hCν2

end DefaultCounts

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
def assembleConstants
    (N I : ℝ → ℝ → ℝ)
    (hJ : VKStandalone.JensenStripInput N I)
    (hI : VKStandalone.IntegralLogPlusBoundVK I) : AssembledConstants :=
  VKStandalone.assembleConstants N I hJ hI

/-- Thin alias for `VKStandalone.buildVKExport`. -/
def buildVKExport
    (N I : ℝ → ℝ → ℝ)
    (hJ : VKStandalone.JensenStripInput N I)
    (hI : VKStandalone.IntegralLogPlusBoundVK I)
    (sigmaStar : ℝ) : Export :=
  VKStandalone.buildVKExport N I hJ hI sigmaStar

/-- Geometric Poisson constant at α = 3/2 (equals 9). -/
def lockedCα : ℝ := VKStandalone.lockedCα

lemma lockedCα_eq_9 : lockedCα = 9 := VKStandalone.lockedCα_eq_9

/-- Assembled K_{ξ,paper} under the locked parameters; depends only on the explicit
near-field budget `Cnear` and the small-height budget `Ksmall` (both provided externally). -/
def lockedKxiPaper (Cnear Ksmall : ℝ) : ℝ :=
  VKStandalone.lockedKxiPaper Cnear Ksmall

/-- The locked Whitney parameters (α = 3/2, c = 1/10). -/
def lockedWhitney : VKStandalone.VKWhitney := VKStandalone.lockedWhitney

/-- The locked VK pair (C_VK, B_VK) = (10^3, 5). -/
def lockedVKPair : ℝ × ℝ := VKStandalone.lockedVKPair

/-- The locked T₀ = e^{30}. -/
def lockedT0 : ℝ := VKStandalone.lockedT0

/-!
## Wiring of Analytic Witnesses (Placeholders)

We provide the concrete wiring for the analytic number theory components here.
These definitions connect the algebraic `buildVKExport` interface to the (future)
analytic proofs. Currently, they use placeholders/sorry, to be filled by the
VK implementation tasks.
-/

/-- Placeholder for the analytic number theory witness N(σ, T). -/
noncomputable def analyticN (σ T : ℝ) : ℝ := 0 -- TODO: Implement

/-- Placeholder for the analytic number theory witness I(σ, T). -/
noncomputable def analyticI (σ T : ℝ) : ℝ := 0 -- TODO: Implement

/-- Placeholder witness for Jensen strip input. -/
noncomputable def witnessJensen : VKStandalone.JensenStripInput analyticN analyticI := by
  sorry

/-- Placeholder witness for Integral log plus bound. -/
noncomputable def witnessIntegral : VKStandalone.IntegralLogPlusBoundVK analyticI := by
  sorry

/-- The fully assembled VK export using the (currently placeholder) analytic witnesses. -/
noncomputable def assembledVK : Export :=
  buildVKExport analyticN analyticI witnessJensen witnessIntegral 0.99 -- sigmaStar placeholder

end Standalone

end VinogradovKorobov
end RH.AnalyticNumberTheory
