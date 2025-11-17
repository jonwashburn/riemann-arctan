import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import rh.RS.sealed.BoundaryWedgeProofCore

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

end VinogradovKorobov
end RH.AnalyticNumberTheory
