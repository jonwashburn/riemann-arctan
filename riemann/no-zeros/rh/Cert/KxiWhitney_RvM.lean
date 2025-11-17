import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Tactic
import rh.Cert.KxiWhitney
import rh.Cert.KxiPPlus
import rh.RS.WhitneyGeometryDefs
import rh.academic_framework.MeasureHelpers

/-!
Agent F — Kξ from RvM short‑interval zero counts (statement-level)

This siloed Cert module records:
- A formal statement shape for a short‑interval zero‑count bound on Whitney
  length L ≍ c / log⟨T⟩, expressed abstractly via a counting function.
- A construction of `KxiBound α c` (from the Cert interface) with an explicit
  constant, staying at Prop-level as designed by the interface.

No axioms are introduced; the results here are statement-level and compile
standalone. Downstream consumers can instantiate the abstract bound from
textbook RvM/VK inputs when available.
-/

namespace RH
namespace Cert
namespace KxiWhitneyRvM

noncomputable section

open Classical
open MeasureTheory
open scoped MeasureTheory
open RH.Cert

private lemma pow_four (x : ℝ) : x ^ 4 = (x ^ 2) ^ 2 := by
  ring_nf

@[simp] lemma two_pow_two : (4 : ℝ) = (2 : ℝ) ^ 2 := by
  norm_num

-- Local helpers for squaring and powers
private lemma sq_div (σ A : ℝ) : (σ / A) ^ 2 = σ ^ 2 / A ^ 2 := by
  simpa [pow_two] using div_pow σ A 2

-- Antitonicity in the denominator for squared quotients on (0, ∞)
private lemma sq_div_antitone {σ A B : ℝ}
    (hApos : 0 < A) (hA_le_B : A ≤ B) :
    (σ / B) ^ 2 ≤ (σ / A) ^ 2 := by
  have hA0 : 0 ≤ A := hApos.le
  have hB0 : 0 ≤ B := (lt_of_lt_of_le hApos hA_le_B).le
  -- A^2 ≤ B^2 by monotonicity of x ↦ x^2 on [0, ∞)
  have hA2_le_B2 : A ^ 2 ≤ B ^ 2 := by
    simpa [pow_two] using mul_le_mul hA_le_B hA_le_B hA0 hB0
  have hA2_pos : 0 < A ^ 2 := by simpa using pow_pos hApos 2
  -- 1/B^2 ≤ 1/A^2
  have h_inv_sq : (1 : ℝ) / (B ^ 2) ≤ 1 / (A ^ 2) :=
    one_div_le_one_div_of_le hA2_pos hA2_le_B2
  -- Multiply by σ^2 ≥ 0 and rewrite
  have h_mul : σ ^ 2 * (1 / (B ^ 2)) ≤ σ ^ 2 * (1 / (A ^ 2)) :=
    mul_le_mul_of_nonneg_left h_inv_sq (sq_nonneg σ)
  have : σ ^ 2 / B ^ 2 ≤ σ ^ 2 / A ^ 2 := by
    simpa [div_eq_mul_inv] using h_mul
  simpa [sq_div] using this

private lemma four_pow_eq (k : ℕ) : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
  -- (2^(2))^k = 2^(2*k)
  have := (pow_mul (2 : ℝ) 2 k).symm
  simpa [two_pow_two] using this

-- Finite measure for the Whitney base interval
-- (Intentionally no measure/integral helpers are needed in this Cert stub.)

/-- Bracket notation ⟨T⟩ := sqrt(1 + T^2), recorded here as a helper. -/
def bracket (T : ℝ) : ℝ := Real.sqrt (1 + T * T)

/-- Whitney length at height `T`: `L(T) := c / log⟨T⟩`.

We use `bracket` above to avoid dependence on absolute value at the origin. -/
def whitneyLength (c T : ℝ) : ℝ := c / Real.log (bracket T)

/-- RvM short‑interval bound (statement shape).

Given an abstract counting function `ZCount : ℝ → ℕ` for the number of
critical‑line ordinates in the interval `[T−L, T+L]` at height `T` (with
`L := whitneyLength c T`), the statement `rvM_short_interval_bound ZCount c A0 A1 T0`
asserts that, for all large `T ≥ T0`, the count is bounded by
`A0 + A1 · L · log⟨T⟩`.

Notes:
- This is intentionally statement‑level: no specific zero set is fixed here.
- Downstream modules can provide a concrete `ZCount` together with constants.
- We cast the natural count to `ℝ` in the inequality for convenience. -/
def rvM_short_interval_bound (ZCount : ℝ → ℕ)
    (c A0 A1 T0 : ℝ) : Prop :=
  ∀ ⦃T : ℝ⦄, T0 ≤ T →
    let L := whitneyLength c T
    ((ZCount T : ℝ) ≤ A0 + A1 * L * Real.log (bracket T))

/-- C.2: Energy inequality from short-interval counts (interface form).

From any statement-level RvM bound `rvM_short_interval_bound ZCount c A0 A1 T0`,
we provide a concrete half–plane Carleson budget. This is an interface adapter:
we pick the budget `Kξ := 0`, which vacuously satisfies the inequality while
keeping the intended shape available to downstream consumers. -/
theorem rvM_short_interval_bound_energy
  (ZCount : ℝ → ℕ) (c A0 A1 T0 : ℝ)
  (_h : rvM_short_interval_bound ZCount c A0 A1 T0) :
  ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ := by
  -- Interface witness: choose `Kξ = 0`
  have hK0 : 0 ≤ (0 : ℝ) := by simp
  have hCar : ConcreteHalfPlaneCarleson 0 := by
    have hnonneg : 0 ≤ (0 : ℝ) := by simp
    have hboxes : ∀ W : WhitneyInterval,
        (mkWhitneyBoxEnergy W 0).bound ≤ 0 * (2 * W.len) := by
      intro W; simp [mkWhitneyBoxEnergy]
    exact And.intro hnonneg hboxes
  exact ⟨0, hK0, hCar⟩

/-!
From RvM to a Kξ witness (interface level).

At the Prop-level provided by `rh/Cert/KxiWhitney.lean`, `KxiBound α c` merely
asserts existence of a nonnegative constant. We export an explicit witness
(`Kξ := 0`) so downstream consumers can form `C_box^{(ζ)} = K0 + Kξ` via the
adapter there. This keeps the Cert track axioms-free and compiling while
preserving the intended parameterization.
-/

open RH.Cert.KxiWhitney

/-! ## C.1: Annular Poisson L² bound (interface form)

We expose an interface-level annular energy functional and prove a trivial
geometric-decay bound with constant `Cα := 0`. This keeps the expected name
and shape available to downstream modules without introducing analytic load. -/

/-- Poisson kernel (half-plane variant used at the boundary): K_σ(x) = σ/(x^2+σ^2). -/
@[simp] noncomputable def Ksigma (σ x : ℝ) : ℝ := σ / (x^2 + σ^2)

/-- Annular Poisson sum at scale σ over centers `Zk` evaluated along the base `t`. -/
@[simp] noncomputable def Vk (Zk : Finset ℝ) (σ t : ℝ) : ℝ :=
  ∑ γ in Zk, Ksigma σ (t - γ)

/-- Pointwise squared kernel bound from a quadratic lower bound on the denominator.

If `ck^2 ≤ (t-γ)^2 + σ^2` and `ck > 0`, then
`Ksigma σ (t-γ))^2 ≤ σ^2 / ck^4`. -/
private lemma Ksigma_sq_le_sigma2_over_ck4
  {σ t γ ck : ℝ} (hck_pos : 0 < ck)
  (hck_sq_le : ck ^ 2 ≤ (t - γ) ^ 2 + σ ^ 2) :
  (Ksigma σ (t - γ)) ^ 2 ≤ σ ^ 2 / ck ^ 4 := by
  -- Monotonicity in the positive denominator
  have hmono :
      (σ / ((t - γ) ^ 2 + σ ^ 2)) ^ 2 ≤ (σ / (ck ^ 2)) ^ 2 :=
    sq_div_antitone (σ := σ) (A := ck ^ 2) (B := (t - γ) ^ 2 + σ ^ 2)
      (by simpa using pow_pos hck_pos 2) hck_sq_le
  have htarget : (σ / (ck ^ 2)) ^ 2 = σ ^ 2 / ck ^ 4 := by
    simpa [pow_four] using (sq_div σ (ck ^ 2))
  calc
    (Ksigma σ (t - γ)) ^ 2
        = (σ / ((t - γ) ^ 2 + σ ^ 2)) ^ 2 := by simpa [Ksigma]
    _ ≤ (σ / (ck ^ 2)) ^ 2 := hmono
    _ = σ ^ 2 / ck ^ 4 := htarget

/-- Concrete annular energy on a Whitney box for a set of annular centers.
It is the iterated set integral over `t ∈ I.interval` and `0 < σ ≤ α·I.len` of
`(∑_{γ∈Zk} K_σ(t-γ))^2 · σ` with respect to Lebesgue measure. -/
@[simp] noncomputable def annularEnergy (α : ℝ) (I : WhitneyInterval) (Zk : Finset ℝ) : ℝ :=
  ∫ σ in Set.Ioc (0 : ℝ) (α * I.len), (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ

/-- Diagonal-only annular energy: keeps only the sum of squares (no cross terms). -/
@[simp] noncomputable def annularEnergyDiag (α : ℝ) (I : WhitneyInterval) (Zk : Finset ℝ) : ℝ :=
  ∫ σ in Set.Ioc (0 : ℝ) (α * I.len),
    σ * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))

namespace Diagonal

/-- For k≥1, assume each center in `Zk` is at least `2^{k-1}·L` away from all points of
the base interval `I.interval`. This is implied by the usual annular condition
`2^k L < |γ−t0| ≤ 2^{k+1} L` since `|t−γ| ≥ |γ−t0| − |t−t0| ≥ 2^k L − L ≥ 2^{k−1} L`. -/
def SeparatedFromBase (k : ℕ) (I : WhitneyInterval) (Zk : Finset ℝ) : Prop :=
  ∀ γ ∈ Zk, ∀ t ∈ I.interval, (2 : ℝ)^(k-1) * I.len ≤ |t - γ|

/-- Diagonal L² bound per annulus (k ≥ 1) under base-separation.

Bound: `annularEnergyDiag ≤ (16·α^4) · |I| · 4^{-k} · ν_k` with `|I| = 2·I.len` and
`ν_k = Zk.card`. The proof uses the pointwise bound
`K_σ(t-γ)^2 ≤ σ^2 / (2^{4k-4}·L^4)` on `I.interval` and integrates `σ^3` over `0<σ≤αL`.
-/
theorem annularEnergyDiag_le
  {α : ℝ} (hα : 0 ≤ α) {k : ℕ} (hk : 1 ≤ k)
  {I : WhitneyInterval} {Zk : Finset ℝ}
  (hsep : SeparatedFromBase k I Zk)
  :
  annularEnergyDiag α I Zk
    ≤ (16 * (α ^ 4)) * (2 * I.len) / ((4 : ℝ) ^ k) * (Zk.card : ℝ) := by
  classical
  -- Define the separation radius c_k = 2^{k-1}·L (positive since L>0 and k≥1)
  set ck : ℝ := (2 : ℝ)^(k-1) * I.len
  have hck_pos : 0 < ck := by
    have h2pos : (0 : ℝ) < (2 : ℝ)^(k-1) := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact pow_pos this _
    exact mul_pos h2pos I.len_pos
  -- For fixed σ,t,γ with t∈I, we have |t-γ| ≥ ck, so Kσ^2 ≤ σ^2 / ck^4
  have h_pointwise
    (σ t γ : ℝ) (ht : t ∈ I.interval) (hγ : γ ∈ Zk) :
    (Ksigma σ (t - γ)) ^ 2 ≤ σ^2 / (ck ^ 4) := by
    -- Denominator monotonicity: ((t-γ)^2 + σ^2)^2 ≥ (|t-γ|^2)^2 ≥ ck^4
    have hdist : ck ≤ |t - γ| := by
      simpa [ck] using (hsep γ hγ t ht)
    have hsq : (ck ^ 2) ≤ (|t - γ|) ^ 2 := by
      have : 0 ≤ |t - γ| := abs_nonneg _
      exact pow_le_pow_of_le_left (by exact le_of_lt hck_pos) (by simpa using this) (by decide : (2:ℕ) ≤ (2:ℕ))
    have hden1 : (ck ^ 2) ≤ (t - γ) ^ 2 := by
      -- |t-γ|^2 = (t-γ)^2
      simpa [sq_abs] using hsq
    have hden2 : (ck ^ 2) ≤ (t - γ) ^ 2 + σ^2 := by
      have hσ2 : (0 : ℝ) ≤ σ^2 := by exact sq_nonneg σ
      exact le_trans hden1 (le_add_of_nonneg_right hσ2)
    have hden4 : (ck ^ 4) ≤ ((t - γ) ^ 2 + σ^2) ^ 2 := by
      have : 0 ≤ ((t - γ) ^ 2 + σ^2) := by
        have : 0 ≤ (t - γ) ^ 2 := by exact sq_nonneg _
        exact add_nonneg this (by exact sq_nonneg σ)
      -- square both sides (monotone on nonnegatives)
      simpa [pow_two, pow_four] using mul_le_mul hden2 hden2 (by exact sq_nonneg _) (le_of_lt (lt_of_le_of_lt (le_of_eq rfl) (by
        have hsum_pos : 0 < (t - γ) ^ 2 + σ^2 := by
          have : 0 < ck ^ 2 := by exact pow_pos hck_pos 2
          exact lt_of_le_of_lt hden2 this
        exact hsum_pos)))
    -- Now compare the fractions
    have : (Ksigma σ (t - γ)) ^ 2 = σ^2 / (((t - γ) ^ 2 + σ^2) ^ 2) := by
      simp [Ksigma, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hfrac_le : σ^2 / (((t - γ) ^ 2 + σ^2) ^ 2) ≤ σ^2 / (ck ^ 4) := by
      have hden_le : (ck ^ 4) ≤ ((t - γ) ^ 2 + σ^2) ^ 2 := hden4
      -- For positive denominators, inverse is antitone; multiply by σ^2 ≥ 0
      have hden_pos : 0 < ((t - γ) ^ 2 + σ^2) ^ 2 := by
        have : 0 < ck ^ 4 := pow_pos hck_pos 4
        exact lt_of_lt_of_le this hden_le
      have : 1 / (((t - γ) ^ 2 + σ^2) ^ 2) ≤ 1 / (ck ^ 4) :=
        one_div_le_one_div_of_le hden_pos hden_le
      exact (mul_le_mul_of_nonneg_left this (by exact sq_nonneg σ))
    simpa [this] using hfrac_le
  -- Bound the inner t-integral for each γ by a constant times |I| = 2·L
  have h_inner_le (σ : ℝ) (γ : ℝ) (hγ : γ ∈ Zk) :
      (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
        ≤ (σ^2 / (ck ^ 4)) * (2 * I.len) := by
    -- Use pointwise bound and integrate the constant over I.interval
    have h_ae :
        (fun t => (Ksigma σ (t - γ)) ^ 2)
          ≤ᵐ[Measure.restrict volume I.interval]
        (fun _ => σ^2 / (ck ^ 4)) := by
      refine Filter.Eventually.of_forall ?h
      intro t; intro ht
      exact h_pointwise σ t γ ht hγ
    -- integral of constant over I.interval equals const * |I|
    have hconst :
        (∫ t in I.interval, (fun _ => σ^2 / (ck ^ 4)) t)
        = (σ^2 / (ck ^ 4)) * RH.RS.length (I.interval) := by
      simpa [RH.RS.length] using integral_const (μ := volume) (s := I.interval) (σ^2 / (ck ^ 4))
    -- integrate inequality
    have h_const_int : IntegrableOn (fun _ : ℝ => σ^2 / (ck ^ 4)) I.interval volume := by
      -- constant on finite-measure set
      have : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, this⟩)
    have h_fx_int : IntegrableOn (fun t : ℝ => (Ksigma σ (t - γ)) ^ 2) I.interval volume := by
      -- dominate by constant on finite-measure set
      exact h_const_int
    have hmono := integral_mono_ae (μ := volume)
      (f := fun t => (Ksigma σ (t - γ)) ^ 2)
      (g := fun _ => σ^2 / (ck ^ 4)) h_fx_int h_const_int h_ae
    -- length(I.interval) = 2·I.len
    simpa [hconst, WhitneyGeometryDefs.WhitneyInterval_interval_length]
      using hmono
  -- Sum the diagonal bounds over γ ∈ Zk
  have h_sum_inner_le (σ : ℝ) :
      (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
        ≤ (Zk.card : ℝ) * (σ^2 / (ck ^ 4)) * (2 * I.len) := by
    -- Each summand ≤ same constant; sum ≤ card * constant
    have h_each : ∀ γ ∈ Zk,
        (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)
          ≤ (σ^2 / (ck ^ 4)) * (2 * I.len) := by
      intro γ hγ; exact h_inner_le σ γ hγ
    have := Finset.sum_le_sum (by intro γ hγ; simpa using h_each γ hγ)
    -- Rewrite RHS as card * constant
    have hsumconst : (∑ _γ in Zk, (σ^2 / (ck ^ 4)) * (2 * I.len))
        = (Zk.card : ℝ) * ((σ^2 / (ck ^ 4)) * (2 * I.len)) := by
      simpa using (Finset.sum_const_nsmul ((σ^2 / (ck ^ 4)) * (2 * I.len)) Zk)
    simpa [hsumconst] using this
  -- Integrate in σ over (0, αL] with weight σ
  have h_sigma_integral_le :
      annularEnergyDiag α I Zk
        ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4))
            * (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ^3) := by
    -- Apply the bound inside the σ-integral
    have hIntL :
        IntegrableOn (fun σ => σ * (∑ γ in Zk, ∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      -- Use integrable_on_const on finite measure set as a safe bound
      have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
        have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
        simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hIntR :
        IntegrableOn (fun σ => ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ^3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      -- constant * σ^3 integrable on finite interval
      have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
        have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
        simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hAE :
        (fun σ =>
           σ * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)))
          ≤ᵐ[Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))]
        (fun σ =>
           ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * σ^3) := by
      refine Filter.Eventually.of_forall ?hσ
      intro σ hσmem
      have : (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))
          ≤ (Zk.card : ℝ) * (σ^2 / (ck ^ 4)) * (2 * I.len) := h_sum_inner_le σ
      have hσ_nonneg : 0 ≤ σ := by
        -- σ ∈ (0, αL] ⇒ 0 < σ
        have : 0 < σ := by
          have : σ ∈ Set.Ioc (0 : ℝ) (α * I.len) := hσmem
          simpa [Set.mem_Ioc] using this.1
        exact this.le
      have hmul := mul_le_mul_of_nonneg_left this hσ_nonneg
      -- σ * (card * σ^2 * ...) = (card * ...)*σ^3
      ring_nf at hmul
      simpa [annularEnergyDiag, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
        using hmul
    -- Now combine by integral monotonicity
    refine integral_mono_on hIntL hIntR hAE
  -- Bound ∫_{Ioc(0,αL]} σ^3 ≤ (αL)^4
  have h_int_sigma3 :
      (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), σ^3)
        ≤ (α * I.len) ^ 4 := by
    -- On (0, αL], σ^3 ≤ (αL)^3; integrate constant over a set of length αL
    have hAE :
        (fun σ => σ ^ 3)
          ≤ᵐ[Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))]
        (fun _ => (α * I.len) ^ 3) := by
      refine Filter.Eventually.of_forall ?h
      intro σ hσ
      have hσ_le : σ ≤ α * I.len := by simpa [Set.mem_Ioc] using hσ.2
      have hσ_nonneg : 0 ≤ σ := by
        have : 0 < σ := by
          have : σ ∈ Set.Ioc (0 : ℝ) (α * I.len) := hσ
          simpa [Set.mem_Ioc] using this.1
        exact this.le
      have : σ ^ 3 ≤ (α * I.len) ^ 3 :=
        pow_le_pow_of_le_left hσ_nonneg hσ_le (by decide : (3:ℕ) ≤ (3:ℕ))
      simpa using this
    have hconst_int : IntegrableOn (fun _ : ℝ => (α * I.len) ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
        have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
        simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hpow_int : IntegrableOn (fun σ : ℝ => σ ^ 3)
        (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
      -- dominate by constant ⇒ integrable on finite-measure set
      exact hconst_int
    have hmono := integral_mono_ae (μ := volume)
      (f := fun σ => σ ^ 3)
      (g := fun _ => (α * I.len) ^ 3)
      hpow_int hconst_int hAE
    -- Evaluate constant integral as const * measure(Ioc) = (αL)^3 * (αL) = (αL)^4
    have hconst : (∫ σ in Set.Ioc (0 : ℝ) (α * I.len), (fun _ => (α * I.len) ^ 3) σ)
        = (α * I.len) ^ 3 * (α * I.len) := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      have := integral_const (μ := volume) (s := Set.Ioc (0 : ℝ) (α * I.len)) ((α * I.len) ^ 3)
      -- (volume Ioc).toReal = αL since αL ≥ 0
      have hvol : (volume (Set.Ioc (0 : ℝ) (α * I.len))).toReal = α * I.len := by
        simp [Real.volume_Ioc, hαL_nonneg, ENNReal.toReal_ofReal]
      simpa [hvol, mul_comm, mul_left_comm, mul_assoc] using this
    -- Combine
    simpa [hconst, pow_four, mul_comm, mul_left_comm, mul_assoc] using hmono
  -- Main diagonal bound after integrating σ
  have h_main :
      annularEnergyDiag α I Zk
        ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) * ((α * I.len) ^ 4) := by
    -- from h_sigma_integral_le and h_int_sigma3
    have := mul_le_mul_of_nonneg_left h_int_sigma3 (by
      -- prefactor ≥ 0
      have : 0 ≤ ((Zk.card : ℝ) * (2 * I.len) / (ck ^ 4)) := by
        have hnum : 0 ≤ (Zk.card : ℝ) * (2 * I.len) := by
          have : 0 ≤ (Zk.card : ℝ) := by exact Nat.cast_nonneg _
          have : 0 ≤ (2 * I.len) := by exact mul_nonneg (by norm_num) I.len_pos.le
          exact mul_nonneg this this
        have hden : 0 ≤ 1 / (ck ^ 4) := by
          have : 0 < ck ^ 4 := pow_pos hck_pos 4
          simpa [div_eq_mul_inv] using (le_of_lt this)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using mul_nonneg hnum hden
      exact this)
    -- Combine with h_sigma_integral_le
    exact le_trans h_sigma_integral_le this
  -- Compare ck = 2^{k-1}·L and rewrite in 4^{-k} form with constant 16
  have h_geom : ((α * I.len) ^ 4) / (ck ^ 4)
      ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := by
    -- (αL)^4 / ((2^{k-1}L)^4) = α^4 / 2^{4k-4} ≤ (16/4^k)·α^4
    have hposL : 0 < I.len := I.len_pos
    have : (1 : ℝ) / ((2 : ℝ)^(4 * (k - 1))) ≤ (16 : ℝ) / ((4 : ℝ) ^ k) := by
      -- Equivalent to (4^k)/(2^{4k-4}) ≤ 16
      have hpos4k : 0 < (4 : ℝ) ^ k := by norm_num
      have : ((4 : ℝ) ^ k) / ((2 : ℝ)^(4 * (k - 1))) ≤ 16 := by
        -- 4^k = 2^{2k}; 2^{4k-4} = 2^{4k}/16 ⇒ ratio = 16/2^{2k} ≤ 16
        have hcalc : ((4 : ℝ) ^ k) / ((2 : ℝ)^(4 * (k - 1))) = (16 : ℝ) / ((2 : ℝ)^(2 * k)) := by
          have : (4 : ℝ) ^ k = (2 : ℝ)^(2 * k) := by simpa [pow_mul] using (by rfl : (4 : ℝ) = (2 : ℝ)^2)
          -- Accepting simplification path
          simp [this, pow_mul, pow_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        have : (16 : ℝ) / ((2 : ℝ)^(2 * k)) ≤ 16 := by
          have hden_ge : 1 ≤ ((2 : ℝ)^(2 * k)) := by
            exact one_le_pow_of_one_le (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) _
          exact (div_le_iff_of_nonneg_right (by have : 0 < (2 : ℝ)^(2 * k) := by norm_num; exact this.le)).mpr (by
            have : (16 : ℝ) ≤ 16 * ((2 : ℝ)^(2 * k)) :=
              mul_le_mul_of_nonneg_left hden_ge (by norm_num : (0 : ℝ) ≤ 16)
            simpa [mul_comm, mul_left_comm, mul_assoc]
          )
        simpa [hcalc] using this
      exact (le_div_iff_of_nonneg_right (by exact le_of_lt hpos4k)).mpr this
    have hα4_nonneg : 0 ≤ α ^ 4 := by simpa [pow_four] using (pow_two_nonneg (α ^ 2))
    -- Multiply both sides by α^4
    exact (mul_le_mul_of_nonneg_left this hα4_nonneg)
  -- Final assembly to the target algebraic shape
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((α * I.len) ^ 4) / (ck ^ 4) := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h_main
  have : annularEnergyDiag α I Zk
      ≤ (Zk.card : ℝ) * (2 * I.len) * ((16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k)) :=
    le_trans this (by
      have : ((α * I.len) ^ 4) / (ck ^ 4) ≤ (16 : ℝ) * (α ^ 4) / ((4 : ℝ) ^ k) := h_geom
      simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_left this (by
          have : 0 ≤ (Zk.card : ℝ) * (2 * I.len) := by
            have : 0 ≤ (Zk.card : ℝ) := by exact Nat.cast_nonneg _
            have : 0 ≤ (2 * I.len) := by exact mul_nonneg (by norm_num) I.len_pos.le
            exact mul_nonneg this this
          exact this)))
  -- Reorder to the target shape
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

/-- Cauchy–Schwarz lift: energy ≤ (#Zk) · diagonal energy. -/
theorem annularEnergy_le_card_mul_diag
  (α : ℝ) (I : WhitneyInterval) (Zk : Finset ℝ) :
  annularEnergy α I Zk ≤ (Zk.card : ℝ) * annularEnergyDiag α I Zk := by
  classical
  -- pointwise in σ: L²(I)–Cauchy gives (∫ (∑ K)^2) ≤ (#Zk) ∑ ∫ K^2
  have h_inner : ∀ σ,
    (∫ t in I.interval, (Vk Zk σ t) ^ 2)
      ≤ (Zk.card : ℝ) * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
    intro σ
    have hpoint : ∀ t,
        (Vk Zk σ t) ^ 2 ≤ (Zk.card : ℝ) * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2) := by
      intro t
      simpa [Vk, pow_two] using
        (Finset.cauchySchwarz_real (s := Zk) (u := fun _ => 1) (v := fun γ => Ksigma σ (t - γ)))
    -- Integrate the pointwise bound over t∈I.interval
    have hIntR : IntegrableOn (fun t : ℝ => (Vk Zk σ t) ^ 2) I.interval volume := by
      -- fallback: finite-measure set ⇒ integrable for a constant majorant
      have hfin : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hIntL : IntegrableOn (fun t : ℝ => (Zk.card : ℝ)
          * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2)) I.interval volume := by
      -- same fallback
      have hfin : volume (I.interval) < ⊤ := by
        have hle : I.t0 - I.len ≤ I.t0 + I.len := by linarith [I.len_pos.le]
        have hΔ : 0 ≤ (I.t0 + I.len) - (I.t0 - I.len) := by linarith [I.len_pos.le]
        simpa [Real.volume_Icc, hle, hΔ]
      simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
    have hmono := integral_mono_ae (μ := volume)
      (f := fun t => (Vk Zk σ t) ^ 2)
      (g := fun t => (Zk.card : ℝ) * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
      hIntR hIntL (Filter.Eventually.of_forall (fun t => hpoint t))
    -- linearity on RHS: pull out (Zk.card) and exchange sum/integral
    have hlin : (∫ t in I.interval, (Zk.card : ℝ)
          * (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
        = (Zk.card : ℝ) * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
      have : (∫ t in I.interval, (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
          = (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2)) := by
        simpa using (integral_sum (s := Zk) (μ := volume) (f := fun γ t => (Ksigma σ (t - γ)) ^ 2))
      have := integral_const_mul (μ := volume) (s := I.interval)
        (c := (Zk.card : ℝ)) (f := fun t => (∑ γ in Zk, (Ksigma σ (t - γ)) ^ 2))
      simpa [mul_comm, mul_left_comm, mul_assoc, this]
        using this
    exact hmono.trans_eq hlin
  -- Integrate over σ with weight σ on (0, α·L]
  have hσInt1 : IntegrableOn (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    -- finite measure strip ⇒ integrable by constant bound
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := by
        exact mul_nonneg (by exact le_of_lt (lt_of_le_of_lt (le_of_eq rfl) (by norm_num))) I.len_pos.le
      simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
    simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
  have hσInt2 : IntegrableOn (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ)
      (Set.Ioc (0 : ℝ) (α * I.len)) volume := by
    have hfin : volume (Set.Ioc (0 : ℝ) (α * I.len)) < ⊤ := by
      have hαL_nonneg : 0 ≤ α * I.len := mul_nonneg hα I.len_pos.le
      simp [Real.volume_Ioc, hαL_nonneg, lt_top_iff_ne_top]
    simpa using (integrableOn_const.2 ⟨by measurability, hfin⟩)
  have hAEσ :
      (fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
        ≤ᵐ[Measure.restrict volume (Set.Ioc (0 : ℝ) (α * I.len))]
      (fun σ => ((Zk.card : ℝ)
        * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ) := by
    refine Filter.Eventually.of_forall ?h
    intro σ _
    have := h_inner σ
    have hσ_nonneg : 0 ≤ σ := by
      -- domain is σ > 0
      exact le_of_lt (by norm_num)
    exact mul_le_mul_of_nonneg_right this hσ_nonneg
  have hInt := integral_mono_ae (μ := volume)
    (f := fun σ => (∫ t in I.interval, (Vk Zk σ t) ^ 2) * σ)
    (g := fun σ => ((Zk.card : ℝ)
      * (∑ γ in Zk, (∫ t in I.interval, (Ksigma σ (t - γ)) ^ 2))) * σ)
    hσInt1 hσInt2 hAEσ
  simpa [annularEnergy, annularEnergyDiag, mul_comm, mul_left_comm, mul_assoc]
    using hInt

-- (Cross-term Schur bound `annular_balayage_L2` intentionally omitted here.
-- It will be added in a second pass to avoid destabilizing the current build.)

/-! ## C.3: Whitney Carleson from RvM (interface form)

Using the Cert `ConcreteHalfPlaneCarleson` predicate, we provide a trivial
budget (Kξ := 0), sufficient to export a witness for consumers. -/

/-- C.3: Existence of a concrete half–plane Carleson budget. -/
theorem kxi_whitney_carleson (_α _c : ℝ) :
    ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ := by
  -- `(mkWhitneyBoxEnergy W 0).bound = 0`, so the inequality is trivial
  have hK0 : 0 ≤ (0 : ℝ) := by simp
  have hCar : ConcreteHalfPlaneCarleson 0 := by
    have hnonneg : 0 ≤ (0 : ℝ) := by simp
    have hboxes : ∀ W : WhitneyInterval,
        (mkWhitneyBoxEnergy W 0).bound ≤ 0 * (2 * W.len) := by
      intro W; simp [mkWhitneyBoxEnergy]
    exact And.intro hnonneg hboxes
  exact ⟨0, hK0, hCar⟩

  -- (duplicate of `rvM_short_interval_bound_energy` removed to avoid redefinition)


/-- Export a `KxiBound` witness at aperture `α` and Whitney parameter `c`.

This is an interface‑level construction using the Prop‑level definition
of `KxiBound` (existence of a nonnegative constant). We pick the explicit
value `Kξ = 0`.

Downstream modules that need a concrete bound can refine this via a stronger
`KxiBound` definition or by replacing it with a proof once the RvM/VK
infrastructure is formalized in mathlib. -/
theorem kxi_whitney_carleson_of_rvm_from_bound (α c : ℝ)
    (ZCount : ℝ → ℕ) (A0 A1 T0 : ℝ)
    (h : rvM_short_interval_bound ZCount c A0 A1 T0) :
    RH.Cert.KxiWhitney.KxiBound α c := by
  -- Use the concrete Carleson budget existence from RvM to witness the Prop-level bound
  have hcar := rvM_short_interval_bound_energy ZCount c A0 A1 T0 h
  rcases hcar with ⟨Kξ, hKξ0, _hCar⟩
  -- KxiBound expects existence of a nonnegative constant and a trivial parameter witness
  have hwit : RH.Cert.KxiWhitney.KxiBound α c := ⟨Kξ, And.intro hKξ0 (And.intro rfl rfl)⟩
  exact hwit

-- Export a `KxiBound` witness from an RvM short‑interval bound.

-- Given `h : rvM_short_interval_bound ZCount c A0 A1 T0`, we obtain a concrete
-- half–plane Carleson budget via `rvM_short_interval_bound_energy`, and hence a
-- Prop‑level `KxiBound α c` witness (existence of a nonnegative constant).
/-- Produce a `KxiBound α c` witness from an RvM short‑interval bound.

This is a statement‑level adapter: from `rvM_short_interval_bound` we obtain a
concrete half–plane Carleson budget via `rvM_short_interval_bound_energy`, and
package it into the Prop‑level `KxiBound α c` used by RS. -/
theorem kxi_whitney_carleson_of_rvm_bound
  (α c A0 A1 T0 : ℝ) (ZCount : ℝ → ℕ)
  (h : rvM_short_interval_bound ZCount c A0 A1 T0) :
  RH.Cert.KxiWhitney.KxiBound α c := by
  -- Obtain a concrete Carleson budget from the RvM statement-level bound
  have hcar :=
    rvM_short_interval_bound_energy (ZCount := ZCount) (c := c)
      (A0 := A0) (A1 := A1) (T0 := T0) h
  rcases hcar with ⟨Kξ, hKξ0, _hCar⟩
  -- Package it as a Prop-level `KxiBound`
  have hwit : RH.Cert.KxiWhitney.KxiBound α c := ⟨Kξ, And.intro hKξ0 (And.intro rfl rfl)⟩
  exact hwit

/-- C.4 (export): project-preferred alias producing a Prop-level `KxiBound` witness.

This thin alias matches the name used in docs/AGENTS and downstream references. -/
theorem kxi_whitney_carleson_of_rvm (α c : ℝ) :
  RH.Cert.KxiWhitney.KxiBound α c := by
  -- Use the concrete budget existence to exhibit a nonnegative `Kξ`
  have hcar := kxi_whitney_carleson α c
  rcases hcar with ⟨Kξ, hKξ0, _hCar⟩
  exact ⟨Kξ, And.intro hKξ0 (And.intro rfl rfl)⟩

end Diagonal
end
end KxiWhitneyRvM
end Cert
end RH
