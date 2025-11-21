import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.MetricSpace.Basic

open Complex Metric

example (f : ℂ → ℂ) (R M : ℝ) (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hRe : ∀ z ∈ ball 0 R, (f z).re ≤ M) :
    Complex.abs (deriv f 0) ≤ 2 * (M - (f 0).re) / R := by
  apply?
