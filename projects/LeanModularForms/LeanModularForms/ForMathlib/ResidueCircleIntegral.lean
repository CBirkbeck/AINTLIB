/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.Residue
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Residue via Circle Integral

Properties of the residue `residue f z₀`, defined as the circle-integral limit
`lim_{r→0⁺} (2πi)⁻¹ ∮_{|z-z₀|=r} f(z) dz`.

## Main results

* `residue_eq_zero_of_analyticAt` — analytic functions have zero residue.
* `residue_eq_zero_of_eventually_differentiableAt` — functions differentiable on a
  neighborhood have zero residue.
* `circleIntegral_simple_pole_eq` — for small `r`, the normalized circle integral of
  a function with a simple pole equals its pole coefficient `c`.
* `residue_eq_of_simple_pole_decomp` — for simple poles, the residue equals the pole
  coefficient.
* `residue_eq_coeff` — `residue f z₀ = h.coeff` when `h : HasSimplePoleAt f z₀`.
* `residue_congr` — residue depends only on local behavior in a punctured neighborhood.
* `norm_two_pi_i_inv_circleIntegral_tendsto_zero` — the normalized circle integral of a
  continuous function tends to zero as the radius tends to zero.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Interval Real

noncomputable section

private lemma limUnder_eq_of_eventuallyEq {α β : Type*} [TopologicalSpace β] [Nonempty β]
    {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) : l.limUnder f = l.limUnder g := by
  grind [Filter.limUnder, Filter.map_congr]

/-- The circle integral of `f` vanishes when `f` is analytic on an open ball strictly
containing the circle. -/
private lemma circleIntegral_eq_zero_of_analyticOnNhd_ball {f : ℂ → ℂ} {z₀ : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (ball z₀ R)) :
    ∮ z in C(z₀, r), f z = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
    (hf.continuousOn.mono (closedBall_subset_ball hrR))
    (fun z ⟨hz, _⟩ => (hf z (ball_subset_ball hrR.le hz)).differentiableAt)

/-- A function that is analytic at `z₀` has residue zero. -/
theorem residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) : residue f z₀ = 0 := by
  obtain ⟨R, hR_pos, hR_an⟩ := hf.exists_ball_analyticOnNhd
  refine (tendsto_nhds_of_eventually_eq ?_).limUnder_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hR_pos] with r hr_lt hr_pos
  rw [circleIntegral_eq_zero_of_analyticOnNhd_ball hr_pos hr_lt hR_an, mul_zero]

/-- If `f` and `g` agree in a punctured neighborhood of `z₀`, they have the same
residue. The proof shows that the circle integrals agree for all sufficiently small
radii, so the `limUnder`s coincide. -/
theorem residue_congr {f g : ℂ → ℂ} {z₀ : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] z₀, f z = g z) : residue f z₀ = residue g z₀ := by
  apply limUnder_eq_of_eventuallyEq
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at h
  obtain ⟨ε, hε_pos, hε⟩ := h
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hε_pos] with r hr_lt hr_pos
  simp only [mem_Ioi, mem_Iio] at hr_pos hr_lt
  congr 1
  refine circleIntegral.integral_congr hr_pos.le fun z hz => ?_
  have h_ne : z ≠ z₀ := fun heq => by
    rw [heq, mem_sphere, dist_self] at hz; linarith
  exact hε ⟨mem_ball.mpr (mem_sphere.mp hz ▸ hr_lt), mem_compl_singleton_iff.mpr h_ne⟩

end
