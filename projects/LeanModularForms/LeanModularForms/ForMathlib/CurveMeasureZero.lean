/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.HausdorffDimension
import LeanModularForms.ForMathlib.PiecewiseC1Path

/-!
# Curve images have Lebesgue measure zero

The image of a Lipschitz map from a 1-dimensional space into `ℂ` has 2-D Lebesgue
measure zero. This is the foundation for proving that for any open `U ⊆ ℂ` with
nonempty intersection with a continuous Lipschitz curve, there exists a point in
`U` off the curve (needed for the Cauchy integral formula trick in
`contourIntegral_eq_zero_of_nullHomologous`).

## Main results

* `volume_image_lipschitz_real_zero` — Lipschitz image of a subset of `ℝ` has
  Lebesgue measure `0` in `ℂ`.
* `exists_mem_not_mem_image_of_isOpen_of_lipschitz` — for open nonempty `U` and
  Lipschitz `f : ℝ → ℂ`, there exists `w₀ ∈ U` off `f '' s`.
-/

open MeasureTheory Measure Set Filter Topology

namespace ForMathlib

/-- The 2-dimensional Hausdorff measure on `ℝ` is zero on any set, since
`finrank ℝ ℝ = 1 < 2`. -/
theorem hausdorffMeasure_two_real_zero (s : Set ℝ) : (μH[2] : Measure ℝ) s = 0 := by
  have h : (μH[2] : Measure ℝ) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt (by simp [Module.finrank_self])
  simp [h]

/-- The 2-dimensional Hausdorff measure of the image of a set `s ⊆ ℝ` under a
Lipschitz map `f : ℝ → ℂ` is zero. -/
theorem hausdorffMeasure_two_lipschitz_image_zero {K : NNReal} {f : ℝ → ℂ}
    (hf : LipschitzWith K f) (s : Set ℝ) : μH[2] (f '' s) = 0 := by
  have h_le := hf.hausdorffMeasure_image_le (d := 2) (by norm_num) s
  rw [hausdorffMeasure_two_real_zero] at h_le
  simpa using h_le

/-- The Lebesgue volume in `ℂ` of the image of a set `s ⊆ ℝ` under a Lipschitz
map `f : ℝ → ℂ` is zero.

Volume on `ℂ` is absolutely continuous w.r.t. the 2-dimensional Hausdorff measure
(both are `AddHaarMeasure`s on a 2-dim real normed space), so vanishing of
Hausdorff 2-measure implies vanishing of volume. -/
theorem volume_image_lipschitz_real_zero {K : NNReal} {f : ℝ → ℂ}
    (hf : LipschitzWith K f) (s : Set ℝ) : volume (f '' s) = 0 := by
  have h_finrank : ((Module.finrank ℝ ℂ : ℕ) : ℝ) = 2 := by
    exact_mod_cast Complex.finrank_real_complex
  have h_haar : (μH[2] : Measure ℂ).IsAddHaarMeasure := by
    rw [show (2 : ℝ) = ((Module.finrank ℝ ℂ : ℕ) : ℝ) from h_finrank.symm]
    exact isAddHaarMeasure_hausdorffMeasure
  have h_ac : (volume : Measure ℂ).AbsolutelyContinuous (μH[2]) :=
    absolutelyContinuous_isAddHaarMeasure _ _
  exact h_ac (hausdorffMeasure_two_lipschitz_image_zero hf s)

/-- For open nonempty `U ⊆ ℂ` and Lipschitz `f : ℝ → ℂ`, there exists `w₀ ∈ U`
off `f '' s`: Lipschitz images have measure zero, so their complement in `U`
has positive measure and in particular is nonempty. -/
theorem exists_mem_not_mem_image_of_isOpen_of_lipschitz {U : Set ℂ} (hU_open : IsOpen U)
    (hU_ne : U.Nonempty) {K : NNReal} {f : ℝ → ℂ} (hf : LipschitzWith K f) (s : Set ℝ) :
    ∃ w₀ ∈ U, w₀ ∉ f '' s := by
  by_contra! h
  have h_zero : volume U ≤ 0 := by
    rw [← volume_image_lipschitz_real_zero hf s]
    exact measure_mono h
  exact (h_zero.trans_lt (hU_open.measure_pos _ hU_ne)).false

/-- If `γ.toPath.extend` is Lipschitz and `U` is open nonempty, there exists
`w₀ ∈ U` with `γ` avoiding `w₀`.

The Lipschitz hypothesis is supplied by the caller; it holds automatically for
`PwC1Immersion` with bounded derivative (typical case). -/
theorem exists_mem_not_mem_path_image_of_isOpen {x y : ℂ} (γ : PiecewiseC1Path x y)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) :
    ∃ w₀ ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t ≠ w₀ := by
  obtain ⟨w₀, hw₀_mem, hw₀_off⟩ :=
    exists_mem_not_mem_image_of_isOpen_of_lipschitz hU_open hU_ne hLip (Icc (0 : ℝ) 1)
  exact ⟨w₀, hw₀_mem, fun t ht heq => hw₀_off ⟨t, ht, heq⟩⟩

end ForMathlib
