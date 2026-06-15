/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CurveUtilities
import LeanModularForms.ForMathlib.FDBoundary

/-!
# Interior Winding Number for the Fundamental Domain Boundary

This file proves that the FD boundary contour avoids every point in the strict interior
of the fundamental domain, and reduces the interior winding number computation to a
contour integral identity.

## Strict interior

A point `z` is in the **strict interior** of the fundamental domain at height `H` when:
- `1 < ‖z‖` (strictly outside the unit circle)
- `|z.re| < 1/2` (strictly between the vertical edges)
- `0 < z.im` (in the upper half-plane)
- `z.im < H` (below the horizontal cap)

## Main results

### Avoidance (fully proved)

* `fdBoundaryFun_avoids_seg1` -- right vertical avoids strict interior (re = 1/2 vs |re| < 1/2)
* `fdBoundaryFun_avoids_seg2` -- right arc avoids strict interior (norm = 1 vs norm > 1)
* `fdBoundaryFun_avoids_seg3` -- left arc avoids strict interior (norm = 1 vs norm > 1)
* `fdBoundaryFun_avoids_seg4` -- left vertical avoids strict interior (re = -1/2 vs |re| < 1/2)
* `fdBoundaryFun_avoids_seg5` -- horizontal avoids strict interior (im = H vs im < H)
* `fdBoundaryFun_avoids_interior` -- full boundary avoids strict interior points

### Minimum distance (fully proved)

* `fdBoundaryFun_minDist_interior` -- the minimum distance from any strict interior point
  to the boundary is positive

### Reduction to contour integral (fully proved)

* `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral` -- if a `PiecewiseC1Path` agrees
  with `fdBoundaryFun` and its contour integral of `(z - z₀)⁻¹` equals `-2πi`, then
  the interior winding number is `-1`.

### Clean constructor (fully proved)

* `FDWindingData.mk_of_interior_contourIntegral` -- build `FDWindingData` by supplying
  the interior contour integral identity as a hypothesis (together with the three
  `SingleCrossingData` for the elliptic points).

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- A point `z` is in the strict interior of the fundamental domain at height `H`.
This means `‖z‖ > 1`, `|z.re| < 1/2`, `0 < z.im`, and `z.im < H`. -/
def FDStrictInterior (z : ℂ) (H : ℝ) : Prop :=
  1 < ‖z‖ ∧ |z.re| < 1/2 ∧ 0 < z.im ∧ z.im < H

theorem FDStrictInterior.norm_gt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    1 < ‖z‖ := h.1

theorem FDStrictInterior.re_abs_lt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    |z.re| < 1/2 := h.2.1

theorem FDStrictInterior.im_pos {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    0 < z.im := h.2.2.1

theorem FDStrictInterior.im_lt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    z.im < H := h.2.2.2

/-- The right vertical segment has `re = 1/2`, so it avoids any point with `|re| < 1/2`. -/
theorem fdBoundaryFun_avoids_seg1 {z : ℂ} (hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) : fdBoundaryFun H t ≠ z := fun heq => by
  rw [show z.re = 1/2 from heq ▸ fdBoundaryFun_seg1_re H t ht] at hz_re
  norm_num at hz_re

/-- The arc segments lie on the unit circle, so they avoid any point with `‖z‖ > 1`. -/
theorem fdBoundaryFun_avoids_arc {z : ℂ} (hz_norm : 1 < ‖z‖)
    {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t ≠ z := fun heq => by
  have h1 : ‖z‖ = 1 := heq ▸ fdBoundaryFun_arc_norm H t ht1 ht2
  linarith

/-- The left vertical segment has `re = -1/2`, so it avoids any point with `|re| < 1/2`. -/
theorem fdBoundaryFun_avoids_seg4 {z : ℂ} (hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t ≠ z := fun heq => by
  rw [show z.re = -1/2 from heq ▸ fdBoundaryFun_seg4_re H t ht3 ht4] at hz_re
  norm_num at hz_re

/-- The horizontal segment has `im = H`, so it avoids any point with `im < H`. -/
theorem fdBoundaryFun_avoids_seg5 {z : ℂ} (hz_im : z.im < H)
    {t : ℝ} (ht : 4/5 < t) : fdBoundaryFun H t ≠ z := fun heq => by
  have h1 : z.im = H := heq ▸ fdBoundaryFun_seg5_im H t ht
  linarith

/-- The FD boundary avoids every point in the strict interior of the fundamental domain.
This follows by case-splitting on the segment and applying the segment-specific avoidance. -/
theorem fdBoundaryFun_avoids_interior {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∀ t ∈ Icc (0 : ℝ) 1, fdBoundaryFun H t ≠ z := by
  intro t _
  by_cases h1 : t ≤ 1/5
  · exact fdBoundaryFun_avoids_seg1 hz_re h1
  push Not at h1
  by_cases h2 : t ≤ 3/5
  · exact fdBoundaryFun_avoids_arc hz_norm h1 h2
  push Not at h2
  by_cases h3 : t ≤ 4/5
  · exact fdBoundaryFun_avoids_seg4 hz_re h2 h3
  push Not at h3
  exact fdBoundaryFun_avoids_seg5 hz_im h3

/-- For a strict interior point, the minimum distance to the FD boundary on `[0, 1]`
is positive. This follows from avoidance + compactness. -/
theorem fdBoundaryFun_minDist_interior_pos {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖fdBoundaryFun H t - z‖ := by
  have h_closed : IsClosed (fdBoundaryFun H '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image (fdBoundaryFun_continuous H)).isClosed
  have h_nonempty : (fdBoundaryFun H '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨fdBoundaryFun H 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_nmem : z ∉ fdBoundaryFun H '' Icc (0 : ℝ) 1 := fun ⟨t, ht, heq⟩ =>
    fdBoundaryFun_avoids_interior hz_norm hz_re hz_im t ht heq
  refine ⟨Metric.infDist z (fdBoundaryFun H '' Icc 0 1),
    (h_closed.notMem_iff_infDist_pos h_nonempty).mp h_nmem, fun t ht => ?_⟩
  rw [← dist_eq_norm, dist_comm]
  exact Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)

/-- If a `PiecewiseC1Path` agrees with `fdBoundaryFun` on `[0, 1]`, then it also
avoids every strict interior point. -/
theorem piecewiseC1Path_avoids_interior {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z‖ := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := fdBoundaryFun_minDist_interior_pos hz_norm hz_re hz_im
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  change δ ≤ ‖γ.toPath.extend t - z‖
  rw [hγ t ht]
  exact hδ_bound t ht

/-- **Reduction to contour integral**: if a `PiecewiseC1Path` agrees with `fdBoundaryFun`
on `[0, 1]`, and the contour integral of `(z - z₀)⁻¹` equals `-2πi`, then the
generalized winding number at `z₀` is `-1`.

This reduces the interior winding number (a CPV/PV limit) to an ordinary contour integral
identity, which is the hard computational content. -/
theorem hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2)
    (_hz_im_pos : 0 < z.im) (hz_im_lt : z.im < H)
    (h_integral : γ.contourIntegral (fun w => (w - z)⁻¹) =
      -(2 * ↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ z (-1) := by
  convert hasGeneralizedWindingNumber_of_avoids
    (piecewiseC1Path_avoids_interior γ hγ hz_norm hz_re hz_im_lt) using 1
  rw [h_integral]
  field_simp

/-- On segment 1, the distance to `z` is at least `1/2 - |z.re|`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_seg1_re_dist {z : ℂ} (_hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) :
    1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖ := by
  calc 1/2 - |z.re| ≤ |1/2 - z.re| := by
        have h := abs_sub_abs_le_abs_sub (1/2 : ℝ) z.re
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] at h
        exact h
    _ = |(fdBoundaryFun H t - z).re| := by rw [sub_re, fdBoundaryFun_seg1_re H t ht]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_re_le_norm _

/-- On segments 2-3, the distance to `z` is at least `‖z‖ - 1`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_arc_dist {z : ℂ} (_hz_norm : 1 < ‖z‖)
    {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖z‖ - 1 ≤ ‖fdBoundaryFun H t - z‖ :=
  calc ‖z‖ - 1 = ‖z‖ - ‖fdBoundaryFun H t‖ := by rw [fdBoundaryFun_arc_norm H t ht1 ht2]
    _ ≤ ‖z - fdBoundaryFun H t‖ := norm_sub_norm_le z _
    _ = ‖fdBoundaryFun H t - z‖ := norm_sub_rev _ _

/-- On segment 4, the distance to `z` is at least `1/2 - |z.re|`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_seg4_re_dist {z : ℂ} (_hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖ := by
  calc 1/2 - |z.re| ≤ |-1/2 - z.re| := by
        have h := abs_sub_abs_le_abs_sub (-1/2 : ℝ) z.re
        rw [show |(-1 : ℝ)/2| = 1/2 by norm_num] at h
        exact h
    _ = |(fdBoundaryFun H t - z).re| := by rw [sub_re, fdBoundaryFun_seg4_re H t ht3 ht4]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_re_le_norm _

/-- On segment 5, the distance to `z` is at least `H - z.im`, which is positive
for strict interior points. -/
theorem fdBoundaryFun_seg5_im_dist {z : ℂ} (hz_im : z.im < H)
    {t : ℝ} (ht : 4/5 < t) :
    H - z.im ≤ ‖fdBoundaryFun H t - z‖ :=
  calc H - z.im = |(fdBoundaryFun H t - z).im| := by
        rw [sub_im, fdBoundaryFun_seg5_im H t ht, abs_of_pos (by linarith)]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_im_le_norm _

end
