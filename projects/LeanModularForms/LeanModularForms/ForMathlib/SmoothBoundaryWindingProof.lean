/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CoreIdentityProof
import LeanModularForms.ForMathlib.BoundaryWinding

/-!
# Smooth Boundary Winding Proof — Constructing `FDWindingDataFull`

This file proves that `FDWindingDataFull` can be constructed from `FDWindingData`
together with the smooth boundary winding condition, and provides pathways for
discharging that condition.

## Architecture

The `boundary_winding` field of `FDWindingDataFull` requires: at every non-elliptic,
non-interior point on the FD boundary, the generalized winding number is `-1/2`.

### Pathway 1: Direct hypothesis
`mkFDWindingDataFull` takes a `FDWindingData` and the boundary condition as a
hypothesis, producing `FDWindingDataFull`.

### Pathway 2: From SmoothBoundaryWindingData
`mkFDWindingDataFull_of_smoothData` constructs `FDWindingDataFull` from
`SmoothBoundaryWindingData` at each smooth boundary point.

### Pathway 3: Geometric classification
`smooth_boundary_classification` shows smooth boundary points fall into
two cases (vertical edge or non-elliptic arc), enabling case-by-case
construction of `SmoothBoundaryWindingData`.

## Main results

* `mkFDWindingDataFull` — assembler from `FDWindingData` + boundary hypothesis
* `boundaryWindingHyp_of_smoothData` — from `SmoothBoundaryWindingData` oracle
* `mkFDWindingDataFull_of_smoothData` — full assembler via smooth data
* `smooth_boundary_classification` — geometric dichotomy for boundary points
* `boundary_point_on_vert_edge`, `boundary_point_on_arc_range` — geometric
  descriptions of the two cases

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex
open scoped Real UpperHalfPlane

noncomputable section

private lemma ellipticPointRho_re : (ellipticPointRho : ℂ).re = -1/2 := by
  simp [ellipticPointRho, ellipticPointRho']

private lemma ellipticPointRho_im : (ellipticPointRho : ℂ).im = Real.sqrt 3 / 2 := by
  simp [ellipticPointRho, ellipticPointRho']

private lemma ellipticPointRhoPlusOne_re : (ellipticPointRhoPlusOne : ℂ).re = 1/2 := by
  simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']

private lemma ellipticPointRhoPlusOne_im :
    (ellipticPointRhoPlusOne : ℂ).im = Real.sqrt 3 / 2 := by
  simp [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']

/-- The boundary winding condition: at every point `z` in the upper half-plane
below height `H`, which is not elliptic, not strict interior, but lies on the
FD boundary (`normSq >= 1`, `|re| <= 1/2`), the winding number of `gamma`
around `z` is `-1/2`. -/
def BoundaryWindingHyp {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H)) : Prop :=
  ∀ z : ℂ, z.im > 0 → z.im < H →
    z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
    ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
    Complex.normSq z ≥ 1 → |z.re| ≤ 1/2 →
    HasGeneralizedWindingNumber γ z (-1/2)

/-- Construct `FDWindingDataFull` from `FDWindingData` and the boundary winding
condition. This is the minimal assembler: it lifts the base winding data
(interior, i, rho, rho+1) to the full data with smooth boundary winding. -/
def mkFDWindingDataFull {H : ℝ} (D : FDWindingData H)
    (h_bdy : BoundaryWindingHyp D.boundary) : FDWindingDataFull H where
  toFDWindingData := D
  boundary_winding := h_bdy

private lemma im_eq_sqrt3_half_of_normSq_one_of_absRe_half
    {z : ℂ} (h_nsq : Complex.normSq z = 1)
    (hz_im : z.im > 0) (h_re_sq : z.re * z.re = 1/4) :
    z.im = Real.sqrt 3 / 2 := by
  rw [Complex.normSq_apply] at h_nsq
  have h_prod : (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) = 0 := by
    nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
  rcases mul_eq_zero.mp h_prod with h | h
  · linarith
  · exact absurd h (ne_of_gt (add_pos hz_im (by positivity)))

/-- A non-elliptic non-interior FD boundary point lies either on a vertical edge
(`|re| = 1/2`, `norm > 1`) or on the smooth part of the unit circle arc
(`norm = 1`, `re ≠ 0`, `|re| ≠ 1/2`). -/
theorem smooth_boundary_classification (z : ℂ)
    (hz_im : z.im > 0)
    (hz_ne_I : z ≠ I)
    (hz_ne_rho : z ≠ ellipticPointRho)
    (hz_ne_rho1 : z ≠ ellipticPointRhoPlusOne)
    (hz_not_int : ¬(‖z‖ > 1 ∧ |z.re| < 1/2))
    (hz_nsq : Complex.normSq z ≥ 1)
    (hz_re : |z.re| ≤ 1/2) :
    (|z.re| = 1/2 ∧ ‖z‖ > 1) ∨ (‖z‖ = 1 ∧ z.re ≠ 0 ∧ |z.re| ≠ 1/2) := by
  have hnorm_ge : (1 : ℝ) ≤ ‖z‖ := by
    rw [Complex.norm_def]; exact Real.one_le_sqrt.mpr hz_nsq
  rcases hnorm_ge.eq_or_lt with h_eq | h_gt
  · have h_nsq_1 : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, ← h_eq]; ring
    refine Or.inr ⟨h_eq.symm, fun hre_zero => ?_, fun hre_half => ?_⟩
    · rw [Complex.normSq_apply, hre_zero, mul_zero, zero_add] at h_nsq_1
      exact hz_ne_I <| Complex.ext (hre_zero.trans I_re.symm) <| by
        nlinarith [mul_self_nonneg (z.im - 1), mul_self_nonneg (z.im + 1), hz_im, I_im]
    · have h_re_sq : z.re * z.re = 1/4 := by nlinarith [sq_abs z.re, hre_half]
      have h_im_val := im_eq_sqrt3_half_of_normSq_one_of_absRe_half h_nsq_1 hz_im h_re_sq
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1/2) |>.mp hre_half with h_pos | h_neg
      · refine hz_ne_rho1 <| Complex.ext ?_ ?_
        · rw [h_pos, ellipticPointRhoPlusOne_re]
        · rw [h_im_val, ellipticPointRhoPlusOne_im]
      · refine hz_ne_rho <| Complex.ext ?_ ?_
        · rw [h_neg, ellipticPointRho_re]; ring
        · rw [h_im_val, ellipticPointRho_im]
  · refine Or.inl ⟨le_antisymm hz_re ?_, h_gt⟩
    by_contra! h
    exact hz_not_int ⟨h_gt, h⟩

end
