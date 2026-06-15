/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.MultipointPV
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# PV Integrals of Simple Pole Terms

Reduces the Cauchy principal value integral of `(z - s)⁻¹` along a piecewise C¹ path that
avoids the pole `s` to the ordinary contour integral, expressed in terms of the
generalized winding number.

## Main results

* `integral_inv_sub_eq_winding` — when `γ` avoids `s`, the ordinary contour integral of
  `(z - s)⁻¹` equals `2πi · generalizedWindingNumber γ s`.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-- When `γ` avoids `s` with positive minimum distance, the ordinary contour integral
of `(z - s)⁻¹` equals `2πi · generalizedWindingNumber γ s`. -/
theorem integral_inv_sub_eq_winding {s : ℂ} {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) :
    γ.contourIntegral (fun z => (z - s)⁻¹) =
      2 * ↑Real.pi * I * generalizedWindingNumber γ s := by
  have hw := hasGeneralizedWindingNumber_of_avoids hδ
  rw [HasCauchyPV.unique (hasCauchyPV_of_avoids hδ) hw, hw.eq]

end
