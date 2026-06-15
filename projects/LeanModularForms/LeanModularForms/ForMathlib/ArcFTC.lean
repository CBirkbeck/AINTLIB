/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# Arc FTC — Crossing Angles and Winding Numbers for FD Boundary

Geometric lemmas for crossings of the fundamental domain boundary at the three
on-curve points `i`, `ρ`, `ρ+1`, used in the `ArcFTCHyp` construction.

## Main results

* `arg_ofReal_mul_I` — `arg(r·I) = π/2` for `r > 0`.
* `fdBoundary_arc_deriv_eq` — derivative of the arc parametrization of the FD boundary.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set

noncomputable section

/-- The argument of `r * I` is `π/2` for `r > 0`. -/
theorem arg_ofReal_mul_I (r : ℝ) (hr : 0 < r) :
    arg (↑r * I) = Real.pi / 2 := by
  rw [Complex.arg_real_mul _ hr, Complex.arg_I]

/-- The derivative of the arc parametrization.
`d/dt exp(i·θ(t)) = (5π/6) · i · exp(i·θ(t))`. -/
theorem fdBoundary_arc_deriv_eq (t : ℝ) :
    deriv (fun s => exp (↑(fdArcAngle s) * I)) t =
      ↑(5 * Real.pi / 6) * I * exp (↑(fdArcAngle t) * I) := by
  simp only [fdArcAngle]
  have hd : HasDerivAt (fun s : ℝ =>
      Real.pi / 3 + (5 * s - 1) * (Real.pi / 6)) (5 * Real.pi / 6) t := by
    convert (((hasDerivAt_id t).const_mul 5).sub_const 1).mul_const (Real.pi / 6)
      |>.const_add (Real.pi / 3) using 1
    all_goals first | rfl | ring
  rw [(hd.ofReal_comp.mul_const I).cexp.deriv]; push_cast; ring

end
