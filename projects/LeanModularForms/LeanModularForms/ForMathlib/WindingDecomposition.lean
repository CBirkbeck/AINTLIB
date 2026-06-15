/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CrossingAnalysis
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# Winding Number Decomposition — Proposition 2.3

Geometric crossing angle for the Hungerbühler–Wasem decomposition of the generalized
winding number.

## Main definitions

* `angleAtCrossing` — the signed angle at a crossing point where `γ` passes through
  `z₀`: `π` at a smooth point, `arg(L_right) - arg(-L_left)` at a partition (corner) point.

## Main results

* `angleAtCrossing_smooth` — at a smooth crossing point, the angle is `π`.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set
open scoped Real

noncomputable section

variable {x y : ℂ}

/-- The signed angle at a crossing point where a piecewise C¹ immersion passes through `z₀`.

At a smooth point (not in the partition), the tangent direction is continuous across the
crossing, and the angle between outgoing and negated incoming directions is `π`.

At a corner point (in the partition), the angle is `arg(L_right) - arg(-L_left)` where
`L_left` and `L_right` are the one-sided derivative limits. -/
def angleAtCrossing (γ : PwC1Immersion x y) (t₀ : ℝ) (_ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : ℝ :=
  if h : t₀ ∈ γ.toPiecewiseC1Path.partition then
    let L_left := Classical.choose (γ.left_deriv_limit t₀ h)
    let L_right := Classical.choose (γ.right_deriv_limit t₀ h)
    arg L_right - arg (-L_left)
  else Real.pi

/-- At a smooth point (not in the partition), the crossing angle is `π`. -/
theorem angleAtCrossing_smooth (γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) :
    angleAtCrossing γ t₀ ht₀ = Real.pi := by
  simp [angleAtCrossing, hsmooth]

end
