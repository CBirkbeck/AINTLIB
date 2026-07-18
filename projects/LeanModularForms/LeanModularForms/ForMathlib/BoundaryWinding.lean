/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ForMathlib.CrossingAtI

/-!
# Smooth Boundary Winding Number

At a smooth boundary crossing of the fundamental domain -- any point on the
FD boundary that is NOT an elliptic point (i, rho, rho+1) and not at a
partition endpoint -- the generalized winding number is `-1/2`.

At any such point the FD boundary passes through `z₀` as a smooth curve
(locally a line segment or arc), making an angle of `π` from entry to exit.
The Hungerbuhler--Wasem decomposition gives winding = `angle / (2π) = -1/2`.

## Main results

* `hasGeneralizedWindingNumber_neg_half_of_scd` -- if `SingleCrossingData`
  has `L = -(π * I)`, then `HasGeneralizedWindingNumber γ z₀ (-1/2)`.
* `generalizedWindingNumber_neg_half_of_scd` -- the corresponding equality.
* `SmoothBoundaryWindingData` -- a structure bundling a crossing parameter,
  cutoff, geometric bounds, and an `ArcFTCHyp` with limit `-(π * I)`.
* `SmoothBoundaryWindingData.hasWindingNumber` -- extracts
  `HasGeneralizedWindingNumber γ z₀ (-1/2)` from the bundled data.

## Design

Rather than constructing `SingleCrossingData` for every possible smooth
boundary point, we take the `SingleCrossingData` as a hypothesis. The key
content is:

1. The general bridge from `SingleCrossingData` with `L = -(π * I)` to
   the winding number `-1/2`, for an arbitrary point `z₀`.
2. The `SmoothBoundaryWindingData` structure and its extraction theorem.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

variable {x y : ℂ}

/-! ### General smooth crossing winding number -/

/-- At any single crossing with limit `L = -(π * I)`, the generalized winding
number is `-1/2`. This is the universal smooth-crossing result: the angle
swept from entry to exit is `π`, giving `-(π * I) / (2 * π * I) = -1/2`. -/
theorem hasGeneralizedWindingNumber_neg_half_of_scd {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (D : SingleCrossingData γ z₀) (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ z₀ (-1 / 2) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Construct `SingleCrossingData` at an arbitrary smooth crossing parameter `t₀`.

**Geometry parameters** (proved per-segment elsewhere):
- `h_far`: outside the δ-window, the curve is ε-far from `z₀`
- `h_near`: inside the δ-window, the curve is ε-close to `z₀`

**Analytic parameter** (`ArcFTCHyp`): the FTC identity, integrability, and limit. -/
def mkSingleCrossingData_smooth {H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (δ : ℝ → ℝ) (threshold : ℝ)
    (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ.toPath.extend t - z₀‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε → ‖γ.toPath.extend t - z₀‖ ≤ ε)
    (L : ℂ) (ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold L) : SingleCrossingData γ z₀ where
  L := L
  t₀ := t₀
  ht₀ := ht₀
  δ := δ
  threshold := threshold
  hthresh := hthresh
  hδ_pos := hδ_pos
  hδ_small := hδ_small
  h_far := h_far
  h_near := h_near
  E := ftcHyp.E
  h_ftc := ftcHyp.h_ftc
  hint_left := ftcHyp.hint_left
  hint_right := ftcHyp.hint_right
  h_limit := ftcHyp.h_limit

/-- From a generic smooth crossing `SingleCrossingData` with limit `L = -(π * I)`,
extract `HasGeneralizedWindingNumber γ z₀ (-1/2)`. -/
theorem boundaryWinding_of_smoothFTCHyp {H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (δ : ℝ → ℝ) (threshold : ℝ)
    (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ.toPath.extend t - z₀‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε → ‖γ.toPath.extend t - z₀‖ ≤ ε)
    (ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold (-(↑Real.pi * I))) :
    HasGeneralizedWindingNumber γ z₀ (-1 / 2) :=
  hasGeneralizedWindingNumber_neg_half_of_scd
    (mkSingleCrossingData_smooth γ z₀ t₀ ht₀ δ threshold hthresh
      hδ_pos hδ_small h_far h_near _ ftcHyp) rfl

/-! ### SmoothBoundaryWindingData

Data witnessing that a smooth boundary point `z₀` has winding number `-1/2`.
This bundles a crossing parameter, cutoff, geometric bounds, and the analytical
`ArcFTCHyp` hypothesis. -/

/-- Data witnessing that a smooth boundary point `z₀` has winding number `-1/2`.

Bundles a crossing parameter, cutoff, geometric bounds, and an `ArcFTCHyp`
with limit `-(π * I)`. -/
structure SmoothBoundaryWindingData {H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (z₀ : ℂ) where
  /-- Crossing parameter in `(0, 1)`. -/
  t₀ : ℝ
  ht₀ : t₀ ∈ Ioo 0 1
  /-- Cutoff function. -/
  δ : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  /-- `δ(ε)` is positive. -/
  hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε
  /-- `δ(ε)` stays within `(0, 1)` around `t₀`. -/
  hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀)
  /-- Far bound. -/
  h_far : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ.toPath.extend t - z₀‖
  /-- Near bound. -/
  h_near : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, |t - t₀| ≤ δ ε → ‖γ.toPath.extend t - z₀‖ ≤ ε
  /-- Analytical hypothesis with limit `-(π * I)`. -/
  ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold (-(↑Real.pi * I))

/-- From `SmoothBoundaryWindingData`, extract `HasGeneralizedWindingNumber γ z₀ (-1/2)`. -/
theorem SmoothBoundaryWindingData.hasWindingNumber {H : ℝ}
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)} {z₀ : ℂ}
    (D : SmoothBoundaryWindingData γ z₀) : HasGeneralizedWindingNumber γ z₀ (-1 / 2) :=
  boundaryWinding_of_smoothFTCHyp γ z₀ D.t₀ D.ht₀ D.δ D.threshold D.hthresh
    D.hδ_pos D.hδ_small D.h_far D.h_near D.ftcHyp

/-! ### Linear cutoff utilities -/

/-- Linear cutoff for vertical and horizontal segments.
Given a smooth curve `γ(t) = a + b*t*I` (or similar linear parameterization),
the distance from `z₀ = γ(t₀)` satisfies `‖γ(t) - z₀‖ = C·|t - t₀|` for some
positive constant `C`. The cutoff `linDelta C ε = ε / C` inverts this. -/
def linDelta (C : ℝ) (ε : ℝ) : ℝ := ε / C

theorem linDelta_pos {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) : 0 < linDelta C ε :=
  div_pos hε hC

end
