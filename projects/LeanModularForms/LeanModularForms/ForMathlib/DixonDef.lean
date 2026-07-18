/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.DSlope
import LeanModularForms.ForMathlib.SimplePoleIntegral

/-!
# Dixon Function Definitions and the h1/h2 Identity

This file defines the Dixon h1 and h2 functions and proves the fundamental identity
relating them. These are the core building blocks for Dixon's proof of the homological
Cauchy integral formula.

## Main definitions

* `dixonH1` -- the Dixon integral `∮_γ dslope(f, w, γ(t)) · γ'(t) dt`.
  Well-defined for all `w`, including points on the curve.
* `dixonH2` -- the Cauchy-type integral `∮_γ f(γ(t))/(γ(t) - w) · γ'(t) dt`.
  Well-defined for `w` off the curve.
* `dixonFunction` -- piecewise: `h1` on `U`, `h2` off `U`.

## Main results

* `dixonH1_eq_dixonH2_sub_winding_f` -- the key identity:
  `h1(w) = h2(w) - 2πi · n(γ, w) · f(w)` for `w` off the curve.

## Design notes

The definitions use `PiecewiseC1Path x x` (closed paths) from the ForMathlib infrastructure,
with `dslope` from mathlib. The h1/h2 identity follows from expanding `dslope` into
`(f(z) - f(w))/(z - w) = f(z)/(z - w) - f(w)/(z - w)` and splitting the integral.

The `dslope f w (γ t)` has center `w` (second argument) and evaluation point `γ t`
(third argument): `dslope f a b = (f b - f a) / (b - a)` when `b ≠ a`, and
`dslope f a a = deriv f a`.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, 1971
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-- The Dixon h1 function: `∮_γ dslope(f, w, γ(t)) · γ'(t) dt`.

This is well-defined for all `w` including points on the curve, because
`dslope f w z` is continuous in `z` even at `z = w` (where it equals `deriv f w`). -/
def dixonH1 (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, dslope f w (γ t) * deriv γ.toPath.extend t

/-- The Dixon h2 function: `∮_γ f(γ(t))/(γ(t) - w) · γ'(t) dt`.

This is the standard Cauchy-type integral, well-defined for `w` off the curve. -/
def dixonH2 (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (γ t) / (γ t - w) * deriv γ.toPath.extend t

/-- The Dixon function: `h1` on `U`, `h2` off `U`.

This piecewise construction is the key to Dixon's proof: both pieces are analytic
(h1 on U, h2 on the complement of the curve image), and they agree on the overlap
by the h1/h2 identity, yielding an entire function. -/
def dixonFunction (f : ℂ → ℂ) (U : Set ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ) : ℂ :=
  if w ∈ U then dixonH1 f γ w else dixonH2 f γ w

private lemma dslope_integrand_eq {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {w : ℂ}
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      dslope f w (γ t) * deriv γ.toPath.extend t =
        f (γ t) / (γ t - w) * deriv γ.toPath.extend t -
          f w / (γ t - w) * deriv γ.toPath.extend t := by
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [dslope_of_ne _ (hoff t ht), slope_def_field]
  ring

private lemma winding_integrand_eq_const_mul (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ) :
    (fun t ↦ f w / (γ t - w) * deriv γ.toPath.extend t) =
      (fun t ↦ f w * ((γ t - w)⁻¹ * deriv γ.toPath.extend t)) := by
  funext t
  field_simp

private lemma contourIntegral_fw_div_eq (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ) :
    ∫ t in (0 : ℝ)..1, f w / (γ t - w) * deriv γ.toPath.extend t =
      f w * γ.contourIntegral (fun z ↦ (z - w)⁻¹) := by
  simp only [PiecewiseC1Path.contourIntegral, winding_integrand_eq_const_mul]
  exact intervalIntegral.integral_const_mul _ _

private lemma winding_integrand_intervalIntegrable (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x) (w : ℂ)
    (h_base : IntervalIntegrable
      (fun t ↦ (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    IntervalIntegrable
      (fun t ↦ f w / (γ t - w) * deriv γ.toPath.extend t) volume 0 1 :=
  winding_integrand_eq_const_mul f γ w ▸ h_base.const_mul _

private theorem avoids_delta_bound (γ : PiecewiseC1Path x x) (w : ℂ)
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - w‖ := by
  have h_compact : IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image γ.toPath.continuous_extend
  have h_pos : 0 < Metric.infDist w (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    (h_compact.isClosed.notMem_iff_infDist_pos
      ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩).mp
      (fun ⟨t, ht, heq⟩ ↦ hoff t ht heq)
  refine ⟨_, h_pos, fun t ht ↦ ?_⟩
  calc Metric.infDist w _ ≤ dist w (γ.toPath.extend t) :=
        Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
    _ = ‖γ.toPath.extend t - w‖ := by rw [Complex.dist_eq, norm_sub_rev]

/-- **The fundamental h1/h2 identity.**

For a closed piecewise C^1 path `γ` and a point `w` off the curve:

  `h1(w) = h2(w) - 2πi · n(γ, w) · f(w)`

where `n(γ, w)` is the generalized winding number.

The proof expands `dslope f w (γ t) = (f(γ t) - f(w)) / (γ t - w)` (since `γ t ≠ w`),
splits into `f(γ t)/(γ t - w) - f(w)/(γ t - w)`, and identifies the second term as
`f(w) · ∮ (z - w)⁻¹ dz = 2πi · n(γ, w) · f(w)`. -/
theorem dixonH1_eq_dixonH2_sub_winding_f {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} (w : ℂ)
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w)
    (h_cauchy_int : IntervalIntegrable
      (fun t ↦ f (γ t) / (γ t - w) * deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t ↦ (γ t - w)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    dixonH1 f γ w =
      dixonH2 f γ w - 2 * ↑Real.pi * I * generalizedWindingNumber γ w * f w := by
  simp only [dixonH1, dixonH2]
  rw [intervalIntegral.integral_congr (dslope_integrand_eq hoff),
    intervalIntegral.integral_sub h_cauchy_int
      (winding_integrand_intervalIntegrable f γ w h_base_int)]
  congr 1
  rw [contourIntegral_fw_div_eq f γ w,
    integral_inv_sub_eq_winding (avoids_delta_bound γ w hoff)]
  ring

/-- On `U`, the Dixon function equals `h1`. -/
theorem dixonFunction_eq_dixonH1 {f : ℂ → ℂ} {U : Set ℂ}
    {γ : PiecewiseC1Path x x} {w : ℂ} (hw : w ∈ U) :
    dixonFunction f U γ w = dixonH1 f γ w :=
  if_pos hw

end
