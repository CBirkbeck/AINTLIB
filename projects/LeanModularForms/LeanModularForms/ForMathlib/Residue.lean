/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Residue Theory

Definitions and basic results for residues of meromorphic functions.

## Main definitions

* `HasSimplePoleAt f z₀` — simple pole decomposition: `f(z) = c/(z-z₀) + g(z)` near `z₀`
  with `g` analytic.
* `HasSimplePoleAt.coeff` — the coefficient `c` in the pole decomposition.
* `residue f z₀` — the residue of `f` at `z₀`, defined via circle integral limit.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Interval Real

noncomputable section

/-- Simple pole decomposition: `f(z) = c/(z-z₀) + g(z)` near `z₀`, where `g` is analytic
at `z₀` and `c` is the residue. -/
def HasSimplePoleAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ c : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z

/-- The residue of `f` at `z₀`, defined as the limit of normalized circle integrals:
`Res(f, z₀) = lim_{r→0⁺} (2πi)⁻¹ ∮_{|z-z₀|=r} f(z) dz`. -/
def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, r), f z

end
