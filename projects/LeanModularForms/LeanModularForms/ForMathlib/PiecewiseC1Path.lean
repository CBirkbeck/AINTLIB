/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1PathOn
import Mathlib.Topology.Path

/-!
# Piecewise C¹ Paths

This file defines piecewise C¹ paths in normed spaces, wrapping mathlib's `Path x y`
(parametrized on `[0,1]`) with piecewise C¹ smoothness conditions.

## Main definitions

* `PiecewiseC1Path x y` — a free-interval `PiecewiseC1PathOn 0 1 zero_lt_one x y`
  bundled with a mathlib `Path x y` whose `extend` agrees pointwise with `toFun` on
  `[0, 1]`. Differentiability and derivative continuity are inherited from the
  parent structure.

* `PwC1Immersion x y` — a `PiecewiseC1Path x y` whose derivative is nonzero away
  from partition points, with nonzero one-sided derivative limits at partition points.

## Design notes

`PiecewiseC1Path` extends `PiecewiseC1PathOn 0 1 zero_lt_one x y` (the free-interval
form). The bundled `Path x y` is kept as an explicit field because the `Path` API is
heavily used by call sites — in particular, the coercion `γ t = γ.toPath.extend t`
must remain stable. The witness `toPath_extend_eq_toFun` ties the two forms together
on `Icc 0 1`.

The definitions are stated for a `NormedAddCommGroup E` with `NormedSpace ℝ E`, which
covers `ℂ` as the main application.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : E}

/-- A piecewise continuously differentiable path from `x` to `y` in a normed space.

This bundles a free-interval `PiecewiseC1PathOn 0 1 zero_lt_one x y` together with a
mathlib `Path x y` whose `extend` agrees with the underlying function on `[0, 1]`.
Differentiability and continuous-derivative conditions are inherited from the parent. -/
@[ext]
structure PiecewiseC1Path (x y : E) extends PiecewiseC1PathOn 0 1 zero_lt_one x y where
  /-- The bundled mathlib `Path x y`. Kept as a field so that `Path.extend`-based
  call sites can continue to use the `Path` API. -/
  toPath : Path x y
  /-- The extended path agrees with the underlying function on the closed unit interval. -/
  toPath_extend_eq_toFun : ∀ t ∈ Icc (0:ℝ) 1, toPath.extend t = toFun t

namespace PiecewiseC1Path

/-- The underlying function `ℝ → E` obtained by extending the path. -/
def extendedPath (γ : PiecewiseC1Path x y) : ℝ → E := γ.toPath.extend

instance : CoeFun (PiecewiseC1Path x y) fun _ => ℝ → E where
  coe := extendedPath

/-- The extended path is differentiable at every point of `(0, 1)` outside the partition.
Same statement as the inherited `differentiable_off` but phrased in terms of `toPath.extend`
instead of `toFun`. The two forms agree on `Icc 0 1` via `toPath_extend_eq_toFun`. -/
theorem differentiable_off_extend (γ : PiecewiseC1Path x y) :
    ∀ t ∈ Ioo (0:ℝ) 1, t ∉ γ.partition → DifferentiableAt ℝ γ.toPath.extend t :=
  fun t ht htp => (γ.differentiable_off t ht htp).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
      fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu))

/-- The derivative of the extended path is continuous at every point of `(0, 1)` outside
the partition. Same statement as `deriv_continuous_off` but in terms of `toPath.extend`. -/
theorem deriv_continuous_off_extend (γ : PiecewiseC1Path x y) :
    ∀ t ∈ Ioo (0:ℝ) 1, t ∉ γ.partition → ContinuousAt (deriv γ.toPath.extend) t :=
  fun t ht htp => (γ.deriv_continuous_off t ht htp).congr
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
      fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu)).deriv.symm

@[simp]
theorem apply_zero (γ : PiecewiseC1Path x y) : γ 0 = x :=
  γ.toPath.extend_zero

@[simp]
theorem apply_one (γ : PiecewiseC1Path x y) : γ 1 = y :=
  γ.toPath.extend_one

/-- The underlying extended path is continuous. -/
@[fun_prop]
theorem continuous (γ : PiecewiseC1Path x y) : Continuous (γ : ℝ → E) :=
  γ.toPath.continuous_extend

end PiecewiseC1Path

/-- A piecewise C¹ immersion from `x` to `y` in a normed space.

This extends `PiecewiseC1Path x y` with the condition that the derivative is nonzero away from
partition points, and has nonzero one-sided limits at partition points. This ensures the path
has a well-defined tangent direction everywhere. -/
@[ext]
structure PwC1Immersion (x y : E) extends PiecewiseC1Path x y where
  /-- The derivative is nonzero at every point of `(0, 1)` outside the partition. -/
  deriv_ne_zero : ∀ t ∈ Ioo 0 1, t ∉ partition →
    deriv toPiecewiseC1Path.toPath.extend t ≠ 0
  /-- At each partition point, the left derivative limit exists and is nonzero. -/
  left_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧
    Tendsto (deriv toPiecewiseC1Path.toPath.extend) (𝓝[<] p) (𝓝 L)
  /-- At each partition point, the right derivative limit exists and is nonzero. -/
  right_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧
    Tendsto (deriv toPiecewiseC1Path.toPath.extend) (𝓝[>] p) (𝓝 L)

namespace PwC1Immersion

instance : CoeFun (PwC1Immersion x y) fun _ => ℝ → E where
  coe γ := γ.toPiecewiseC1Path.extendedPath

/-- The underlying extended path is continuous. -/
@[fun_prop]
theorem continuous (γ : PwC1Immersion x y) : Continuous (γ : ℝ → E) :=
  γ.toPiecewiseC1Path.continuous

end PwC1Immersion

end
