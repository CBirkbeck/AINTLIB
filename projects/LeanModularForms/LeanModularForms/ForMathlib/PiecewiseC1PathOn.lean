/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn

/-!
# Piecewise C¹ Paths on Arbitrary Intervals

This file defines `PiecewiseC1PathOn a b hab x y`, the free-interval form of a
piecewise C¹ path. The unit-interval form `PiecewiseC1Path` (defined in
`PiecewiseC1Path.lean`) is built on top of this by extending and bundling a
mathlib `Path x y`.

## Main definitions

* `PiecewiseC1PathOn a b hab x y` — a continuous function `ℝ → E` with `f a = x`,
  `f b = y`, continuous on `[a, b]`, that is `C¹` away from a finite set of breakpoints
  in `(a, b)`. The partition lives in the open interval `Ioo a b`.

## Design notes

This file deliberately does not depend on `Mathlib.Topology.Path`. The unit-interval
form `PiecewiseC1Path` extends this structure and adds a bundled `Path x y` together
with an equality witness `toPath.extend t = toFun t` on `Icc 0 1`.

We do not require the underlying carrier to be a mathlib `Path` because `Path` is
fixed to `[0, 1]` via `unitInterval`. A free-interval generalization needs a raw
`ℝ → E` with continuity on `Icc a b`.

## References

* `PROJECT_OVERVIEW.md` §3.6 (four parallel curve types).
* `P4_PLAN.md` (multi-day plan).
-/

open Set Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A piecewise continuously differentiable path from `x` to `y` on a free interval
`[a, b]` in a normed space.

The smoothness conditions (differentiability and continuous derivative) hold at every
point of `(a, b)` outside a finite set of breakpoints. The partition lives in the open
interval `Ioo a b` — the endpoints `a` and `b` are not partition points. -/
@[ext]
structure PiecewiseC1PathOn (a b : ℝ) (hab : a < b) (x y : E) where
  /-- The underlying function `ℝ → E`. -/
  toFun : ℝ → E
  /-- The path starts at `x` (at parameter `a`). -/
  source : toFun a = x
  /-- The path ends at `y` (at parameter `b`). -/
  target : toFun b = y
  /-- The path is continuous on the closed interval `[a, b]`. -/
  continuous_toFun : ContinuousOn toFun (Icc a b)
  /-- Finite set of breakpoints in the open interval `(a, b)`. -/
  partition : Finset ℝ
  /-- All breakpoints lie in the open interval `(a, b)`. -/
  partition_subset : (partition : Set ℝ) ⊆ Ioo a b
  /-- `toFun` is differentiable at every point of `(a, b)` outside the partition. -/
  differentiable_off : ∀ t ∈ Ioo a b, t ∉ partition → DifferentiableAt ℝ toFun t
  /-- The derivative of `toFun` is continuous at every point of `(a, b)` outside the
  partition. -/
  deriv_continuous_off : ∀ t ∈ Ioo a b, t ∉ partition → ContinuousAt (deriv toFun) t

namespace PiecewiseC1PathOn

variable {a b : ℝ} {hab : a < b} {x y : E}

instance : CoeFun (PiecewiseC1PathOn a b hab x y) fun _ => ℝ → E where
  coe := PiecewiseC1PathOn.toFun

end PiecewiseC1PathOn

end
