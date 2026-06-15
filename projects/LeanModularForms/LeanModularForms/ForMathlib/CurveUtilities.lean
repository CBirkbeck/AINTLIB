/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.Analysis.Complex.Basic

/-!
# Curve Utilities and Avoidance

Utility lemmas for working with `PiecewiseC1Path` partition structure and curve avoidance.

## Main definitions

* `PiecewiseC1Path.infDist` — infimum distance from `z₀` to the path image on `[0, 1]`.
-/

open Set Complex Metric

noncomputable section

variable {x y : ℂ}

namespace PiecewiseC1Path

/-- Infimum distance from `z₀` to the path image on `[0, 1]`. -/
noncomputable def infDist (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℝ :=
  Metric.infDist z₀ (γ.toPath.extend '' Icc 0 1)

end PiecewiseC1Path

end
