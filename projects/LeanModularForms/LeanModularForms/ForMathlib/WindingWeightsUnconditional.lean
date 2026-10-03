/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import LeanModularForms.ForMathlib.ArcFTCLimit
public import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# Unconditional Winding Weights Assembly

Computes the generalized winding number at `i` on the fundamental-domain boundary from
a `SingleCrossingData` with FTC limit `-(πi)`.

## Main results

* `hasWindingNumber_atI_of_scd` — winding number at `i` is `-1/2`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Winding number at `i` is `-1/2` from `SingleCrossingData` with limit `-(πi)`. -/
theorem hasWindingNumber_atI_of_scd
    {γ : PiecewiseC1Path x y} (D : SingleCrossingData γ I)
    (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ I (-1/2) := by
  convert D.hasWindingNumber using 1
  rw [hL]
  field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]

end
