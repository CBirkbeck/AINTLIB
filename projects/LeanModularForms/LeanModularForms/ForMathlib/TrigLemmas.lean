/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Shared Trigonometric Identities

Exact values of `cos` and `sin` at `2π/3`.
-/

open Complex

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.sin_pi_sub]
  exact Real.sin_pi_div_three
