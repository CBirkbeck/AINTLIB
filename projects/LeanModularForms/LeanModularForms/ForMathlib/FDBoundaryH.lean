/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.EllipticPoints

/-!
# Fundamental Domain Boundary – Basic Definitions

Definitions and continuity for the boundary of the standard fundamental domain
for SL₂(ℤ), both at fixed height `heightCutoff` and at variable height `H`.

## Main Definitions

* `heightCutoff` — fixed cutoff height (√3/2 + 1)
* `fdBoundary` — 5-segment boundary at fixed height
* `fdBoundary_H` — 5-segment boundary at variable height H
* `fdPartition` — interior partition points
* `fdBoundaryFullPartition` — full partition including endpoints
* `fdBoundary_H_partition` — partition for H-parameterized boundary
* `seg5_q_radius_H` — q-expansion radius e^(-2πH)
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Height cutoff for the finite-height fundamental domain boundary. -/
def heightCutoff : ℝ := Real.sqrt 3 / 2 + 1

/-- Segment 2: arc from ρ+1 to i (angle π/3 → π/2). -/
def fdBoundary_seg2 : ℝ → ℂ := fun t ↦
  Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)

/-- Segment 3: arc from i to ρ (angle π/2 → 2π/3). -/
def fdBoundary_seg3 : ℝ → ℂ := fun t ↦
  Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)

/-- Boundary of the standard fundamental domain at fixed
height `heightCutoff`, parameterized over [0, 5]. -/
def fdBoundary : ℝ → ℂ := fun t ↦
  if t ≤ 1 then
    1 / 2 +
      (heightCutoff - t * (heightCutoff - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp
      ((Real.pi / 3 +
        (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp
      ((Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1 / 2 +
      (Real.sqrt 3 / 2 +
        (t - 3) * (heightCutoff - Real.sqrt 3 / 2)) * I
  else
    (t - 9 / 2) + heightCutoff * I

/-- Full partition including endpoints. -/
def fdBoundaryFullPartition : Finset ℝ := {0, 1, 2, 3, 4, 5}

/-- The arc point of segment 3 at parameter `t = 3` is the elliptic point `ρ`. Shared by
`fdBoundary_at_three` and `fdBoundary_H_at_three`, since segment 3 is height-independent. -/
private lemma exp_seg3_at_three :
    Complex.exp ((↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I) =
      ellipticPointRho := by
  rw [show (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  ring

lemma fdBoundary_at_three :
    fdBoundary 3 = ellipticPointRho := by
  simp only [fdBoundary, show ¬(3 : ℝ) ≤ 1 by norm_num,
    show ¬(3 : ℝ) ≤ 2 by norm_num, le_refl (3 : ℝ),
    ite_true, ite_false]
  exact exp_seg3_at_three

/-- Segment 1 at height H: right vertical from (1/2 + H·i) down
to ρ+1. -/
def fdBoundary_seg1_H (H : ℝ) : ℝ → ℂ := fun t ↦
  1 / 2 + (H - t * (H - Real.sqrt 3 / 2)) * I

/-- Segment 2 at height H (H-independent): arc from ρ+1 to i. -/
def fdBoundary_seg2_H : ℝ → ℂ := fdBoundary_seg2

/-- Segment 3 at height H (H-independent): arc from i to ρ. -/
def fdBoundary_seg3_H : ℝ → ℂ := fdBoundary_seg3

/-- Segment 4 at height H: left vertical from ρ up to (-1/2 + H·i). -/
def fdBoundary_seg4_H (H : ℝ) : ℝ → ℂ := fun t ↦
  -1 / 2 + (Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I

/-- Segment 5 at height H: horizontal from (-1/2 + H·i) to (1/2 + H·i). -/
def fdBoundary_seg5_H (H : ℝ) : ℝ → ℂ := fun t ↦ (t - 9 / 2) + H * I

/-- Boundary of the standard fundamental domain at variable height H,
parameterized over [0, 5]. -/
def fdBoundary_H (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 1 then
    1 / 2 + (H - t * (H - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp
      ((Real.pi / 3 +
        (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp
      ((Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1 / 2 +
      (Real.sqrt 3 / 2 +
        (t - 3) * (H - Real.sqrt 3 / 2)) * I
  else
    (t - 9 / 2) + H * I

/-- Non-differentiable corner points of fdBoundary_H (excluding smooth
transitions at t = 2). -/
def fdBoundary_H_partition : Finset ℝ := {1, 3, 4}

/-- The q-expansion radius at height H: e^(-2πH). -/
def seg5_q_radius_H (H : ℝ) : ℝ := Real.exp (-2 * Real.pi * H)

lemma fdBoundary_H_at_zero (H : ℝ) :
    fdBoundary_H H 0 = 1 / 2 + H * I := by
  simp [fdBoundary_H]

lemma fdBoundary_H_at_one (H : ℝ) :
    fdBoundary_H H 1 = ellipticPointRhoPlusOne := by
  simp [fdBoundary_H, ellipticPointRhoPlusOne, ellipticPointRhoPlusOne']

lemma fdBoundary_H_at_three (H : ℝ) :
    fdBoundary_H H 3 = ellipticPointRho := by
  simp only [fdBoundary_H, show ¬(3 : ℝ) ≤ 1 by norm_num,
    show ¬(3 : ℝ) ≤ 2 by norm_num, le_refl (3 : ℝ),
    ite_true, ite_false]
  exact exp_seg3_at_three

lemma fdBoundary_H_at_four (H : ℝ) :
    fdBoundary_H H 4 = -1 / 2 + H * I := by
  simp only [fdBoundary_H, show ¬(4 : ℝ) ≤ 1 by norm_num,
    show ¬(4 : ℝ) ≤ 2 by norm_num, show ¬(4 : ℝ) ≤ 3 by norm_num,
    le_refl (4 : ℝ), ite_true, ite_false]
  push_cast
  ring

lemma fdBoundary_H_at_five (H : ℝ) :
    fdBoundary_H H 5 = 1 / 2 + H * I := by
  simp only [fdBoundary_H, show ¬(5 : ℝ) ≤ 1 by norm_num,
    show ¬(5 : ℝ) ≤ 2 by norm_num, show ¬(5 : ℝ) ≤ 3 by norm_num,
    show ¬(5 : ℝ) ≤ 4 by norm_num, ite_false]
  push_cast
  ring

lemma fdBoundary_H_closed (H : ℝ) :
    fdBoundary_H H 0 = fdBoundary_H H 5 := by
  rw [fdBoundary_H_at_zero, fdBoundary_H_at_five]

private lemma fdBoundary_H_seg1_cont (H : ℝ) :
    Continuous (fun t : ℝ ↦ (1 : ℂ) / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I) := by
  fun_prop

private lemma fdBoundary_H_seg23_cont :
    Continuous (fun t : ℝ ↦ exp
      ((↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)) := by
  fun_prop

private lemma fdBoundary_H_seg23b_cont :
    Continuous (fun t : ℝ ↦ exp
      ((↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)) := by
  fun_prop

private lemma fdBoundary_H_seg4_cont (H : ℝ) :
    Continuous (fun t : ℝ ↦
      (-1 : ℂ) / 2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I) := by
  fun_prop

private lemma fdBoundary_H_seg5_cont (H : ℝ) :
    Continuous (fun t : ℝ ↦ (↑t - 9 / 2 : ℂ) + ↑H * I) := by
  fun_prop

private def fdBoundary_H_inner34 (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 4 then
    -1 / 2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else (↑t - 9 / 2 : ℂ) + ↑H * I

private lemma fdBoundary_H_inner34_cont (H : ℝ) : Continuous (fdBoundary_H_inner34 H) :=
  Continuous.if_le (fdBoundary_H_seg4_cont H) (fdBoundary_H_seg5_cont H)
    continuous_id continuous_const (fun t (ht : t = 4) => by
      subst ht
      push_cast
      ring)

private def fdBoundary_H_inner234 (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 3 then
    exp ((↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
  else fdBoundary_H_inner34 H t

private lemma fdBoundary_H_inner234_cont (H : ℝ) : Continuous (fdBoundary_H_inner234 H) := by
  apply Continuous.if_le fdBoundary_H_seg23b_cont
    (fdBoundary_H_inner34_cont H) continuous_id continuous_const
  intro t ht
  simp only [id] at ht
  obtain rfl : t = 3 := by linarith
  unfold fdBoundary_H_inner34
  simp only [show (3 : ℝ) ≤ 4 by norm_num, ite_true]
  rw [show (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast
  ring

private def fdBoundary_H_inner1234 (H : ℝ) : ℝ → ℂ := fun t ↦
  if t ≤ 2 then
    exp ((↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)
  else fdBoundary_H_inner234 H t

private lemma fdBoundary_H_inner1234_cont (H : ℝ) : Continuous (fdBoundary_H_inner1234 H) := by
  apply Continuous.if_le fdBoundary_H_seg23_cont
    (fdBoundary_H_inner234_cont H) continuous_id continuous_const
  intro t ht
  simp only [id] at ht
  obtain rfl : t = 2 := by linarith
  unfold fdBoundary_H_inner234
  simp only [show (2 : ℝ) ≤ 3 by norm_num, ite_true]
  rw [show (↑Real.pi / 3 + (↑(2 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I by push_cast; ring,
    show (↑Real.pi / 2 + (↑(2 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(Real.pi / 2) * I by push_cast; ring]

private lemma fdBoundary_H_eq_layered (H : ℝ) (t : ℝ) :
    fdBoundary_H H t =
      (if t ≤ 1 then 1 / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
       else fdBoundary_H_inner1234 H t) := by
  unfold fdBoundary_H fdBoundary_H_inner1234 fdBoundary_H_inner234 fdBoundary_H_inner34
  split_ifs <;> rfl

@[fun_prop]
theorem fdBoundary_H_continuous (H : ℝ) :
    Continuous (fdBoundary_H H) := by
  rw [show fdBoundary_H H = (fun t ↦ if t ≤ 1 then
      1 / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
      else fdBoundary_H_inner1234 H t) from funext (fdBoundary_H_eq_layered H)]
  apply Continuous.if_le (fdBoundary_H_seg1_cont H) (fdBoundary_H_inner1234_cont H)
    continuous_id continuous_const
  intro t ht
  simp only [id] at ht
  obtain rfl : t = 1 := by linarith
  unfold fdBoundary_H_inner1234
  simp only [show (1 : ℝ) ≤ 2 by norm_num, ite_true]
  rw [show (↑Real.pi / 3 + (↑(1 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 3) * I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

end
