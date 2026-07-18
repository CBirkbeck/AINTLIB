/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.WeilPairing.OneSubComapConcrete
import HasseWeil.HasseBound.WeilPairing.OneSubFrobeniusBaseChangeWitnesses
import HasseWeil.HasseBound.WeilPairing.WallAGenericRealization

/-!
# Affine residue calculus for addition-formula isogenies

This file provides residue arithmetic for the base-changed Weierstrass function field and the
invariant-differential tangent-slope residue for a pair of isogenies with equal affine image.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

noncomputable local instance instDecEqACAffineResidue : DecidableEq (AlgebraicClosure K) :=
  Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]
variable [Fintype W.toAffine.Point]

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- `resid`-form: `x_gen^{K̄} ≡ P.x` modulo `m_P` (the generic `x`-coordinate residues to `P.x`).
Public re-derivation of `SamePlace.resid_x_gen`. -/
theorem residPV_x_gen (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
  (AlgebraicClosure K)).SmoothPoint) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)) -
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        P.x) < 1 := by
  rw [HasseWeil.x_gen_sub_const_eq_algebraMap_XClass]
  exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
    (C := (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K))) _ P).mpr (HasseWeil.XClass_mem_maximalIdealAt _ P P.x rfl)

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- A residue `u ≡ a` makes `u` regular at `P` (`pV P u ≤ 1`). -/
theorem residPV_le_one {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
  (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (h : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P (u - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P u ≤ 1 := by
  rw [show u = (u - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a
    by ring]
  exact pointValuation_add_le_one (W.baseChange (AlgebraicClosure K)) P (le_of_lt h)
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation_algebraMap_F_le_one P a)

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- Residues multiply: `u ≡ a`, `v ≡ b` ⟹ `u·v ≡ a·b`. -/
theorem residPV_mul {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
  (AlgebraicClosure K)).SmoothPoint}
    {u v : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a b : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P (u - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1)
    (hv : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P (v - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P (u * v - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a * b)) < 1 := by
  have hu_le := residPV_le_one W hu
  rw [show u * v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a * b) =
      u * (v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField b *
        (u - algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) by
        rw [map_mul]
        ring]
  refine lt_of_le_of_lt (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).pointValuation P).map_add _ _) (max_lt ?_ ?_)
  · exact pointValuation_mul_lt_one_of_le_and_lt (W.baseChange (AlgebraicClosure K)) P hu_le hv
  · exact pointValuation_mul_lt_one_of_le_and_lt (W.baseChange (AlgebraicClosure K)) P
      ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
        K)).pointValuation_algebraMap_F_le_one P b) hu

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- Residues raise to a power: `u ≡ a` ⟹ `u^n ≡ a^n`. -/
theorem residPV_pow {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
  (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P (u - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) < 1) (n : ℕ) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P (u ^ n - algebraMap (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a ^ n)) < 1 := by
  induction n with
  | zero =>
    simp only [pow_zero, map_one, sub_self, map_zero]
    exact zero_lt_one
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact residPV_mul W ih hu

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- A scalar `algebraMap c` residues to `c`. -/
theorem residPV_const (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) (c : AlgebraicClosure K) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField c
        -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          c) < 1 := by
  rw [sub_self, map_zero]
  exact zero_lt_one

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- Residues subtract: `u ≡ a`, `v ≡ b` ⟹ `u − v ≡ a − b`. -/
theorem residPV_sub {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u v : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a b : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField a) < 1)
    (hv : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField b) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (u - v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField (a - b)) < 1 := by
  have heq : u - v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a - b) =
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField a) -
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField b) := by
    rw [map_sub]
    abel
  rw [heq]
  exact lt_of_le_of_lt
    (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P).map_sub _ _)
    (max_lt hu hv)

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- Residues add: `u ≡ a`, `v ≡ b` ⟹ `u + v ≡ a + b`. -/
theorem residPV_add {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u v : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a b : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField a) < 1)
    (hv : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField b) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (u + v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField (a + b)) < 1 := by
  have heq : u + v - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (a + b) =
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField a) +
      (v - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField b) := by
    rw [map_add]
    abel
  rw [heq]
  exact lt_of_le_of_lt
    (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P).map_add _ _)
    (max_lt hu hv)

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- Residues negate: `u ≡ a` ⟹ `−u ≡ −a`. -/
theorem residPV_neg {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (hu : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField a) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (-u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField (-a)) < 1 := by
  have h0 : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
    K)).pointValuation P
      ((0 : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          0) < 1 := by
    have : (0 : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField 0
          = 0 := by
      rw [_root_.map_zero, sub_self]
    rw [this, Valuation.map_zero]
    exact zero_lt_one
  have := residPV_sub W h0 hu
  rwa [zero_sub, zero_sub] at this

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [(W.baseChange (AlgebraicClosure
  K)).toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- A residue `u ≡ a` with `a ≠ 0` makes `u` a unit at `P` (`pV P u = 1`). -/
theorem residPV_unit {P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint}
    {u : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField} {a : AlgebraicClosure K}
    (h : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P
      (u - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
        K)).toAffine.FunctionField a) < 1)
    (ha : a ≠ 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P u = 1 := by
  have hconst : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).pointValuation P
      (algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a)
        = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero (W.baseChange (AlgebraicClosure K)) P ha
  rw [show u = (u - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a
        by abel,
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).pointValuation P).map_add_eq_of_lt_right
      (by
        rw [hconst]
        exact h), hconst]

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] in
private theorem alpha_star_u_residPV_aux
    (α : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (hx : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1)
    (hy : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (alpha_star_u (W.baseChange (AlgebraicClosure K)) α -
        algebraMap (AlgebraicClosure K)
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (2 * y + (W.baseChange (AlgebraicClosure K)).a₁ * x +
            (W.baseChange (AlgebraicClosure K)).a₃)) < 1 := by
  rw [alpha_star_u_eq, show HasseWeil.u_gen (W.baseChange (AlgebraicClosure K)) =
      2 * HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).a₁ * HasseWeil.x_gen (W.baseChange (AlgebraicClosure
          K)) +
      algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (W.baseChange (AlgebraicClosure K)).a₃ from rfl]
  simp only [map_add, map_mul, map_ofNat, AlgHom.commutes]
  have r2 := residPV_const W P (2 : AlgebraicClosure K)
  have ra1 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₁
  have ra3 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₃
  have hstep := residPV_add W (residPV_add W (residPV_mul W r2 hy) (residPV_mul W ra1 hx)) ra3
  refine lt_of_eq_of_lt (congrArg _ ?_) hstep
  simp only [map_ofNat, map_add, map_mul]

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] in
private theorem Dω_y_pullback_numerator_residPV_aux
    (α : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x y : AlgebraicClosure K}
    (hx : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x) < 1)
    (hy : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y) < 1) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      ((3 * α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) ^ 2 +
          2 * algebraMap (AlgebraicClosure K)
              (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₂ *
            α.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) +
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
            (W.baseChange (AlgebraicClosure K)).a₄ -
          algebraMap (AlgebraicClosure K)
              (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
              (W.baseChange (AlgebraicClosure K)).a₁ *
            α.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (3 * x ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * x +
            (W.baseChange (AlgebraicClosure K)).a₄ -
            (W.baseChange (AlgebraicClosure K)).a₁ * y)) < 1 := by
  have r3 := residPV_const W P (3 : AlgebraicClosure K)
  have ra2 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₂
  have ra4 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₄
  have ra1 := residPV_const W P (W.baseChange (AlgebraicClosure K)).a₁
  have hstep := residPV_sub W (residPV_add W (residPV_add W
    (residPV_mul W r3 (residPV_pow W hx 2))
    (residPV_mul W (residPV_mul W (residPV_const W P (2 : AlgebraicClosure K)) ra2) hx)) ra4)
    (residPV_mul W ra1 hy)
  refine lt_of_eq_of_lt (congrArg _ ?_) hstep
  simp only [map_ofNat, map_add, map_mul, map_sub]

omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] in
/-- A secant whose left summand has vanishing generator differentials residues to the tangent slope
when the two summands have the same affine image. -/
theorem addSlopePair_resid_tangent_of_DωLeft_zero
    (α₁ α₂ : Isogeny (W.baseChange (AlgebraicClosure K)).toAffine
      (W.baseChange (AlgebraicClosure K)).toAffine)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint) {x₁ y₁ x₂ y₂ : AlgebraicClosure K}
    (hDα₁x : Dω (W.baseChange (AlgebraicClosure K))
      (α₁.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) = 0)
    (hDα₁y : Dω (W.baseChange (AlgebraicClosure K))
      (α₁.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) = 0)
    (hx₁ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₁.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x₁) < 1)
    (hy₁ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₁.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y₁) < 1)
    (hx₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₂.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField x₂) < 1)
    (hy₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
        (α₂.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) -
          algebraMap (AlgebraicClosure K)
            (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField y₂) < 1)
    (hxeq : x₁ = x₂) (hyeq : y₁ = y₂)
    (huQ : 2 * y₁ + (W.baseChange (AlgebraicClosure K)).a₁ * x₁ +
      (W.baseChange (AlgebraicClosure K)).a₃ ≠ 0)
    (hcoeff₂ : omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) α₂ ∈
      (algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField).range)
    (hcoeff₂_ne : omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) α₂ ≠ 0)
    (hu₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P P
        (alpha_star_u (W.baseChange (AlgebraicClosure K)) α₂) = 0) :
    (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P
      (addSlopePair α₁ α₂ -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          ((3 * x₁ ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * x₁ +
              (W.baseChange (AlgebraicClosure K)).a₄ -
              (W.baseChange (AlgebraicClosure K)).a₁ * y₁) /
            (2 * y₁ + (W.baseChange (AlgebraicClosure K)).a₁ * x₁ +
              (W.baseChange (AlgebraicClosure K)).a₃))) < 1 := by
  set nuQ : AlgebraicClosure K := 3 * x₁ ^ 2 + 2 * (W.baseChange (AlgebraicClosure K)).a₂ * x₁
    + (W.baseChange (AlgebraicClosure K)).a₄ - (W.baseChange (AlgebraicClosure K)).a₁ * y₁
    with hnuQ
  set uQ : AlgebraicClosure K := 2 * y₁ + (W.baseChange (AlgebraicClosure K)).a₁ * x₁ +
    (W.baseChange (AlgebraicClosure K)).a₃ with huQ_def
  set lamC : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField :=
    algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField (nuQ
      / uQ) with hlamC
  set f : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField :=
    α₁.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) - α₂.pullback
      (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) with hf
  set g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField :=
    α₁.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) - α₂.pullback
      (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))) with hg
  have hDf : Dω (W.baseChange (AlgebraicClosure K)) f = -(alpha_star_u (W.baseChange
    (AlgebraicClosure K)) α₂ * omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) α₂) :=
    by
    rw [hf, Dω_sub, hDα₁x, Dω_isog_pullback_x_gen (W.baseChange (AlgebraicClosure K)) α₂,
      zero_sub]
  obtain ⟨c₂, hc₂⟩ := hcoeff₂
  have hc₂_ne : c₂ ≠ 0 := fun h ↦ hcoeff₂_ne (by
    rw [h, map_zero] at hc₂
    exact hc₂.symm)
  have hDf_ord : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).ord_P P (Dω (W.baseChange (AlgebraicClosure K)) f) = 0 := by
    rw [hDf, SmoothPlaneCurve.ord_P_neg, (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).ord_P_mul, hu₂, ← hc₂,
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
        K)).ord_P_algebraMap_F_of_ne_zero hc₂_ne, add_zero]
  have hu₂_ne0 : alpha_star_u (W.baseChange (AlgebraicClosure K)) α₂ ≠ 0 := by
    intro h0
    rw [h0, (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).ord_P_zero] at hu₂
    exact WithTop.top_ne_coe hu₂
  have hDf_ne : Dω (W.baseChange (AlgebraicClosure K)) f ≠ 0 := by
    rw [hDf]
    exact neg_ne_zero.mpr (mul_ne_zero hu₂_ne0 hcoeff₂_ne)
  have hf_ne : f ≠ 0 := by
    intro h0
    apply hDf_ne
    rw [h0]
    simp only [Dω_zero]
  have hf_lt : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).pointValuation P f < 1 := by
    have hstep := residPV_sub W hx₁ hx₂
    rw [hf]
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    rw [hxeq, sub_self, map_zero]
    ring
  have hf_ord1 : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).ord_P P f = ((1 : ℤ) : WithTop ℤ) := by
    refine le_antisymm ?_ ?_
    · by_contra hlt
      rw [not_le] at hlt
      have h2le : ((2 : ℤ) : WithTop ℤ) ≤ (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩
        : SmoothPlaneCurve (AlgebraicClosure K)).ord_P P f := by
        obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (((⟨(W.baseChange (AlgebraicClosure
          K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).ord_P_eq_top_iff f).not.mpr
          hf_ne)
        rw [← hm] at hlt ⊢
        rw [WithTop.coe_lt_coe] at hlt
        rw [WithTop.coe_le_coe]
        omega
      have := one_le_ord_P_Dω_of_two_le (W.baseChange (AlgebraicClosure K)) hf_ne P h2le
      rw [hDf_ord] at this
      exact (not_le_of_gt zero_lt_one) this
    · exact_mod_cast ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
      (AlgebraicClosure K)).one_le_ord_P_iff_pointValuation_lt_one (P := P) hf_ne).mpr hf_lt
  have hg_res : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).pointValuation P g < 1 := by
    have hstep := residPV_sub W hy₁ hy₂
    rw [hg]
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    rw [hyeq, sub_self, map_zero]
    ring
  have hpb_ne : α₁.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) ≠
    α₂.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K))) :=
    sub_ne_zero.mp hf_ne
  have hslope_eq : addSlopePair α₁ α₂ = g / f := by rw [addSlopePair_eq_of_x_ne hpb_ne, hf,
    hg]
  have hDg : Dω (W.baseChange (AlgebraicClosure K)) g = -((3 * (α₂.pullback (HasseWeil.x_gen
    (W.baseChange (AlgebraicClosure K)))) ^ 2 +
        2 * algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
          K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₂ *
          (α₂.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) +
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).a₄ -
        algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
          (W.baseChange (AlgebraicClosure K)).a₁ *
          (α₂.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))))) *
      omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) α₂) := by
    rw [hg, Dω_sub, hDα₁y, Dω_isog_pullback_y_gen (W.baseChange (AlgebraicClosure K)) α₂,
      zero_sub]
  have hu₂_resid : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).pointValuation P
      (alpha_star_u (W.baseChange (AlgebraicClosure K)) α₂ - algebraMap (AlgebraicClosure K)
        (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField uQ) < 1 := by
    rw [huQ_def, hxeq, hyeq]
    exact alpha_star_u_residPV_aux W α₂ P hx₂ hy₂
  set φ : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField := g - lamC * f with hφ
  have hφ_res : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).pointValuation P φ < 1 := by
    rw [hφ]
    have hlamf : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
      (AlgebraicClosure K)).pointValuation P (lamC * f) < 1 := by
      rw [hlamC]
      exact pointValuation_mul_lt_one_of_le_and_lt (W.baseChange (AlgebraicClosure K)) P
        ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
          K)).pointValuation_algebraMap_F_le_one P (nuQ / uQ)) hf_lt
    exact lt_of_le_of_lt (((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
      (AlgebraicClosure K)).pointValuation P).map_sub _ _) (max_lt hg_res hlamf)
  have hDφ_res : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
    (AlgebraicClosure K)).pointValuation P (Dω (W.baseChange (AlgebraicClosure K)) φ) < 1 := by
    have hDlamC : Dω (W.baseChange (AlgebraicClosure K)) lamC = 0 := by
      rw [hlamC]
      exact Dω_algebraMap _ _
    have hDφ_eq : Dω (W.baseChange (AlgebraicClosure K)) φ = Dω (W.baseChange (AlgebraicClosure
      K)) g - lamC * Dω (W.baseChange (AlgebraicClosure K)) f := by
      rw [hφ, Dω_sub, Dω_mul, hDlamC]
      ring
    rw [hDφ_eq, hDg, hDf]
    have hν₂_resid : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
      (AlgebraicClosure K)).pointValuation P
        ((3 * (α₂.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) ^ 2 +
            2 * algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
              K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₂ *
              (α₂.pullback (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) +
            algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
              K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₄ -
            algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
              K)).toAffine.FunctionField (W.baseChange (AlgebraicClosure K)).a₁ *
              (α₂.pullback (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K))))) -
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
            nuQ) < 1 := by
      rw [hnuQ, hxeq, hyeq]
      exact Dω_y_pullback_numerator_residPV_aux W α₂ P hx₂ hy₂
    have rlam : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
      (AlgebraicClosure K)).pointValuation P
        (lamC - algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure
          K)).toAffine.FunctionField (nuQ / uQ)) < 1 := by
      rw [hlamC, sub_self, Valuation.map_zero]
      exact zero_lt_one
    have rc₂ : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
      (AlgebraicClosure K)).pointValuation P
        (omegaPullbackCoeff (W.baseChange (AlgebraicClosure K)) α₂ -
          algebraMap (AlgebraicClosure K) (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
            c₂) < 1 := by
      rw [hc₂, sub_self, Valuation.map_zero]
      exact zero_lt_one
    have hstep := residPV_sub W
      (residPV_neg W (residPV_mul W hν₂_resid rc₂))
      (residPV_mul W rlam (residPV_neg W (residPV_mul W hu₂_resid rc₂)))
    refine lt_of_eq_of_lt (congrArg _ ?_) hstep
    have hval : -(nuQ * c₂) - nuQ / uQ * -(uQ * c₂) = 0 := by
      field_simp
      ring
    rw [hval]
    simp only [map_zero]
    ring
  by_cases hφ0 : φ = 0
  · have hgf : g = lamC * f := by
      rw [hφ, sub_eq_zero] at hφ0
      exact hφ0
    rw [hslope_eq, hgf, mul_div_assoc, div_self hf_ne, mul_one, hlamC, sub_self, map_zero]
    exact zero_lt_one
  · have hφ_ge1 : ((1 : ℤ) : WithTop ℤ) ≤ (⟨(W.baseChange (AlgebraicClosure
    K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).ord_P P φ :=
      ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
        K)).one_le_ord_P_iff_pointValuation_lt_one (P := P) hφ0).mpr hφ_res
    have hDφ_ge1 : ((1 : ℤ) : WithTop ℤ) ≤ (⟨(W.baseChange (AlgebraicClosure
      K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).ord_P P (Dω (W.baseChange
      (AlgebraicClosure K)) φ) := by
      by_cases hDφ0 : Dω (W.baseChange (AlgebraicClosure K)) φ = 0
      · rw [hDφ0, (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
        (AlgebraicClosure K)).ord_P_zero]
        exact le_top
      · exact ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
        (AlgebraicClosure K)).one_le_ord_P_iff_pointValuation_lt_one (P := P) hDφ0).mpr hDφ_res
    have hφ_ge2 : ((2 : ℤ) : WithTop ℤ) ≤ (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩
      : SmoothPlaneCurve (AlgebraicClosure K)).ord_P P φ :=
      two_le_ord_P_of_Dω_vanishes_of_uniformizer (W.baseChange (AlgebraicClosure K)) hφ0 P hφ_ge1
        hDφ_ge1 hf_ord1 hDf_ord
    have hdiff_eq : addSlopePair α₁ α₂ - lamC = φ / f := by
      rw [hslope_eq, hφ, eq_comm, sub_div, mul_div_assoc, div_self hf_ne, mul_one]
    have hdiff_ne : addSlopePair α₁ α₂ - lamC ≠ 0 := by
      rw [hdiff_eq]
      exact div_ne_zero hφ0 hf_ne
    have hord_diff : ((1 : ℤ) : WithTop ℤ) ≤ (⟨(W.baseChange (AlgebraicClosure
      K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).ord_P P (addSlopePair α₁ α₂ -
      lamC) := by
      rw [hdiff_eq, div_eq_mul_inv, (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ord_P_mul, (⟨(W.baseChange (AlgebraicClosure
        K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure K)).ord_P_inv _ hf_ne, hf_ord1]
      calc ((1 : ℤ) : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) + (-((1 : ℤ) : WithTop ℤ)) :=
        rfl
        _ ≤ (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve
          (AlgebraicClosure K)).ord_P P φ + (-((1 : ℤ) : WithTop ℤ)) := by gcongr
    rw [hlamC] at hdiff_ne hord_diff
    exact ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ : SmoothPlaneCurve (AlgebraicClosure
      K)).one_le_ord_P_iff_pointValuation_lt_one (P := P) hdiff_ne).mp hord_diff

end HasseWeil.WeilPairing
