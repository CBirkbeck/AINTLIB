/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.IntegralClosure
import HasseWeil.Curves.NormValuation
import HasseWeil.EC.TranslateLocalRing
import HasseWeil.Ramification

/-!
# Discharge of `IsTranslateValuationCompatible` for non-zero translation

The substantive geometric content of Step (B'') of the ord-transport arc.
For non-zero `k = (xk, yk)` and a smooth point `P` with `(P + k).IsSome`
(translate is finite), the K-algebra automorphism
`τ_k = translateAlgEquivOfPoint W k` carries `localRingAt(P+k)` bijectively
onto `localRingAt(P)` and preserves the maximal ideals — hence
`pointValuation P ∘ τ_k = pointValuation (P+k)` as Valuations on K(E).

The proof proceeds via the **reviewer-blessed geometric route**:

1. **Generator vanishing** (`IsTranslateXY_evaluatesAt`): the τ_k-image
   of the maxIdeal generators `(x_gen − alg(P+k).x)` and
   `(y_gen − alg(P+k).y)` (after subtracting the corresponding constants)
   vanish at P. This uses the addition law on E geometrically: at P, the
   value of `τ_k(x_gen) = translateX_xy_k` equals `(P+k).x` because
   `τ_k` is the function-field-level translation by `k`.

2. **CoordinateRing-restricted maxIdeal compatibility**: by polynomial
   induction over CoordinateRing, the generator vanishing extends to all
   coord ring elements `r ∈ maxIdealAt(P+k)`.

3. **Full maxIdeal compatibility**: the localisation extension lifts
   from coord ring images to all of K(E).

4. **Valuation equality**: by DVR uniqueness applied to the maxIdeal-
   preserving local ring iso.

This file ships pieces 1–4 step by step.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.1, II.2, III.4.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- For `P.x ≠ xk`, the coord ring element `XClass W xk` is NOT in the
maximal ideal at `P`. Companion to `XClass_mem_maximalIdealAt` (which
handles the `P.x = xk` case). -/
theorem XClass_notMem_maximalIdealAt (P : (W_smooth W).SmoothPoint) (xk : F) (h_x : P.x ≠ xk) :
    Affine.CoordinateRing.XClass W.toAffine xk ∉ (W_smooth W).maximalIdealAt P := by
  intro h_mem
  apply h_x
  have h_eval : (W_smooth W).evalAt P
      (Affine.CoordinateRing.XClass W.toAffine xk) = 0 := by
    rw [← RingHom.mem_ker, (W_smooth W).ker_evalAt P]
    exact h_mem
  have h_xk_eval : (W_smooth W).evalAt P
      (Affine.CoordinateRing.XClass W.toAffine xk) = P.x - xk := by
    change ((⟨W.toAffine⟩ : Curves.SmoothPlaneCurve F).evalAt P)
        (Affine.CoordinateRing.XClass W.toAffine xk) = P.x - xk
    unfold Affine.CoordinateRing.XClass
    rw [SmoothPlaneCurve.evalAt_mk]
    simp [Polynomial.evalEval_C]
  exact sub_eq_zero.mp (h_xk_eval ▸ h_eval)

/-- For `P.x ≠ xk`, the function `x_gen − alg xk` has `pointValuation = 1`
at `P` (i.e., is a unit in localRingAt(P)). This is the chord-case
non-vanishing complement of the negSmoothPoint vanishing. -/
theorem pointValuation_x_gen_sub_const_eq_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P (x_gen W - algebraMap F KE xk) = 1 := by
  rw [x_gen_sub_const_eq_algebraMap_XClass W xk]
  have h_le : (W_smooth W).pointValuation P
      (algebraMap W.toAffine.CoordinateRing KE
        (Affine.CoordinateRing.XClass W.toAffine xk)) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_le_one _ P
  have h_not_lt : ¬ (W_smooth W).pointValuation P
      (algebraMap W.toAffine.CoordinateRing KE
        (Affine.CoordinateRing.XClass W.toAffine xk)) < 1 := by
    intro h_lt
    apply XClass_notMem_maximalIdealAt W P xk h_x
    exact (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) _ P).mp h_lt
  exact le_antisymm h_le (not_lt.mp h_not_lt)

/-- When `P.x ≠ xk`, `(x_gen − alg xk)` is a unit in K(E), and its inverse
also has `pointValuation = 1` at `P`. -/
theorem pointValuation_x_gen_sub_const_inv_eq_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P (x_gen W - algebraMap F KE xk)⁻¹ = 1 := by
  have h_ne : x_gen W - algebraMap F KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have h_eq : (W_smooth W).pointValuation P (x_gen W - algebraMap F KE xk) = 1 :=
    pointValuation_x_gen_sub_const_eq_one_of_X_ne W P xk h_x
  rw [map_inv₀, h_eq]
  rfl

/-- For chord-case `P` (P.x ≠ xk), the translate slope `(y_gen − alg yk) /
(x_gen − alg xk)` is in `localRingAt(P)` (no pole). -/
theorem pointValuation_translateSlope_xy_le_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P (translateSlope_xy W xk yk) ≤ 1 := by
  unfold translateSlope_xy
  rw [Affine.slope_of_X_ne (hx := fun h_eq ↦ x_gen_sub_const_ne_zero W xk
    (sub_eq_zero.mpr h_eq))]
  rw [div_eq_mul_inv]
  apply pointValuation_mul_le_one W P
  · have hy_eq := y_gen_sub_const_eq_algebraMap_YClass W yk
    rw [hy_eq]
    exact (W_smooth W).pointValuation_algebraMap_le_one _ P
  · exact le_of_eq (pointValuation_x_gen_sub_const_inv_eq_one_of_X_ne W P xk h_x)

/-- Helper: for chord-case `P` (P.x ≠ xk), the algebraic identity
`(y_gen − alg yk) · (P.x − xk) − (P.y − yk) · (x_gen − alg xk)` vanishes
at `P`. This is the substantive content of "slope difference vanishes at P". -/
theorem pointValuation_chord_numerator_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      ((y_gen W - algebraMap F KE yk) * algebraMap F KE (P.x - xk) -
        algebraMap F KE (P.y - yk) * (x_gen W - algebraMap F KE xk)) < 1 := by
  have h_eq : (y_gen W - algebraMap F KE yk) * algebraMap F KE (P.x - xk) -
        algebraMap F KE (P.y - yk) * (x_gen W - algebraMap F KE xk) =
      algebraMap F KE (P.x - xk) * (y_gen W - algebraMap F KE P.y) -
        algebraMap F KE (P.y - yk) * (x_gen W - algebraMap F KE P.x) := by
    push_cast
    ring
  rw [h_eq]
  refine lt_of_le_of_lt
    (((W_smooth W).pointValuation P).map_sub _ _) ?_
  apply max_lt
  · have h1 : (W_smooth W).pointValuation P (algebraMap F KE (P.x - xk)) ≤ 1 :=
      (W_smooth W).pointValuation_algebraMap_F_le_one P (P.x - xk)
    have h2 : (W_smooth W).pointValuation P (y_gen W - algebraMap F KE P.y) < 1 := by
      have h_ymem : Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y) ∈
          (W_smooth W).maximalIdealAt P :=
        YClass_mem_maximalIdealAt W P P.y rfl
      have h_lt :=
        (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
          (C := W_smooth W) (Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y))
          P).mpr h_ymem
      have h_eq := y_gen_sub_const_eq_algebraMap_YClass W P.y
      rw [h_eq]
      exact h_lt
    exact pointValuation_mul_lt_one_of_le_and_lt W P h1 h2
  · have h1 : (W_smooth W).pointValuation P (algebraMap F KE (P.y - yk)) ≤ 1 :=
      (W_smooth W).pointValuation_algebraMap_F_le_one P (P.y - yk)
    have h2 : (W_smooth W).pointValuation P (x_gen W - algebraMap F KE P.x) < 1 := by
      have h_xmem : Affine.CoordinateRing.XClass W.toAffine P.x ∈
          (W_smooth W).maximalIdealAt P :=
        XClass_mem_maximalIdealAt W P P.x rfl
      have h_lt :=
        (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
          (C := W_smooth W) (Affine.CoordinateRing.XClass W.toAffine P.x) P).mpr h_xmem
      have h_eq := x_gen_sub_const_eq_algebraMap_XClass W P.x
      rw [h_eq]
      exact h_lt
    exact pointValuation_mul_lt_one_of_le_and_lt W P h1 h2

/-- A nonzero constant in F has `pointValuation = 1` at any smooth point. -/
theorem pointValuation_algebraMap_F_eq_one_of_ne_zero
    (P : (W_smooth W).SmoothPoint) {c : F} (hc : c ≠ 0) :
    (W_smooth W).pointValuation P (algebraMap F KE c) = 1 := by
  have h_ord : (W_smooth W).ord_P P (algebraMap F KE c) = 0 :=
    Curves.SmoothPlaneCurve.ord_P_algebraMap_F_of_ne_zero (W_smooth W) hc P
  have h_alg_ne : (algebraMap F KE c : KE) ≠ 0 := fun h ↦ hc <|
    FaithfulSMul.algebraMap_injective F KE (h.trans (map_zero _).symm)
  unfold Curves.SmoothPlaneCurve.ord_P at h_ord
  by_cases hv : (W_smooth W).pointValuation P (algebraMap F KE c) = 0
  · exfalso
    exact h_alg_ne ((Curves.SmoothPlaneCurve.pointValuation_eq_zero_iff
      (algebraMap F KE c)).mp hv)
  · rw [dif_neg hv] at h_ord
    have h_int : (-(WithZero.unzero hv).toAdd : ℤ) = 0 := by exact_mod_cast h_ord
    have h_toAdd : (WithZero.unzero hv).toAdd = 0 := by lia
    have h_unz : WithZero.unzero hv = 1 := by
      apply Multiplicative.toAdd.injective
      simp [h_toAdd]
    rw [← WithZero.coe_unzero hv, h_unz]
    rfl

/-- If the denominator `b` is a unit at `P` (`pointValuation = 1`) and `a ∈ m_P`
(`pointValuation < 1`), then `a / b ∈ m_P`. -/
private theorem pointValuation_div_lt_one_of_denom_eq_one (P : (W_smooth W).SmoothPoint)
    {a b : (W_smooth W).FunctionField}
    (hb : (W_smooth W).pointValuation P b = 1) (ha : (W_smooth W).pointValuation P a < 1) :
    (W_smooth W).pointValuation P (a / b) < 1 := by
  rw [div_eq_mul_inv, Valuation.map_mul, map_inv₀, hb, inv_one, mul_one]
  exact ha

/-- For chord-case `P` (P.x ≠ xk), the difference `translateSlope_xy −
alg(chord slope at P, k)` vanishes at `P`. -/
theorem pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      (translateSlope_xy W xk yk -
        algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) < 1 := by
  have h_denom_ne_F : P.x - xk ≠ 0 := sub_ne_zero.mpr h_x
  have h_denom_xgen_ne : x_gen W - algebraMap F KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have h_tslope : translateSlope_xy W xk yk =
      (y_gen W - algebraMap F KE yk) / (x_gen W - algebraMap F KE xk) := by
    unfold translateSlope_xy
    rw [Affine.slope_of_X_ne (hx := fun h_eq ↦
      h_denom_xgen_ne (sub_eq_zero.mpr h_eq))]
  have h_alg_slope : W.toAffine.slope P.x xk P.y yk =
      (P.y - yk) / (P.x - xk) := by
    rw [Affine.slope_of_X_ne (hx := h_x)]
  rw [h_tslope, h_alg_slope, map_div₀]
  have h_alg_xpx_ne : algebraMap F KE (P.x - xk) ≠ 0 := by
    intro h
    apply h_denom_ne_F
    exact FaithfulSMul.algebraMap_injective F KE
      (h.trans (map_zero _).symm)
  have h_combine :
      (y_gen W - algebraMap F KE yk) / (x_gen W - algebraMap F KE xk) -
        algebraMap F KE (P.y - yk) / algebraMap F KE (P.x - xk) =
      ((y_gen W - algebraMap F KE yk) * algebraMap F KE (P.x - xk) -
          algebraMap F KE (P.y - yk) * (x_gen W - algebraMap F KE xk)) /
        ((x_gen W - algebraMap F KE xk) * algebraMap F KE (P.x - xk)) := by
    field_simp
  rw [h_combine]
  have h_xgen_pV : (W_smooth W).pointValuation P
      (x_gen W - algebraMap F KE xk) = 1 :=
    pointValuation_x_gen_sub_const_eq_one_of_X_ne W P xk h_x
  have h_alg_pV : (W_smooth W).pointValuation P (algebraMap F KE (P.x - xk)) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P h_denom_ne_F
  have h_denom_pV :
      (W_smooth W).pointValuation P
        ((x_gen W - algebraMap F KE xk) * algebraMap F KE (P.x - xk)) = 1 := by
    calc (W_smooth W).pointValuation P
            ((x_gen W - algebraMap F KE xk) * algebraMap F KE (P.x - xk))
        = (W_smooth W).pointValuation P (x_gen W - algebraMap F KE xk) *
            (W_smooth W).pointValuation P (algebraMap F KE (P.x - xk)) :=
        Valuation.map_mul _ _ _
      _ = 1 * 1 := by rw [h_xgen_pV, h_alg_pV]
      _ = 1 := one_mul _
  have h_num_pV_lt :
      (W_smooth W).pointValuation P
        ((y_gen W - algebraMap F KE yk) * algebraMap F KE (P.x - xk) -
          algebraMap F KE (P.y - yk) * (x_gen W - algebraMap F KE xk)) < 1 :=
    pointValuation_chord_numerator_lt_one_of_X_ne W P xk yk h_x
  exact pointValuation_div_lt_one_of_denom_eq_one W P h_denom_pV h_num_pV_lt

/-- Chord-case slope factor bound: the product
`(slope_K − alg slope_F) · (slope_K + alg slope_F + a₁)` has `pointValuation < 1` at `P`,
where `slope_K = translateSlope_xy W xk yk` and `slope_F = W.slope P.x xk P.y yk`. -/
private theorem pointValuation_slope_diff_mul_sum_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      ((translateSlope_xy W xk yk - algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) *
        (translateSlope_xy W xk yk + algebraMap F KE (W.toAffine.slope P.x xk P.y yk) +
          (W_KE W).a₁)) < 1 := by
  set slope_K : KE := translateSlope_xy W xk yk with hslope_K
  set slope_F : F := W.toAffine.slope P.x xk P.y yk with hslope_F
  have h_slope_diff_lt :
      (W_smooth W).pointValuation P (slope_K - algebraMap F KE slope_F) < 1 :=
    pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne W P xk yk h_x
  have h_slope_K_le : (W_smooth W).pointValuation P slope_K ≤ 1 :=
    pointValuation_translateSlope_xy_le_one_of_X_ne W P xk yk h_x
  have h_alg_slope_F_le : (W_smooth W).pointValuation P (algebraMap F KE slope_F) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P slope_F
  have h_alg_a1_le : (W_smooth W).pointValuation P ((W_KE W).a₁) ≤ 1 := by
    change (W_smooth W).pointValuation P ((W.map (algebraMap F KE)).a₁) ≤ 1
    exact (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁
  have h_sum_le : (W_smooth W).pointValuation P
      (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) ≤ 1 :=
    pointValuation_add_le_one W P
      (pointValuation_add_le_one W P h_slope_K_le h_alg_slope_F_le)
      h_alg_a1_le
  have h_swap : (slope_K - algebraMap F KE slope_F) *
      (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) =
    (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) *
      (slope_K - algebraMap F KE slope_F) := by ring
  rw [h_swap]
  exact pointValuation_mul_lt_one_of_le_and_lt W P h_sum_le h_slope_diff_lt

/-- The generator difference `x_gen − alg P.x` lies in the maximal ideal at `P`
(vanishes at `P`), hence has `pointValuation < 1`. -/
private theorem pointValuation_x_gen_sub_alg_x_self_lt_one
    (P : (W_smooth W).SmoothPoint) :
    (W_smooth W).pointValuation P (x_gen W - algebraMap F KE P.x) < 1 := by
  have h_xmem : Affine.CoordinateRing.XClass W.toAffine P.x ∈
      (W_smooth W).maximalIdealAt P :=
    XClass_mem_maximalIdealAt W P P.x rfl
  have h_lt :=
    (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) (Affine.CoordinateRing.XClass W.toAffine P.x) P).mpr h_xmem
  have h_eq := x_gen_sub_const_eq_algebraMap_XClass W P.x
  rw [h_eq]
  exact h_lt

/-- For chord-case `P` (P.x ≠ xk), the difference
`translateX_xy − alg(W.addX P.x xk slope_at_P)` has `pointValuation < 1` at P.
This is the geometric content "value of τ_k(x_gen) at P equals (P+k).x"
in the chord case. -/
theorem pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      (translateX_xy W xk yk -
        algebraMap F KE
          (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))) < 1 := by
  set slope_K : KE := translateSlope_xy W xk yk with hslope_K
  set slope_F : F := W.toAffine.slope P.x xk P.y yk with hslope_F
  unfold translateX_xy
  have h_alg_addX :
      algebraMap F KE (W.toAffine.addX P.x xk slope_F) =
        (W_KE W).toAffine.addX (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE slope_F) := by
    show (algebraMap F KE) (W.toAffine.addX P.x xk slope_F) = _
    change _ = (W.map (algebraMap F KE)).toAffine.addX _ _ _
    exact (Affine.map_addX (algebraMap F KE) P.x xk slope_F).symm
  rw [h_alg_addX]
  have h_addX_diff :
      (W_KE W).toAffine.addX (x_gen W) (algebraMap F KE xk) slope_K -
        (W_KE W).toAffine.addX (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE slope_F) =
      (slope_K - algebraMap F KE slope_F) *
        (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) -
      (x_gen W - algebraMap F KE P.x) := by
    change slope_K ^ 2 + (W_KE W).a₁ * slope_K - (W_KE W).a₂ - x_gen W - algebraMap F KE xk -
        ((algebraMap F KE slope_F) ^ 2 + (W_KE W).a₁ * algebraMap F KE slope_F -
          (W_KE W).a₂ - algebraMap F KE P.x - algebraMap F KE xk) =
      _
    ring
  rw [h_addX_diff]
  refine lt_of_le_of_lt
    (((W_smooth W).pointValuation P).map_sub _ _) ?_
  apply max_lt
  · exact pointValuation_slope_diff_mul_sum_lt_one_of_X_ne W P xk yk h_x
  · exact pointValuation_x_gen_sub_alg_x_self_lt_one W P

/-- Helper for chord-case y-evaluation: the algebraic identity
`addY(a, b, c, ℓ) = -(ℓ · (addX(a, b, ℓ) - a) + c) - W.a₁ · addX(a, b, ℓ) - W.a₃`. -/
theorem addY_eq_unfolded_neg_negAddY {R : Type*} [CommRing R]
    (W' : WeierstrassCurve R) (x₁ x₂ y₁ ℓ : R) :
    W'.toAffine.addY x₁ x₂ y₁ ℓ =
      -(ℓ * (W'.toAffine.addX x₁ x₂ ℓ - x₁) + y₁) - W'.a₁ * W'.toAffine.addX x₁ x₂ ℓ -
        W'.a₃ := by
  change W'.toAffine.negY (W'.toAffine.addX x₁ x₂ ℓ)
      (W'.toAffine.negAddY x₁ x₂ y₁ ℓ) = _
  unfold WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.negAddY
  ring

/-- Pure ring identity used to split the chord-case `addY`-difference into the
four valuation-bounded pieces (T1–T4) of
`pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne`. With `aK`/`aF` the
K(E)- and F-level `addX` values, `ℓK`/`ℓF` the slopes, `xK`/`yK` the generic
coordinates and `a₁`/`a₃` the curve constants, the unfolded `negAddY`-difference
equals `-T1 + T2 - T3 - T4`. -/
theorem addY_diff_four_term_ring_identity {R : Type*} [CommRing R]
    (ℓK aK xK yK xP yP ℓF aF a₁ a₃ : R) :
    -(ℓK * (aK - xK) + yK) - a₁ * aK - a₃ -
        (-(ℓF * (aF - xP) + yP) - a₁ * aF - a₃) =
      -((ℓK + a₁) * (aK - aF)) + ℓK * (xK - xP) -
        (ℓK - ℓF) * (aF - xP) - (yK - yP) := by
  ring

/-- T1 (chord case): the product `(slope_K + a₁) · (translateX_xy − alg addX)`
has `pointValuation < 1` at `P`. The first factor has valuation `≤ 1` (sum of a
slope with valuation `≤ 1` and a constant), the second is the regular vanishing
of the `x`-coordinate evaluation (`…translateX_xy_sub_alg_addX…`). -/
private theorem pointValuation_slope_add_a₁_mul_translateX_diff_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      ((translateSlope_xy W xk yk + (W.map (algebraMap F KE)).a₁) *
        ((W.map (algebraMap F KE)).toAffine.addX (x_gen W) (algebraMap F KE xk)
            (translateSlope_xy W xk yk) -
          algebraMap F KE (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk)))) < 1 := by
  have h_factor1_le : (W_smooth W).pointValuation P
      (translateSlope_xy W xk yk + (W.map (algebraMap F KE)).a₁) ≤ 1 := by
    apply pointValuation_add_le_one W P
    · exact pointValuation_translateSlope_xy_le_one_of_X_ne W P xk yk h_x
    · exact (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁
  have h_diff_addX_lt : (W_smooth W).pointValuation P
      ((W.map (algebraMap F KE)).toAffine.addX (x_gen W) (algebraMap F KE xk)
          (translateSlope_xy W xk yk) -
        algebraMap F KE (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))) < 1 := by
    change (W_smooth W).pointValuation P
      (translateX_xy W xk yk -
        algebraMap F KE (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))) < 1
    exact pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne W P xk yk h_x
  exact pointValuation_mul_lt_one_of_le_and_lt W P h_factor1_le h_diff_addX_lt

/-- T2 (chord case): the product `slope_K · (x_gen − alg P.x)` has
`pointValuation < 1` at `P`. The slope has valuation `≤ 1`; the generator
difference `x_gen − alg P.x` vanishes at `P`
(`pointValuation_x_gen_sub_alg_x_self_lt_one`). -/
private theorem pointValuation_slope_mul_x_gen_diff_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      (translateSlope_xy W xk yk * (x_gen W - algebraMap F KE P.x)) < 1 := by
  refine pointValuation_mul_lt_one_of_le_and_lt W P
    (pointValuation_translateSlope_xy_le_one_of_X_ne W P xk yk h_x) ?_
  exact pointValuation_x_gen_sub_alg_x_self_lt_one W P

/-- T3 (chord case): the product `(slope_K − alg slope_F) · (alg addX − alg P.x)`
has `pointValuation < 1` at `P`. The slope difference is the regular vanishing of
the slope evaluation (`…translateSlope_xy_sub_alg_slope…`), strictly `< 1`; the
constant `addX − P.x` lifts from `F`, so its valuation is `≤ 1`. -/
private theorem pointValuation_slope_diff_mul_alg_addX_diff_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      ((translateSlope_xy W xk yk - algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) *
        (algebraMap F KE (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk)) -
          algebraMap F KE P.x)) < 1 := by
  have h_addX_diff_F_le : (W_smooth W).pointValuation P
      (algebraMap F KE (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk)) -
        algebraMap F KE P.x) ≤ 1 := by
    rw [← map_sub]
    exact (W_smooth W).pointValuation_algebraMap_F_le_one P
      (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk) - P.x)
  rw [mul_comm]
  exact pointValuation_mul_lt_one_of_le_and_lt W P h_addX_diff_F_le
    (pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne W P xk yk h_x)

/-- T4 (chord case): the generator difference `y_gen − alg P.y` lies in the
maximal ideal at `P` (vanishes at `P`), hence has `pointValuation < 1`. The
`y`-coordinate mirror of `pointValuation_x_gen_sub_alg_x_self_lt_one`. -/
private theorem pointValuation_y_gen_sub_alg_y_self_lt_one
    (P : (W_smooth W).SmoothPoint) :
    (W_smooth W).pointValuation P (y_gen W - algebraMap F KE P.y) < 1 := by
  have h_ymem : Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y) ∈
      (W_smooth W).maximalIdealAt P :=
    YClass_mem_maximalIdealAt W P P.y rfl
  have h_lt :=
    (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
      (C := W_smooth W) (Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y)) P).mpr h_ymem
  rw [y_gen_sub_const_eq_algebraMap_YClass W P.y]
  exact h_lt

/-- For chord-case `P` (P.x ≠ xk), the difference
`translateY_xy − alg(W.addY P.x xk P.y slope_at_P)` has `pointValuation < 1` at P.
This is the geometric content "value of τ_k(y_gen) at P equals (P+k).y"
in the chord case. -/
theorem pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_x : P.x ≠ xk) :
    (W_smooth W).pointValuation P
      (translateY_xy W xk yk -
        algebraMap F KE
          (W.toAffine.addY P.x xk P.y (W.toAffine.slope P.x xk P.y yk))) < 1 := by
  set slope_K : KE := translateSlope_xy W xk yk with hslope_K
  set slope_F : F := W.toAffine.slope P.x xk P.y yk with hslope_F
  unfold translateY_xy
  rw [← Affine.map_addY (algebraMap F KE) P.x P.y xk slope_F]
  -- Normalize: use W.map (algebraMap F KE) form throughout (= W_KE W definitionally).
  change (W_smooth W).pointValuation P
      ((W.map (algebraMap F KE)).toAffine.addY (x_gen W) (algebraMap F KE xk) (y_gen W) slope_K -
        (W.map (algebraMap F KE)).toAffine.addY (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE P.y) (algebraMap F KE slope_F)) < 1
  rw [addY_eq_unfolded_neg_negAddY (W.map (algebraMap F KE)) (x_gen W) (algebraMap F KE xk)
        (y_gen W) slope_K,
      addY_eq_unfolded_neg_negAddY (W.map (algebraMap F KE)) (algebraMap F KE P.x)
        (algebraMap F KE xk) (algebraMap F KE P.y) (algebraMap F KE slope_F)]
  rw [show (W.map (algebraMap F KE)).toAffine.addX (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE slope_F) =
        algebraMap F KE (W.toAffine.addX P.x xk slope_F) from
      Affine.map_addX (algebraMap F KE) P.x xk slope_F]
  set addX_K : KE := (W.map (algebraMap F KE)).toAffine.addX (x_gen W) (algebraMap F KE xk) slope_K
    with haddX_K
  set addX_F : F := W.toAffine.addX P.x xk slope_F with haddX_F
  -- Split the unfolded `negAddY`-difference into the four pieces T1–T4.
  rw [addY_diff_four_term_ring_identity slope_K addX_K (x_gen W) (y_gen W)
      (algebraMap F KE P.x) (algebraMap F KE P.y) (algebraMap F KE slope_F)
      (algebraMap F KE addX_F) (W.map (algebraMap F KE)).a₁ (W.map (algebraMap F KE)).a₃]
  -- Bound each piece (T1–T4) and assemble via the ultrametric inequality.
  refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_sub _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_sub _ _) (max_lt ?_ ?_)
    · refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_add _ _) (max_lt ?_ ?_)
      · calc (W_smooth W).pointValuation P
              (-((slope_K + (W.map (algebraMap F KE)).a₁) *
                  (addX_K - algebraMap F KE addX_F)))
            = (W_smooth W).pointValuation P
              ((slope_K + (W.map (algebraMap F KE)).a₁) *
                (addX_K - algebraMap F KE addX_F)) := Valuation.map_neg _ _
          _ < 1 :=
            pointValuation_slope_add_a₁_mul_translateX_diff_lt_one_of_X_ne W P xk yk h_x
      · exact pointValuation_slope_mul_x_gen_diff_lt_one_of_X_ne W P xk yk h_x
    · exact pointValuation_slope_diff_mul_alg_addX_diff_lt_one_of_X_ne W P xk yk h_x
  · exact pointValuation_y_gen_sub_alg_y_self_lt_one W P

/-- **Weierstrass factorization** in K(E): from the curve equation at
`(xk, yk)` and the generic-point equation, the K(E)-level identity
`(y_gen − alg yk) · A = (x_gen − alg xk) · B`, where `A, B` are the
explicit polynomial coefficients arising from the difference factorization.

* `A = y_gen + alg yk + a₁ · x_gen + a₃` — evaluates at `P = (xk, yk)` to
  `2yk + a₁ xk + a₃ = yk − negY xk yk = ∂_y W` (non-zero iff non-2-torsion).
* `B = x_gen² + alg xk · x_gen + alg xk² + a₂ · (x_gen + alg xk) + a₄
       − a₁ · alg yk` — evaluates at `P = (xk, yk)` to
  `3 xk² + 2 a₂ xk + a₄ − a₁ yk = -∂_x W`. -/
theorem weierstrass_factorization
    (xk yk : F) (h_eq : W.toAffine.Equation xk yk) :
    (y_gen W - algebraMap F KE yk) *
        (y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) =
    (x_gen W - algebraMap F KE xk) *
        (x_gen W ^ 2 + algebraMap F KE xk * x_gen W + algebraMap F KE xk ^ 2 +
          (W_KE W).a₂ * (x_gen W + algebraMap F KE xk) + (W_KE W).a₄ -
          (W_KE W).a₁ * algebraMap F KE yk) := by
  have h_gen : (W_KE W).toAffine.Equation (x_gen W) (y_gen W) := generic_equation W
  rw [WeierstrassCurve.Affine.equation_iff'] at h_gen
  rw [WeierstrassCurve.Affine.equation_iff'] at h_eq
  have h_eq_alg :
      (algebraMap F KE yk) ^ 2 +
        (W_KE W).a₁ * algebraMap F KE xk * algebraMap F KE yk +
        (W_KE W).a₃ * algebraMap F KE yk -
        ((algebraMap F KE xk) ^ 3 +
          (W_KE W).a₂ * (algebraMap F KE xk) ^ 2 +
          (W_KE W).a₄ * algebraMap F KE xk +
          (W_KE W).a₆) = 0 := by
    have h := congrArg (algebraMap F KE) h_eq
    rw [map_zero] at h
    change _ = (0 : KE)
    change (algebraMap F KE yk) ^ 2 +
        algebraMap F KE W.a₁ * algebraMap F KE xk * algebraMap F KE yk +
        algebraMap F KE W.a₃ * algebraMap F KE yk -
        ((algebraMap F KE xk) ^ 3 +
          algebraMap F KE W.a₂ * (algebraMap F KE xk) ^ 2 +
          algebraMap F KE W.a₄ * algebraMap F KE xk +
          algebraMap F KE W.a₆) = 0
    rw [show (algebraMap F KE) yk ^ 2 = algebraMap F KE (yk ^ 2) from
        (map_pow _ _ _).symm,
      show algebraMap F KE W.a₁ * algebraMap F KE xk = algebraMap F KE (W.a₁ * xk) from
        (map_mul _ _ _).symm,
      show algebraMap F KE (W.a₁ * xk) * algebraMap F KE yk =
          algebraMap F KE (W.a₁ * xk * yk) from (map_mul _ _ _).symm,
      show algebraMap F KE W.a₃ * algebraMap F KE yk =
          algebraMap F KE (W.a₃ * yk) from (map_mul _ _ _).symm,
      show algebraMap F KE xk ^ 3 = algebraMap F KE (xk ^ 3) from
        (map_pow _ _ _).symm,
      show algebraMap F KE xk ^ 2 = algebraMap F KE (xk ^ 2) from
        (map_pow _ _ _).symm,
      show algebraMap F KE W.a₂ * algebraMap F KE (xk ^ 2) =
          algebraMap F KE (W.a₂ * xk ^ 2) from (map_mul _ _ _).symm,
      show algebraMap F KE W.a₄ * algebraMap F KE xk =
          algebraMap F KE (W.a₄ * xk) from (map_mul _ _ _).symm,
      show algebraMap F KE (yk ^ 2) + algebraMap F KE (W.a₁ * xk * yk) =
          algebraMap F KE (yk ^ 2 + W.a₁ * xk * yk) from (map_add _ _ _).symm,
      show algebraMap F KE (yk ^ 2 + W.a₁ * xk * yk) + algebraMap F KE (W.a₃ * yk) =
          algebraMap F KE (yk ^ 2 + W.a₁ * xk * yk + W.a₃ * yk) from (map_add _ _ _).symm,
      show algebraMap F KE (xk ^ 3) + algebraMap F KE (W.a₂ * xk ^ 2) =
          algebraMap F KE (xk ^ 3 + W.a₂ * xk ^ 2) from (map_add _ _ _).symm,
      show algebraMap F KE (xk ^ 3 + W.a₂ * xk ^ 2) + algebraMap F KE (W.a₄ * xk) =
          algebraMap F KE (xk ^ 3 + W.a₂ * xk ^ 2 + W.a₄ * xk) from (map_add _ _ _).symm,
      show algebraMap F KE (xk ^ 3 + W.a₂ * xk ^ 2 + W.a₄ * xk) + algebraMap F KE W.a₆ =
          algebraMap F KE (xk ^ 3 + W.a₂ * xk ^ 2 + W.a₄ * xk + W.a₆) from (map_add _ _ _).symm,
      show algebraMap F KE (yk ^ 2 + W.a₁ * xk * yk + W.a₃ * yk) -
          algebraMap F KE (xk ^ 3 + W.a₂ * xk ^ 2 + W.a₄ * xk + W.a₆) =
        algebraMap F KE (yk ^ 2 + W.a₁ * xk * yk + W.a₃ * yk -
          (xk ^ 3 + W.a₂ * xk ^ 2 + W.a₄ * xk + W.a₆)) from (map_sub _ _ _).symm]
    rw [h]
  linear_combination h_gen - h_eq_alg

/-- In the doubling case (`P = (xk, yk)`), the factor `A` differs from the nonzero
constant `yk − negY xk yk` by `(y_gen − yk) + a₁·(x_gen − xk)` — both in `m_P` — so
`pointValuation P (A − algebraMap (yk − negY xk yk)) < 1`. -/
private theorem pointValuation_A_sub_algC_lt_one_of_doubling
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk)
    (h_a1_le : (W_smooth W).pointValuation P ((W_KE W).a₁) ≤ 1) :
    (W_smooth W).pointValuation P
      ((y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) -
        algebraMap F KE (yk - W.toAffine.negY xk yk)) < 1 := by
  have h_negY : W.toAffine.negY xk yk = -yk - W.a₁ * xk - W.a₃ := rfl
  have ha1 : (W_KE W).a₁ = algebraMap F KE W.a₁ := rfl
  have ha3 : (W_KE W).a₃ = algebraMap F KE W.a₃ := rfl
  have h_diff_eq :
      (y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) -
        algebraMap F KE (yk - W.toAffine.negY xk yk) =
      (y_gen W - algebraMap F KE yk) + (W_KE W).a₁ * (x_gen W - algebraMap F KE xk) := by
    rw [h_negY, ha1, ha3]
    push_cast
    ring
  rw [h_diff_eq]
  apply lt_of_le_of_lt (((W_smooth W).pointValuation P).map_add _ _)
  apply max_lt
  · rw [← h_eq_y]
    have h_ymem : Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y) ∈
        (W_smooth W).maximalIdealAt P :=
      YClass_mem_maximalIdealAt W P P.y rfl
    have h_lt :=
      (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
        (C := W_smooth W) (Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y))
        P).mpr h_ymem
    have h_yeq := y_gen_sub_const_eq_algebraMap_YClass W P.y
    rw [h_yeq]
    exact h_lt
  · rw [← h_eq_x]
    have h_xmem : Affine.CoordinateRing.XClass W.toAffine P.x ∈
        (W_smooth W).maximalIdealAt P :=
      XClass_mem_maximalIdealAt W P P.x rfl
    have h_lt :=
      (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
        (C := W_smooth W) (Affine.CoordinateRing.XClass W.toAffine P.x) P).mpr h_xmem
    have h_xeq := x_gen_sub_const_eq_algebraMap_XClass W P.x
    apply pointValuation_mul_lt_one_of_le_and_lt W P h_a1_le
    rw [h_xeq]
    exact h_lt

/-- Helper: at `P = (xk, yk)` with `yk ≠ negY xk yk` (non-2-tor), the K(E)
factor `A = y_gen + alg yk + a₁ · x_gen + a₃` has `pointValuation = 1` at
`P`. This is because `A` evaluates to `yk − negY xk yk ≠ 0` at `P`. -/
theorem pointValuation_A_eq_one_of_doubling
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation P
      (y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) = 1 := by
  have h_y_le : (W_smooth W).pointValuation P (y_gen W) ≤ 1 :=
    pointValuation_y_gen_le_one W P
  have h_x_le : (W_smooth W).pointValuation P (x_gen W) ≤ 1 :=
    pointValuation_x_gen_le_one W P
  have h_alg_yk_le : (W_smooth W).pointValuation P (algebraMap F KE yk) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P yk
  have h_a1_le : (W_smooth W).pointValuation P ((W_KE W).a₁) ≤ 1 := by
    change (W_smooth W).pointValuation P ((W.map (algebraMap F KE)).a₁) ≤ 1
    exact (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁
  have h_a3_le : (W_smooth W).pointValuation P ((W_KE W).a₃) ≤ 1 := by
    change (W_smooth W).pointValuation P ((W.map (algebraMap F KE)).a₃) ≤ 1
    exact (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₃
  have h_A_le : (W_smooth W).pointValuation P
      (y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) ≤ 1 := by
    apply pointValuation_add_le_one W P
    · apply pointValuation_add_le_one W P
      · exact pointValuation_add_le_one W P h_y_le h_alg_yk_le
      · exact pointValuation_mul_le_one W P h_a1_le h_x_le
    · exact h_a3_le
  have h_diff_lt :=
    pointValuation_A_sub_algC_lt_one_of_doubling W P xk yk h_eq_x h_eq_y h_a1_le
  have h_c_ne : yk - W.toAffine.negY xk yk ≠ 0 := sub_ne_zero.mpr h_not_2_tor
  have h_alg_c_eq : (W_smooth W).pointValuation P
      (algebraMap F KE (yk - W.toAffine.negY xk yk)) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P h_c_ne
  have h_eq : y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃ =
      ((y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) -
          algebraMap F KE (yk - W.toAffine.negY xk yk)) +
        algebraMap F KE (yk - W.toAffine.negY xk yk) := by ring
  rw [h_eq]
  have h_lt_strict : (W_smooth W).pointValuation P
      ((y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃) -
          algebraMap F KE (yk - W.toAffine.negY xk yk)) <
      (W_smooth W).pointValuation P
        (algebraMap F KE (yk - W.toAffine.negY xk yk)) := by
    rw [h_alg_c_eq]
    exact h_diff_lt
  exact (Valuation.map_add_eq_of_lt_right _ h_lt_strict).trans h_alg_c_eq

/-- **Tangent (doubling) case slope eval**: at `P = (xk, yk)` with
`yk ≠ negY xk yk`, the K(E) slope `translateSlope_xy` evaluates to the
tangent slope `(3 xk² + 2 a₂ xk + a₄ − a₁ yk) / (yk − negY xk yk)` in
the sense that `pV (translateSlope_xy − alg slope_F) < 1` at `P`.

This is the tangent counterpart of
`pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_X_ne`. -/
theorem pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation P
      (translateSlope_xy W xk yk -
        algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) < 1 := by
  have h_curve : W.toAffine.Equation xk yk := by
    have := P.nonsingular.1
    rw [h_eq_x, h_eq_y] at this; exact this
  set slope_F : F := W.toAffine.slope P.x xk P.y yk with hslope_F
  have h_slope_F_def :
      slope_F = (3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk) /
        (yk - W.toAffine.negY xk yk) := by
    change W.toAffine.slope P.x xk P.y yk = _
    rw [h_eq_x, h_eq_y]
    exact W.toAffine.slope_of_Y_ne rfl h_not_2_tor
  have h_slope_F_mul : slope_F * (yk - W.toAffine.negY xk yk) =
      3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk := by
    rw [h_slope_F_def, div_mul_cancel₀]
    exact sub_ne_zero.mpr h_not_2_tor
  set A_K : KE := y_gen W + algebraMap F KE yk + (W_KE W).a₁ * x_gen W + (W_KE W).a₃
    with hA_K
  set B_K : KE := x_gen W ^ 2 + algebraMap F KE xk * x_gen W + algebraMap F KE xk ^ 2 +
      (W_KE W).a₂ * (x_gen W + algebraMap F KE xk) + (W_KE W).a₄ -
      (W_KE W).a₁ * algebraMap F KE yk with hB_K
  have h_A_pV : (W_smooth W).pointValuation P A_K = 1 :=
    pointValuation_A_eq_one_of_doubling W P xk yk h_eq_x h_eq_y h_not_2_tor
  have h_A_ne : A_K ≠ 0 := by
    intro h
    rw [h] at h_A_pV
    have h_zero : (W_smooth W).pointValuation P 0 = 0 := Valuation.map_zero _
    exact zero_ne_one (h_zero.symm.trans h_A_pV)
  have h_x_ne : x_gen W - algebraMap F KE xk ≠ 0 := x_gen_sub_const_ne_zero W xk
  have h_factor : (y_gen W - algebraMap F KE yk) * A_K =
      (x_gen W - algebraMap F KE xk) * B_K :=
    weierstrass_factorization W xk yk h_curve
  have ha1 : (W_KE W).a₁ = algebraMap F KE W.a₁ := rfl
  have ha2 : (W_KE W).a₂ = algebraMap F KE W.a₂ := rfl
  have ha3 : (W_KE W).a₃ = algebraMap F KE W.a₃ := rfl
  have ha4 : (W_KE W).a₄ = algebraMap F KE W.a₄ := rfl
  have h_negY : W.toAffine.negY xk yk = -yk - W.a₁ * xk - W.a₃ := rfl
  have h_slope_F_mul_KE :
      algebraMap F KE slope_F *
        (2 * algebraMap F KE yk + algebraMap F KE W.a₁ * algebraMap F KE xk +
          algebraMap F KE W.a₃) =
      3 * (algebraMap F KE xk) ^ 2 + 2 * algebraMap F KE W.a₂ * algebraMap F KE xk +
        algebraMap F KE W.a₄ - algebraMap F KE W.a₁ * algebraMap F KE yk := by
    have h_F : slope_F * (2 * yk + W.a₁ * xk + W.a₃) =
        3 * xk ^ 2 + 2 * W.a₂ * xk + W.a₄ - W.a₁ * yk := by
      have h1 := h_slope_F_mul
      have h2 : yk - W.toAffine.negY xk yk = 2 * yk + W.a₁ * xk + W.a₃ := by
        change yk - (-yk - W.a₁ * xk - W.a₃) = _
        ring
      rw [h2] at h1
      exact h1
    have h_alg := congrArg (algebraMap F KE) h_F
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h_alg
    exact h_alg
  have h_B_minus_AS :
      B_K - A_K * algebraMap F KE slope_F =
      (x_gen W - algebraMap F KE xk) *
          ((x_gen W - algebraMap F KE xk) +
            (3 * algebraMap F KE xk + algebraMap F KE W.a₂ -
              algebraMap F KE slope_F * algebraMap F KE W.a₁)) -
        algebraMap F KE slope_F * (y_gen W - algebraMap F KE yk) := by
    rw [hB_K, hA_K, ha1, ha2, ha3, ha4]
    linear_combination -h_slope_F_mul_KE
  have h_x_sub_lt : (W_smooth W).pointValuation P
      (x_gen W - algebraMap F KE xk) < 1 := by
    rw [← h_eq_x]
    have h_xmem : Affine.CoordinateRing.XClass W.toAffine P.x ∈
        (W_smooth W).maximalIdealAt P :=
      XClass_mem_maximalIdealAt W P P.x rfl
    have h_lt :=
      (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
        (C := W_smooth W) (Affine.CoordinateRing.XClass W.toAffine P.x) P).mpr h_xmem
    have h_xeq := x_gen_sub_const_eq_algebraMap_XClass W P.x
    rw [h_xeq]; exact h_lt
  have h_y_sub_lt : (W_smooth W).pointValuation P
      (y_gen W - algebraMap F KE yk) < 1 := by
    rw [← h_eq_y]
    have h_ymem : Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y) ∈
        (W_smooth W).maximalIdealAt P :=
      YClass_mem_maximalIdealAt W P P.y rfl
    have h_lt :=
      (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
        (C := W_smooth W) (Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y))
        P).mpr h_ymem
    have h_yeq := y_gen_sub_const_eq_algebraMap_YClass W P.y
    rw [h_yeq]; exact h_lt
  have h_inner_le : (W_smooth W).pointValuation P
      ((x_gen W - algebraMap F KE xk) +
        ((3 : KE) * algebraMap F KE xk + algebraMap F KE W.a₂ -
          algebraMap F KE slope_F * algebraMap F KE W.a₁)) ≤ 1 := by
    apply pointValuation_add_le_one W P
    · exact pointValuation_sub_le_one W P (pointValuation_x_gen_le_one W P)
        ((W_smooth W).pointValuation_algebraMap_F_le_one P xk)
    · apply pointValuation_sub_le_one W P
      · apply pointValuation_add_le_one W P
        · have h3 : (3 : KE) * algebraMap F KE xk = algebraMap F KE (3 * xk) := by
            rw [_root_.map_mul, map_ofNat]
          rw [h3]
          exact (W_smooth W).pointValuation_algebraMap_F_le_one P (3 * xk)
        · exact (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₂
      · exact pointValuation_mul_le_one W P
          ((W_smooth W).pointValuation_algebraMap_F_le_one P slope_F)
          ((W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁)
  have h_BAS_lt_one : (W_smooth W).pointValuation P
      (B_K - A_K * algebraMap F KE slope_F) < 1 := by
    rw [h_B_minus_AS]
    refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_sub _ _) ?_
    apply max_lt
    · rw [mul_comm]
      exact pointValuation_mul_lt_one_of_le_and_lt W P h_inner_le h_x_sub_lt
    · exact pointValuation_mul_lt_one_of_le_and_lt W P
        ((W_smooth W).pointValuation_algebraMap_F_le_one P slope_F) h_y_sub_lt
  have h_T_A : translateSlope_xy W xk yk * A_K = B_K := by
    rw [translateSlope_xy_eq]
    field_simp
    linear_combination h_factor
  have h_diff_eq : translateSlope_xy W xk yk - algebraMap F KE slope_F =
      (B_K - A_K * algebraMap F KE slope_F) / A_K := by
    field_simp
    linear_combination h_T_A
  rw [h_diff_eq]
  calc (W_smooth W).pointValuation P
        ((B_K - A_K * algebraMap F KE slope_F) / A_K)
      = (W_smooth W).pointValuation P (B_K - A_K * algebraMap F KE slope_F) /
          (W_smooth W).pointValuation P A_K := Valuation.map_div _ _ _
    _ = (W_smooth W).pointValuation P (B_K - A_K * algebraMap F KE slope_F) / 1 := by
          rw [h_A_pV]
    _ = (W_smooth W).pointValuation P (B_K - A_K * algebraMap F KE slope_F) := div_one _
    _ < 1 := h_BAS_lt_one

/-- Tangent (doubling) bound: at `P = (xk, yk)` with `yk ≠ negY xk yk`,
`translateSlope_xy` has `pointValuation ≤ 1` at `P`. Derived from the slope
eval lemma plus the F-constant bound on `alg slope_F`. -/
theorem pointValuation_translateSlope_xy_le_one_of_doubling
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation P (translateSlope_xy W xk yk) ≤ 1 := by
  have h_eval := pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling
    W P xk yk h_eq_x h_eq_y h_not_2_tor
  have h_alg_le : (W_smooth W).pointValuation P
      (algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P _
  have h_eq : translateSlope_xy W xk yk =
      (translateSlope_xy W xk yk - algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) +
        algebraMap F KE (W.toAffine.slope P.x xk P.y yk) := by ring
  rw [h_eq]
  exact pointValuation_add_le_one W P (le_of_lt h_eval) h_alg_le

/-- Doubling-case slope factor bound: the product
`(slope_K − alg slope_F) · (slope_K + alg slope_F + a₁)` has `pointValuation < 1` at `P`,
where `slope_K = translateSlope_xy W xk yk` and `slope_F = W.slope P.x xk P.y yk`.
Tangent counterpart of `pointValuation_slope_diff_mul_sum_lt_one_of_X_ne`. -/
private theorem pointValuation_slope_diff_mul_sum_lt_one_of_doubling
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation P
      ((translateSlope_xy W xk yk - algebraMap F KE (W.toAffine.slope P.x xk P.y yk)) *
        (translateSlope_xy W xk yk + algebraMap F KE (W.toAffine.slope P.x xk P.y yk) +
          (W_KE W).a₁)) < 1 := by
  set slope_K : KE := translateSlope_xy W xk yk with hslope_K
  set slope_F : F := W.toAffine.slope P.x xk P.y yk with hslope_F
  have h_slope_diff_lt :
      (W_smooth W).pointValuation P (slope_K - algebraMap F KE slope_F) < 1 :=
    pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling W P xk yk
      h_eq_x h_eq_y h_not_2_tor
  have h_slope_K_le : (W_smooth W).pointValuation P slope_K ≤ 1 :=
    pointValuation_translateSlope_xy_le_one_of_doubling W P xk yk
      h_eq_x h_eq_y h_not_2_tor
  have h_alg_slope_F_le : (W_smooth W).pointValuation P (algebraMap F KE slope_F) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P slope_F
  have h_alg_a1_le : (W_smooth W).pointValuation P ((W_KE W).a₁) ≤ 1 := by
    change (W_smooth W).pointValuation P ((W.map (algebraMap F KE)).a₁) ≤ 1
    exact (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁
  have h_sum_le : (W_smooth W).pointValuation P
      (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) ≤ 1 :=
    pointValuation_add_le_one W P
      (pointValuation_add_le_one W P h_slope_K_le h_alg_slope_F_le)
      h_alg_a1_le
  have h_swap : (slope_K - algebraMap F KE slope_F) *
      (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) =
    (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) *
      (slope_K - algebraMap F KE slope_F) := by ring
  rw [h_swap]
  exact pointValuation_mul_lt_one_of_le_and_lt W P h_sum_le h_slope_diff_lt

/-- **Tangent (doubling) case x_gen evaluation**: at `P = (xk, yk)` with
`yk ≠ negY xk yk`, the difference `translateX_xy − alg(W.addX P.x xk slope_F)`
has `pointValuation < 1` at `P`. This is the geometric content
"`τ_k(x_gen)(P) = (P + k).x`" in the tangent/doubling case. -/
theorem pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation P
      (translateX_xy W xk yk -
        algebraMap F KE
          (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))) < 1 := by
  set slope_K : KE := translateSlope_xy W xk yk with hslope_K
  set slope_F : F := W.toAffine.slope P.x xk P.y yk with hslope_F
  unfold translateX_xy
  have h_alg_addX :
      algebraMap F KE (W.toAffine.addX P.x xk slope_F) =
        (W_KE W).toAffine.addX (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE slope_F) := by
    show (algebraMap F KE) (W.toAffine.addX P.x xk slope_F) = _
    change _ = (W.map (algebraMap F KE)).toAffine.addX _ _ _
    exact (Affine.map_addX (algebraMap F KE) P.x xk slope_F).symm
  rw [h_alg_addX]
  have h_addX_diff :
      (W_KE W).toAffine.addX (x_gen W) (algebraMap F KE xk) slope_K -
        (W_KE W).toAffine.addX (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE slope_F) =
      (slope_K - algebraMap F KE slope_F) *
        (slope_K + algebraMap F KE slope_F + (W_KE W).a₁) -
      (x_gen W - algebraMap F KE P.x) := by
    change slope_K ^ 2 + (W_KE W).a₁ * slope_K - (W_KE W).a₂ - x_gen W - algebraMap F KE xk -
        ((algebraMap F KE slope_F) ^ 2 + (W_KE W).a₁ * algebraMap F KE slope_F -
          (W_KE W).a₂ - algebraMap F KE P.x - algebraMap F KE xk) =
      _
    ring
  rw [h_addX_diff]
  refine lt_of_le_of_lt
    (((W_smooth W).pointValuation P).map_sub _ _) ?_
  apply max_lt
  · exact pointValuation_slope_diff_mul_sum_lt_one_of_doubling W P xk yk h_eq_x h_eq_y h_not_2_tor
  · exact pointValuation_x_gen_sub_alg_x_self_lt_one W P

/-- **Tangent (doubling) case y_gen evaluation**: at `P = (xk, yk)` with
`yk ≠ negY xk yk`, the difference `translateY_xy − alg(W.addY P.x xk P.y slope_F)`
has `pointValuation < 1` at `P`. This is the geometric content
"`τ_k(y_gen)(P) = (P + k).y`" in the tangent/doubling case. -/
theorem pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_eq_x : P.x = xk) (h_eq_y : P.y = yk)
    (h_not_2_tor : yk ≠ W.toAffine.negY xk yk) :
    (W_smooth W).pointValuation P
      (translateY_xy W xk yk -
        algebraMap F KE
          (W.toAffine.addY P.x xk P.y (W.toAffine.slope P.x xk P.y yk))) < 1 := by
  set slope_K : KE := translateSlope_xy W xk yk with hslope_K
  set slope_F : F := W.toAffine.slope P.x xk P.y yk with hslope_F
  unfold translateY_xy
  rw [← Affine.map_addY (algebraMap F KE) P.x P.y xk slope_F]
  change (W_smooth W).pointValuation P
      ((W.map (algebraMap F KE)).toAffine.addY (x_gen W) (algebraMap F KE xk) (y_gen W) slope_K -
        (W.map (algebraMap F KE)).toAffine.addY (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE P.y) (algebraMap F KE slope_F)) < 1
  rw [addY_eq_unfolded_neg_negAddY (W.map (algebraMap F KE)) (x_gen W) (algebraMap F KE xk)
        (y_gen W) slope_K,
      addY_eq_unfolded_neg_negAddY (W.map (algebraMap F KE)) (algebraMap F KE P.x)
        (algebraMap F KE xk) (algebraMap F KE P.y) (algebraMap F KE slope_F)]
  rw [show (W.map (algebraMap F KE)).toAffine.addX (algebraMap F KE P.x) (algebraMap F KE xk)
          (algebraMap F KE slope_F) =
        algebraMap F KE (W.toAffine.addX P.x xk slope_F) from
      Affine.map_addX (algebraMap F KE) P.x xk slope_F]
  set addX_K : KE := (W.map (algebraMap F KE)).toAffine.addX (x_gen W) (algebraMap F KE xk) slope_K
    with haddX_K
  set addX_F : F := W.toAffine.addX P.x xk slope_F with haddX_F
  have h_diff_eq :
      -(slope_K * (addX_K - x_gen W) + y_gen W) -
          (W.map (algebraMap F KE)).a₁ * addX_K - (W.map (algebraMap F KE)).a₃ -
        (-(algebraMap F KE slope_F * (algebraMap F KE addX_F - algebraMap F KE P.x) +
            algebraMap F KE P.y) -
          (W.map (algebraMap F KE)).a₁ * algebraMap F KE addX_F -
          (W.map (algebraMap F KE)).a₃) =
      -((slope_K + (W.map (algebraMap F KE)).a₁) *
          (addX_K - algebraMap F KE addX_F)) +
        slope_K * (x_gen W - algebraMap F KE P.x) -
        (slope_K - algebraMap F KE slope_F) *
          (algebraMap F KE addX_F - algebraMap F KE P.x) -
        (y_gen W - algebraMap F KE P.y) := by
    ring
  rw [h_diff_eq]
  have h_T1 : (W_smooth W).pointValuation P
      ((slope_K + (W.map (algebraMap F KE)).a₁) *
        (addX_K - algebraMap F KE addX_F)) < 1 := by
    have h_factor1_le : (W_smooth W).pointValuation P
        (slope_K + (W.map (algebraMap F KE)).a₁) ≤ 1 := by
      apply pointValuation_add_le_one W P
      · exact pointValuation_translateSlope_xy_le_one_of_doubling W P xk yk
          h_eq_x h_eq_y h_not_2_tor
      · exact (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁
    have h_diff_addX_lt : (W_smooth W).pointValuation P
        (addX_K - algebraMap F KE addX_F) < 1 := by
      change (W_smooth W).pointValuation P
        (translateX_xy W xk yk - algebraMap F KE (W.toAffine.addX P.x xk slope_F)) < 1
      exact pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling W P xk yk
        h_eq_x h_eq_y h_not_2_tor
    exact pointValuation_mul_lt_one_of_le_and_lt W P h_factor1_le h_diff_addX_lt
  have h_T2 : (W_smooth W).pointValuation P
      (slope_K * (x_gen W - algebraMap F KE P.x)) < 1 := by
    have h_slope_K_le : (W_smooth W).pointValuation P slope_K ≤ 1 :=
      pointValuation_translateSlope_xy_le_one_of_doubling W P xk yk
        h_eq_x h_eq_y h_not_2_tor
    have h_xgen_diff_lt : (W_smooth W).pointValuation P
        (x_gen W - algebraMap F KE P.x) < 1 := by
      have h_xmem : Affine.CoordinateRing.XClass W.toAffine P.x ∈
          (W_smooth W).maximalIdealAt P :=
        XClass_mem_maximalIdealAt W P P.x rfl
      have h_lt :=
        (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
          (C := W_smooth W) (Affine.CoordinateRing.XClass W.toAffine P.x) P).mpr h_xmem
      have h_eq := x_gen_sub_const_eq_algebraMap_XClass W P.x
      rw [h_eq]
      exact h_lt
    exact pointValuation_mul_lt_one_of_le_and_lt W P h_slope_K_le h_xgen_diff_lt
  have h_T3 : (W_smooth W).pointValuation P
      ((slope_K - algebraMap F KE slope_F) *
        (algebraMap F KE addX_F - algebraMap F KE P.x)) < 1 := by
    have h_slope_diff_lt : (W_smooth W).pointValuation P
        (slope_K - algebraMap F KE slope_F) < 1 :=
      pointValuation_translateSlope_xy_sub_alg_slope_lt_one_of_doubling W P xk yk
        h_eq_x h_eq_y h_not_2_tor
    have h_addX_diff_F_le : (W_smooth W).pointValuation P
        (algebraMap F KE addX_F - algebraMap F KE P.x) ≤ 1 := by
      rw [← map_sub]
      exact (W_smooth W).pointValuation_algebraMap_F_le_one P (addX_F - P.x)
    have h_swap : (slope_K - algebraMap F KE slope_F) *
        (algebraMap F KE addX_F - algebraMap F KE P.x) =
        (algebraMap F KE addX_F - algebraMap F KE P.x) *
        (slope_K - algebraMap F KE slope_F) := by ring
    rw [h_swap]
    exact pointValuation_mul_lt_one_of_le_and_lt W P h_addX_diff_F_le h_slope_diff_lt
  have h_T4 : (W_smooth W).pointValuation P
      (y_gen W - algebraMap F KE P.y) < 1 := by
    have h_ymem : Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y) ∈
        (W_smooth W).maximalIdealAt P :=
      YClass_mem_maximalIdealAt W P P.y rfl
    have h_lt :=
      (Curves.SmoothPlaneCurve.pointValuation_algebraMap_lt_one_iff_mem_maximalIdealAt
        (C := W_smooth W) (Affine.CoordinateRing.YClass W.toAffine (Polynomial.C P.y))
        P).mpr h_ymem
    have h_eq := y_gen_sub_const_eq_algebraMap_YClass W P.y
    rw [h_eq]
    exact h_lt
  refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_sub _ _) ?_
  apply max_lt
  · refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_sub _ _) ?_
    apply max_lt
    · refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_add _ _) ?_
      apply max_lt
      · calc (W_smooth W).pointValuation P
              (-((slope_K + (W.map (algebraMap F KE)).a₁) *
                  (addX_K - algebraMap F KE addX_F)))
            = (W_smooth W).pointValuation P
              ((slope_K + (W.map (algebraMap F KE)).a₁) *
                (addX_K - algebraMap F KE addX_F)) := Valuation.map_neg _ _
          _ < 1 := h_T1
      · exact h_T2
    · exact h_T3
  · exact h_T4

/-- Helper: `τ_k(x_gen) = translateX_xy W xk yk` for any non-zero `k`,
regardless of 2-tor status (uniform case-dispatch on
`translateAlgEquivOfPoint`). -/
theorem translateAlgEquivOfPoint_apply_x_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (x_gen W) =
      translateX_xy W xk yk := by
  by_cases h_2_tor : yk = W.toAffine.negY xk yk
  · rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h_2_tor]
    change (translateAlgHom_of_2tor W xk yk h_ns h_2_tor).toFun (x_gen W) = _
    exact translateAlgHom_of_2tor_apply_x_gen W xk yk h_ns h_2_tor
  · rw [translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h_2_tor]
    change (translateAlgHom_of_nonTorsion W xk yk h_ns h_2_tor).toFun (x_gen W) = _
    exact translateAlgHom_apply_x_gen W xk yk h_ns h_2_tor

/-- Helper: `τ_k(y_gen) = translateY_xy W xk yk` for any non-zero `k`,
regardless of 2-tor status. -/
theorem translateAlgEquivOfPoint_apply_y_gen
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk) :
    translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (y_gen W) =
      translateY_xy W xk yk := by
  by_cases h_2_tor : yk = W.toAffine.negY xk yk
  · rw [translateAlgEquivOfPoint_some_2tor W xk yk h_ns h_2_tor]
    change (translateAlgHom_of_2tor W xk yk h_ns h_2_tor).toFun (y_gen W) = _
    exact translateAlgHom_of_2tor_apply_y_gen W xk yk h_ns h_2_tor
  · rw [translateAlgEquivOfPoint_some_nonTor W xk yk h_ns h_2_tor]
    change (translateAlgHom_of_nonTorsion W xk yk h_ns h_2_tor).toFun (y_gen W) = _
    exact translateAlgHom_apply_y_gen W xk yk h_ns h_2_tor

instance W_smooth_toAffine_isElliptic : (W_smooth W).toAffine.IsElliptic :=
  inferInstanceAs W.toAffine.IsElliptic

/-- If `P + (xk, yk)` is a finite point, then `P` is not the negation of `(xk, yk)`,
i.e. `(P.x, P.y) ≠ (xk, negY xk yk)`. (If it were, the sum would be the point at
infinity, contradicting `IsSome`.) -/
private theorem not_eq_negY_pair_of_add_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    ¬(P.x = xk ∧ P.y = W.toAffine.negY xk yk) := by
  intro ⟨h_x_eq, h_y_eq⟩
  have h_zero : P.toAffinePoint +
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) = 0 := by
    change Affine.Point.some P.x P.y P.nonsingular +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) = 0
    exact Affine.Point.add_of_Y_eq h_x_eq h_y_eq
  exact Affine.Point.zero_not_isSome (h_zero ▸ h)

/-- In the equal-`x` branch of an addition with `(P.x, P.y) ≠ (xk, negY xk yk)`,
the point is genuinely being doubled: `P.y = yk` and `yk ≠ negY xk yk`. -/
private theorem yk_ne_negY_and_eq_of_x_eq
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_zero_pair : ¬(P.x = xk ∧ P.y = W.toAffine.negY xk yk)) (h_xeq : P.x = xk) :
    P.y = yk ∧ yk ≠ W.toAffine.negY xk yk := by
  have h_y_ne_negY : P.y ≠ W.toAffine.negY xk yk := fun h_yeq ↦
    h_not_zero_pair ⟨h_xeq, h_yeq⟩
  have h_yeq : P.y = yk :=
    W.toAffine.Y_eq_of_Y_ne P.nonsingular.1 h_ns.1 h_xeq h_y_ne_negY
  exact ⟨h_yeq, h_yeq ▸ h_y_ne_negY⟩

/-- The `x_gen` half of `isTranslateXY_evaluatesAt_some`: dispatches the
equal-`x` (doubling) and distinct-`x` (chord) cases of the `addX` valuation bound. -/
private theorem pointValuation_translateX_xy_sub_alg_addX_lt_one_of_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_zero_pair : ¬(P.x = xk ∧ P.y = W.toAffine.negY xk yk)) :
    (W_smooth W).pointValuation P
      (translateX_xy W xk yk -
        algebraMap F KE
          (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))) < 1 := by
  by_cases h_xeq : P.x = xk
  · obtain ⟨h_yeq, h_not_2_tor⟩ :=
      yk_ne_negY_and_eq_of_x_eq W P xk yk h_ns h_not_zero_pair h_xeq
    exact pointValuation_translateX_xy_sub_alg_addX_lt_one_of_doubling W P xk yk
      h_xeq h_yeq h_not_2_tor
  · exact pointValuation_translateX_xy_sub_alg_addX_lt_one_of_X_ne W P xk yk h_xeq

/-- The `y_gen` half of `isTranslateXY_evaluatesAt_some`: dispatches the
equal-`x` (doubling) and distinct-`x` (chord) cases of the `addY` valuation bound. -/
private theorem pointValuation_translateY_xy_sub_alg_addY_lt_one_of_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_not_zero_pair : ¬(P.x = xk ∧ P.y = W.toAffine.negY xk yk)) :
    (W_smooth W).pointValuation P
      (translateY_xy W xk yk -
        algebraMap F KE
          (W.toAffine.addY P.x xk P.y (W.toAffine.slope P.x xk P.y yk))) < 1 := by
  by_cases h_xeq : P.x = xk
  · obtain ⟨h_yeq, h_not_2_tor⟩ :=
      yk_ne_negY_and_eq_of_x_eq W P xk yk h_ns h_not_zero_pair h_xeq
    exact pointValuation_translateY_xy_sub_alg_addY_lt_one_of_doubling W P xk yk
      h_xeq h_yeq h_not_2_tor
  · exact pointValuation_translateY_xy_sub_alg_addY_lt_one_of_X_ne W P xk yk h_xeq

/-- **Composition**: `IsTranslateXY_evaluatesAt` for non-zero `k`,
unifying the chord and tangent discharges. -/
theorem isTranslateXY_evaluatesAt_some
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    IsTranslateXY_evaluatesAt W P
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) h := by
  set k : (W_smooth W).toAffine.Point :=
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) with hk_def
  have h_not_zero_pair : ¬(P.x = xk ∧ P.y = W.toAffine.negY xk yk) :=
    not_eq_negY_pair_of_add_isSome W P xk yk h_ns h
  have hsum :
      P.toAffinePoint + k =
        (Affine.Point.some (W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk))
          (W.toAffine.addY P.x xk P.y (W.toAffine.slope P.x xk P.y yk))
          (W.toAffine.nonsingular_add P.nonsingular h_ns h_not_zero_pair)
            : (W_smooth W).toAffine.Point) := by
    change Affine.Point.some P.x P.y P.nonsingular +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) = _
    exact Affine.Point.add_some h_not_zero_pair
  have h_PK_x :
      (P.translate_of_finite k h).x =
        W.toAffine.addX P.x xk (W.toAffine.slope P.x xk P.y yk) :=
    Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_x P _ h hsum
  have h_PK_y :
      (P.translate_of_finite k h).y =
        W.toAffine.addY P.x xk P.y (W.toAffine.slope P.x xk P.y yk) :=
    Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_y P _ h hsum
  have h_tau_x : translateAlgEquivOfPoint W k (x_gen W) = translateX_xy W xk yk := by
    change translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (x_gen W) = _
    exact translateAlgEquivOfPoint_apply_x_gen W xk yk h_ns
  have h_tau_y : translateAlgEquivOfPoint W k (y_gen W) = translateY_xy W xk yk := by
    change translateAlgEquivOfPoint W (Affine.Point.some xk yk h_ns) (y_gen W) = _
    exact translateAlgEquivOfPoint_apply_y_gen W xk yk h_ns
  refine ⟨?_, ?_⟩
  · rw [h_tau_x, h_PK_x]
    exact pointValuation_translateX_xy_sub_alg_addX_lt_one_of_isSome W P xk yk h_ns
      h_not_zero_pair
  · rw [h_tau_y, h_PK_y]
    exact pointValuation_translateY_xy_sub_alg_addY_lt_one_of_isSome W P xk yk h_ns
      h_not_zero_pair

/-- **Unified slope bound**: for any P and non-zero `k = (xk, yk)` with
`(P + k).IsSome`, `pV(translateSlope_xy W xk yk) ≤ 1` at `P`. -/
theorem pointValuation_translateSlope_xy_le_one_of_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    (W_smooth W).pointValuation P (translateSlope_xy W xk yk) ≤ 1 := by
  have h_not_zero_pair : ¬(P.x = xk ∧ P.y = W.toAffine.negY xk yk) := by
    intro ⟨h_x_eq, h_y_eq⟩
    have h_zero : P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) = 0 := by
      change Affine.Point.some P.x P.y P.nonsingular +
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) = 0
      exact Affine.Point.add_of_Y_eq h_x_eq h_y_eq
    exact Affine.Point.zero_not_isSome (h_zero ▸ h)
  by_cases h_xeq : P.x = xk
  · have h_y_ne_negY : P.y ≠ W.toAffine.negY xk yk := fun h_yeq ↦
      h_not_zero_pair ⟨h_xeq, h_yeq⟩
    have h_yeq : P.y = yk :=
      W.toAffine.Y_eq_of_Y_ne P.nonsingular.1 h_ns.1 h_xeq h_y_ne_negY
    have h_not_2_tor : yk ≠ W.toAffine.negY xk yk := h_yeq ▸ h_y_ne_negY
    exact pointValuation_translateSlope_xy_le_one_of_doubling W P xk yk
      h_xeq h_yeq h_not_2_tor
  · exact pointValuation_translateSlope_xy_le_one_of_X_ne W P xk yk h_xeq

/-- `pV(translateX_xy) ≤ 1` at `P` when `(P + k).IsSome`. Used in
polynomial-induction lifting of `IsTranslateXY_evaluatesAt`. -/
theorem pointValuation_translateX_xy_le_one_of_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    (W_smooth W).pointValuation P (translateX_xy W xk yk) ≤ 1 := by
  unfold translateX_xy
  change (W_smooth W).pointValuation P
    ((translateSlope_xy W xk yk) ^ 2 + (W_KE W).a₁ * translateSlope_xy W xk yk -
      (W_KE W).a₂ - x_gen W - algebraMap F KE xk) ≤ 1
  have h_slope_le := pointValuation_translateSlope_xy_le_one_of_isSome W P xk yk h_ns h
  have h_a1_le : (W_smooth W).pointValuation P ((W_KE W).a₁) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁
  have h_a2_le : (W_smooth W).pointValuation P ((W_KE W).a₂) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₂
  have h_xgen_le := pointValuation_x_gen_le_one W P
  have h_alg_xk_le : (W_smooth W).pointValuation P (algebraMap F KE xk) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P xk
  apply pointValuation_sub_le_one W P
  · apply pointValuation_sub_le_one W P
    · apply pointValuation_sub_le_one W P
      · apply pointValuation_add_le_one W P
        · exact pointValuation_pow_le_one W P h_slope_le 2
        · exact pointValuation_mul_le_one W P h_a1_le h_slope_le
      · exact h_a2_le
    · exact h_xgen_le
  · exact h_alg_xk_le

/-- `pV(translateY_xy) ≤ 1` at `P` when `(P + k).IsSome`. Companion to
`pointValuation_translateX_xy_le_one_of_isSome`. -/
theorem pointValuation_translateY_xy_le_one_of_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    (W_smooth W).pointValuation P (translateY_xy W xk yk) ≤ 1 := by
  rw [show translateY_xy W xk yk =
      -(translateSlope_xy W xk yk *
          (translateX_xy W xk yk - x_gen W) + y_gen W) -
        (W_KE W).a₁ * translateX_xy W xk yk - (W_KE W).a₃ from by
    change (W_KE W).toAffine.addY (x_gen W) (algebraMap F KE xk) (y_gen W)
        (translateSlope_xy W xk yk) = _
    exact addY_eq_unfolded_neg_negAddY (W_KE W) (x_gen W) (algebraMap F KE xk)
      (y_gen W) (translateSlope_xy W xk yk)]
  have h_slope_le := pointValuation_translateSlope_xy_le_one_of_isSome W P xk yk h_ns h
  have h_addX_le := pointValuation_translateX_xy_le_one_of_isSome W P xk yk h_ns h
  have h_a1_le : (W_smooth W).pointValuation P ((W_KE W).a₁) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₁
  have h_a3_le : (W_smooth W).pointValuation P ((W_KE W).a₃) ≤ 1 :=
    (W_smooth W).pointValuation_algebraMap_F_le_one P W.a₃
  have h_xgen_le := pointValuation_x_gen_le_one W P
  have h_ygen_le := pointValuation_y_gen_le_one W P
  apply pointValuation_sub_le_one W P
  · apply pointValuation_sub_le_one W P
    · apply pointValuation_neg_le_one W P
      apply pointValuation_add_le_one W P
      · apply pointValuation_mul_le_one W P h_slope_le
        exact pointValuation_sub_le_one W P h_addX_le h_xgen_le
      · exact h_ygen_le
    · exact pointValuation_mul_le_one W P h_a1_le h_addX_le
  · exact h_a3_le

open Polynomial in
/-- **Constant-coefficient leaf.** For `c : F`, the τ_k-image of the constant
coordinate-ring element `of (C c)` has point-valuation `≤ 1` at `P`: since `τ_k`
is an `F`-algebra map it fixes `algebraMap F KE c`, whose valuation is `≤ 1` by
`pointValuation_algebraMap_F_le_one`. (Leaf of the inner coefficient induction in
`pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome`.) -/
private theorem pointValuation_translateAlgEquivOfPoint_of_C_le_one
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (c : F) :
    (W_smooth W).pointValuation P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c)))) ≤ 1 := by
  have h_const :
      (AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c) =
      algebraMap F (W_smooth W).CoordinateRing c :=
    (IsScalarTower.algebraMap_apply F F[X] (W_smooth W).CoordinateRing c).symm
  rw [h_const, ← IsScalarTower.algebraMap_apply F
    (W_smooth W).CoordinateRing (W_smooth W).FunctionField c]
  change (W_smooth W).pointValuation P
    ((translateAlgEquivOfPoint W
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
      (algebraMap F W.toAffine.FunctionField c)) ≤ 1
  rw [(translateAlgEquivOfPoint W
    (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).commutes c]
  exact (W_smooth W).pointValuation_algebraMap_F_le_one P c

/-- **`x`-generator power leaf.** For `m : ℕ`, the `m`-th power of the τ_k-image
of the `x`-generator `of X` has point-valuation `≤ 1` at `P`: the generator maps
to `translateX_xy`, whose valuation is `≤ 1` by
`pointValuation_translateX_xy_le_one_of_isSome`, and powers preserve `≤ 1`.
(Leaf of the inner coefficient induction.) -/
private theorem pointValuation_translateAlgEquivOfPoint_of_X_pow_le_one
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (m : ℕ) :
    (W_smooth W).pointValuation P
      (((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X))) ^ m) ≤ 1 := by
  have h_tau_x : translateAlgEquivOfPoint W
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) (x_gen W) =
      translateX_xy W xk yk :=
    translateAlgEquivOfPoint_apply_x_gen W xk yk h_ns
  have h_tx_le := pointValuation_translateX_xy_le_one_of_isSome W P xk yk h_ns h
  have h_X_to_x_gen :
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
        ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X) =
      x_gen W := rfl
  rw [h_X_to_x_gen, h_tau_x]
  exact pointValuation_pow_le_one W P h_tx_le m

open Polynomial in
/-- **Coefficient lift.** For any `a : F[X]`, the τ_k-image of the
coordinate-ring element `of a` has point-valuation `≤ 1` at `P`. Polynomial
induction on `a`: the sum case is additivity (`pointValuation_add_le_one`), and a
monomial `C c * X^m` splits into the constant and `x`-power leaves
(`pointValuation_translateAlgEquivOfPoint_of_C_le_one` /
`..._of_X_pow_le_one`) combined by `pointValuation_mul_le_one`. -/
private theorem pointValuation_translateAlgEquivOfPoint_of_le_one
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (a : F[X]) :
    (W_smooth W).pointValuation P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) a))) ≤ 1 := by
  induction a using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [show (AdjoinRoot.of (W_smooth W).toAffine.polynomial) (p + q) =
          (AdjoinRoot.of (W_smooth W).toAffine.polynomial) p +
          (AdjoinRoot.of (W_smooth W).toAffine.polynomial) q from map_add _ _ _,
      show (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) p +
            (AdjoinRoot.of (W_smooth W).toAffine.polynomial) q) =
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) p) +
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) q) from map_add _ _ _,
      show (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) p) +
          (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) q)) =
        (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) p)) +
        (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) q)) from map_add _ _ _]
    exact pointValuation_add_le_one W P hp hq
  | monomial m c =>
    rw [show (Polynomial.monomial m c : F[X]) = Polynomial.C c * Polynomial.X ^ m
      from (Polynomial.C_mul_X_pow_eq_monomial).symm]
    rw [show (AdjoinRoot.of (W_smooth W).toAffine.polynomial)
          (Polynomial.C c * Polynomial.X ^ m) =
        (AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c) *
        (AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.X ^ m) from
      map_mul _ _ _]
    rw [show (AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.X ^ m) =
        ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X) ^ m from
      map_pow _ _ _]
    rw [show (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c) *
            (AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X ^ m) =
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c)) *
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X) ^ m from by
      rw [map_mul, map_pow]]
    rw [show (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c)) *
          (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X) ^ m) =
        (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c))) *
        ((translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X))) ^ m from by
      rw [show
          (translateAlgEquivOfPoint W
              (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
                ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c)) *
              (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
                  ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X) ^ m) =
          (translateAlgEquivOfPoint W
              (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) (Polynomial.C c))) *
          (translateAlgEquivOfPoint W
              (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
                ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X) ^ m) from
        map_mul _ _ _]
      rw [show
          (translateAlgEquivOfPoint W
              (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
                ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X) ^ m) =
          ((translateAlgEquivOfPoint W
              (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
                ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) Polynomial.X))) ^ m from
        map_pow _ _ _]]
    exact pointValuation_mul_le_one W P
      (pointValuation_translateAlgEquivOfPoint_of_C_le_one W P xk yk h_ns h c)
      (pointValuation_translateAlgEquivOfPoint_of_X_pow_le_one W P xk yk h_ns h m)

/-- **`y`-generator power leaf.** For `n : ℕ`, the `n`-th power of the τ_k-image
of the `y`-generator `root` has point-valuation `≤ 1` at `P`: the generator maps
to `translateY_xy`, whose valuation is `≤ 1` by
`pointValuation_translateY_xy_le_one_of_isSome`, and powers preserve `≤ 1`. -/
private theorem pointValuation_translateAlgEquivOfPoint_root_pow_le_one
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (n : ℕ) :
    (W_smooth W).pointValuation P
      (((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          (AdjoinRoot.root (W_smooth W).toAffine.polynomial))) ^ n) ≤ 1 := by
  have h_tau_y : translateAlgEquivOfPoint W
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) (y_gen W) =
      translateY_xy W xk yk :=
    translateAlgEquivOfPoint_apply_y_gen W xk yk h_ns
  have h_ty_le := pointValuation_translateY_xy_le_one_of_isSome W P xk yk h_ns h
  rw [show (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
        (AdjoinRoot.root (W_smooth W).toAffine.polynomial) = y_gen W from rfl, h_tau_y]
  exact pointValuation_pow_le_one W P h_ty_le n

open Polynomial in
/-- **Monomial lift.** For `n : ℕ` and `a : F[X]`, the τ_k-image of the
coordinate-ring element `mk (C a * X^n)` (i.e. `of a * root^n`) has
point-valuation `≤ 1` at `P`. The product splits via `pointValuation_mul_le_one`
into the coefficient lift (`pointValuation_translateAlgEquivOfPoint_of_le_one`)
and the `y`-power leaf (`..._root_pow_le_one`). (Leaf of the outer bivariate
induction.) -/
private theorem pointValuation_translateAlgEquivOfPoint_mk_monomial_le_one
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (n : ℕ) (a : F[X]) :
    (W_smooth W).pointValuation P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          (AdjoinRoot.mk (W_smooth W).toAffine.polynomial
            (Polynomial.C a * Polynomial.X ^ n)))) ≤ 1 := by
  rw [show AdjoinRoot.mk (W_smooth W).toAffine.polynomial
        (Polynomial.C a * Polynomial.X ^ n) =
      (AdjoinRoot.of (W_smooth W).toAffine.polynomial) a *
        (AdjoinRoot.root (W_smooth W).toAffine.polynomial) ^ n from by
    rw [map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]]
  rw [show (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
        ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) a *
          (AdjoinRoot.root (W_smooth W).toAffine.polynomial) ^ n) =
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) a) *
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            (AdjoinRoot.root (W_smooth W).toAffine.polynomial) ^ n from by
    rw [map_mul, map_pow]]
  rw [show (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) a) *
          (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.root (W_smooth W).toAffine.polynomial) ^ n) =
        (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            ((AdjoinRoot.of (W_smooth W).toAffine.polynomial) a)) *
        (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.root (W_smooth W).toAffine.polynomial) ^ n) from
      map_mul _ _ _]
  rw [show (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.root (W_smooth W).toAffine.polynomial) ^ n) =
        ((translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.root (W_smooth W).toAffine.polynomial))) ^ n from
      map_pow _ _ _]
  exact pointValuation_mul_le_one W P
    (pointValuation_translateAlgEquivOfPoint_of_le_one W P xk yk h_ns h a)
    (pointValuation_translateAlgEquivOfPoint_root_pow_le_one W P xk yk h_ns h n)

open Polynomial in
/-- **Polynomial induction lift**: for any `r ∈ CoordinateRing` and non-zero
`k = (xk, yk)` with `(P + k).IsSome`, `pV(τ_k(algMap r)) ≤ 1` at `P`. -/
theorem pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (r : (W_smooth W).CoordinateRing) :
    (W_smooth W).pointValuation P
      (translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField r)) ≤ 1 := by
  -- Bivariate induction on `r = mk p`, `p : F[X][X]`: the addition cases are
  -- discharged by additivity of the point-valuation, and each monomial leaf
  -- `mk (C a * X^n)` by `pointValuation_translateAlgEquivOfPoint_mk_monomial_le_one`.
  induction r using AdjoinRoot.induction_on with | _ p => ?_
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [show AdjoinRoot.mk (W_smooth W).toAffine.polynomial (p + q) =
            AdjoinRoot.mk (W_smooth W).toAffine.polynomial p +
            AdjoinRoot.mk (W_smooth W).toAffine.polynomial q from map_add _ _ _,
      show (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            (AdjoinRoot.mk (W_smooth W).toAffine.polynomial p +
              AdjoinRoot.mk (W_smooth W).toAffine.polynomial q) =
          (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            (AdjoinRoot.mk (W_smooth W).toAffine.polynomial p) +
          (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            (AdjoinRoot.mk (W_smooth W).toAffine.polynomial q) from map_add _ _ _,
      show (translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.mk (W_smooth W).toAffine.polynomial p) +
            (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.mk (W_smooth W).toAffine.polynomial q)) =
          (translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.mk (W_smooth W).toAffine.polynomial p)) +
          (translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              (AdjoinRoot.mk (W_smooth W).toAffine.polynomial q)) from map_add _ _ _]
    exact pointValuation_add_le_one W P hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    exact pointValuation_translateAlgEquivOfPoint_mk_monomial_le_one W P xk yk h_ns h n a

/-- **Linearisation of `τ_k` on the two-generator combination.** For
`a b : CoordinateRing`, the image under `τ_k ∘ algebraMap` of the linear
combination `a · XClass xPK + b · YClass (C yPK)` of the two generators of the
maximal ideal at `P + k` splits as a sum of two products, with the generator
images normalised to `τ_k x_gen − algMap xPK` and `τ_k y_gen − algMap yPK`.
Pure `algebraMap`/`AlgEquiv` linearity (`map_add`/`map_mul`/`map_sub` plus
`AlgEquiv.commutes` for the constant terms), with the generator–class identities
`x_gen_sub_const_eq_algebraMap_XClass` / `y_gen_sub_const_eq_algebraMap_YClass`. -/
private theorem translateAlgEquivOfPoint_algebraMap_XClass_add_YClass_some
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (a b : (W_smooth W).CoordinateRing) :
    (translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
          (a * Affine.CoordinateRing.XClass (W_smooth W).toAffine
              (P.translate_of_finite (Affine.Point.some xk yk h_ns :
                (W_smooth W).toAffine.Point) h).x +
            b * Affine.CoordinateRing.YClass (W_smooth W).toAffine
              (Polynomial.C (P.translate_of_finite (Affine.Point.some xk yk h_ns :
                (W_smooth W).toAffine.Point) h).y))) =
      (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) a) *
        ((translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) (x_gen W) -
          algebraMap F W.toAffine.FunctionField
            (P.translate_of_finite (Affine.Point.some xk yk h_ns :
              (W_smooth W).toAffine.Point) h).x) +
      (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
          ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) b) *
        ((translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) (y_gen W) -
          algebraMap F W.toAffine.FunctionField
            (P.translate_of_finite (Affine.Point.some xk yk h_ns :
              (W_smooth W).toAffine.Point) h).y) := by
  rw [map_add, map_mul, map_mul]
  change (translateAlgEquivOfPoint W
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
      ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) a *
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
            (Affine.CoordinateRing.XClass W.toAffine
              (P.translate_of_finite (Affine.Point.some xk yk h_ns :
                (W_smooth W).toAffine.Point) h).x) +
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) b *
          (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField)
            (Affine.CoordinateRing.YClass W.toAffine
              (Polynomial.C (P.translate_of_finite (Affine.Point.some xk yk h_ns :
                (W_smooth W).toAffine.Point) h).y))) = _
  rw [← x_gen_sub_const_eq_algebraMap_XClass W
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h).x,
    ← y_gen_sub_const_eq_algebraMap_YClass W
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h).y,
    map_add, map_mul, map_mul, map_sub, map_sub,
    (translateAlgEquivOfPoint W
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).commutes,
    (translateAlgEquivOfPoint W
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).commutes]

/-- **Value bound on the two-generator combination.** For
`a b : CoordinateRing`, the point-valuation at `P` of `τ_k` applied to the
normalised combination `τ_k(algMap a)·(τ_k x_gen − algMap xPK) +
τ_k(algMap b)·(τ_k y_gen − algMap yPK)` is `< 1`, given the
`IsTranslateXY_evaluatesAt` bounds `h_xy_x`/`h_xy_y` on the two generator
differences. Triangle inequality (`Valuation.map_add` + `max_lt`) and the
product bound `pointValuation_mul_lt_one_of_le_and_lt`, using the global lift
`pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome` for the
two scalar factors. -/
private theorem pointValuation_translateAlgEquivOfPoint_XClass_add_YClass_lt_one_some
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (a b : (W_smooth W).CoordinateRing)
    (h_xy_x : (W_smooth W).pointValuation P
        ((translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) (x_gen W) -
          algebraMap F W.toAffine.FunctionField
            (P.translate_of_finite (Affine.Point.some xk yk h_ns :
              (W_smooth W).toAffine.Point) h).x) < 1)
    (h_xy_y : (W_smooth W).pointValuation P
        ((translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) (y_gen W) -
          algebraMap F W.toAffine.FunctionField
            (P.translate_of_finite (Affine.Point.some xk yk h_ns :
              (W_smooth W).toAffine.Point) h).y) < 1) :
    (W_smooth W).pointValuation P
        ((translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) a) *
          ((translateAlgEquivOfPoint W
              (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) (x_gen W) -
            algebraMap F W.toAffine.FunctionField
              (P.translate_of_finite (Affine.Point.some xk yk h_ns :
                (W_smooth W).toAffine.Point) h).x) +
        (translateAlgEquivOfPoint W
            (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
            ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) b) *
          ((translateAlgEquivOfPoint W
              (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) (y_gen W) -
            algebraMap F W.toAffine.FunctionField
              (P.translate_of_finite (Affine.Point.some xk yk h_ns :
                (W_smooth W).toAffine.Point) h).y)) < 1 := by
  refine lt_of_le_of_lt (((W_smooth W).pointValuation P).map_add _ _) ?_
  apply max_lt
  · apply pointValuation_mul_lt_one_of_le_and_lt W P
    · exact pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome
        W P xk yk h_ns h a
    · exact h_xy_x
  · apply pointValuation_mul_lt_one_of_le_and_lt W P
    · exact pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome
        W P xk yk h_ns h b
    · exact h_xy_y

/-- `IsTranslateMaxIdealCompatible_on_CoordinateRing` for non-zero `k`: for
`r ∈ maxIdealAt(P + k)` in the coordinate ring, `pV P (τ_k (algMap r)) < 1`. -/
theorem isTranslateMaxIdealCompatible_on_CoordinateRing_some
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    IsTranslateMaxIdealCompatible_on_CoordinateRing W P
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) h := by
  obtain ⟨h_xy_x, h_xy_y⟩ := isTranslateXY_evaluatesAt_some W P xk yk h_ns h
  intro r h_mem
  have h_mem' : r ∈ Ideal.span ({Affine.CoordinateRing.XClass (W_smooth W).toAffine
        (P.translate_of_finite (Affine.Point.some xk yk h_ns :
          (W_smooth W).toAffine.Point) h).x,
      Affine.CoordinateRing.YClass (W_smooth W).toAffine
        (Polynomial.C (P.translate_of_finite (Affine.Point.some xk yk h_ns :
          (W_smooth W).toAffine.Point) h).y)} :
      Set (W_smooth W).CoordinateRing) := h_mem
  rw [Ideal.mem_span_pair] at h_mem'
  obtain ⟨a, b, hab⟩ := h_mem'
  show (W_smooth W).pointValuation P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField) r)) < 1
  rw [← hab,
    translateAlgEquivOfPoint_algebraMap_XClass_add_YClass_some W P xk yk h_ns h a b]
  exact pointValuation_translateAlgEquivOfPoint_XClass_add_YClass_lt_one_some
    W P xk yk h_ns h a b h_xy_x h_xy_y

/-- If `r ∉ maximalIdealAt P'`, then its evaluation `evalAt P' r` is a nonzero
constant. Immediate from `ker_evalAt`: the maximal ideal is exactly the kernel
of evaluation, so an element outside it has nonzero value. -/
private theorem evalAt_ne_zero_of_notMem_maximalIdealAt
    (P' : (W_smooth W).SmoothPoint) (r : (W_smooth W).CoordinateRing)
    (h_notMem : r ∉ (W_smooth W).maximalIdealAt P') :
    (W_smooth W).evalAt P' r ≠ 0 := by
  intro h_c
  apply h_notMem
  rw [← (W_smooth W).ker_evalAt P', RingHom.mem_ker]
  exact h_c

/-- Subtracting off its evaluation lands `r` in the maximal ideal: with
`c = evalAt P' r`, the difference `r - algebraMap c` lies in `maximalIdealAt P'`.
This is the "vanishing at `P'`" half of `ker_evalAt`, since `evalAt` is constant
on the image of `algebraMap F`. -/
private theorem sub_algebraMap_evalAt_mem_maximalIdealAt
    (P' : (W_smooth W).SmoothPoint) (r : (W_smooth W).CoordinateRing) :
    r - algebraMap F (W_smooth W).CoordinateRing ((W_smooth W).evalAt P' r) ∈
      (W_smooth W).maximalIdealAt P' := by
  rw [← (W_smooth W).ker_evalAt P', RingHom.mem_ker, map_sub,
    Curves.SmoothPlaneCurve.evalAt_algebraMap]
  simp

/-- The translate `AlgEquiv` of a constant-corrected coordinate function splits as
`τ_Q(algMap r) = τ_Q(algMap r') + algMap c`, where `r' = r - algMap c` and the
last summand is the *same* constant `c` because `τ_Q` is an `F`-algebra equivalence
(so it commutes with `algebraMap F`) and `algMap F → FunctionField` factors through
`CoordinateRing`. Purely the ring/`F`-algebra structure of `τ_Q`; no valuation
input. -/
private theorem translateAlgEquivOfPoint_algebraMap_eq_add_algebraMap_const
    (Q : W.toAffine.Point) (r' : (W_smooth W).CoordinateRing) (c : F) :
    (translateAlgEquivOfPoint W Q)
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
          (r' + algebraMap F (W_smooth W).CoordinateRing c)) =
      (translateAlgEquivOfPoint W Q)
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r') +
      algebraMap F W.toAffine.FunctionField c := by
  rw [map_add]
  rw [show (translateAlgEquivOfPoint W Q)
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField) r' +
            (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
              ((algebraMap F (W_smooth W).CoordinateRing) c)) =
        (translateAlgEquivOfPoint W Q)
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField) r') +
        (translateAlgEquivOfPoint W Q)
          ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
            ((algebraMap F (W_smooth W).CoordinateRing) c)) from map_add _ _ _]
  congr 1
  show (translateAlgEquivOfPoint W Q)
      ((algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField)
        ((algebraMap F (W_smooth W).CoordinateRing) c)) =
    algebraMap F W.toAffine.FunctionField c
  rw [← IsScalarTower.algebraMap_apply F (W_smooth W).CoordinateRing
    (W_smooth W).FunctionField c]
  change (translateAlgEquivOfPoint W Q)
      (algebraMap F W.toAffine.FunctionField c) =
    algebraMap F W.toAffine.FunctionField c
  rw [(translateAlgEquivOfPoint W Q).commutes c]

/-- For `r ∈ CoordinateRing` with `r ∉ maxIdealAt(P+k)`,
`pV P (τ_k(algMap r)) = 1`. -/
theorem pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (r : (W_smooth W).CoordinateRing)
    (h_notMem : r ∉ (W_smooth W).maximalIdealAt
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)) :
    (W_smooth W).pointValuation P
      (translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField r)) = 1 := by
  set P' := P.translate_of_finite
    (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) h with hP'_def
  -- `r` corrected by its constant value `c = evalAt P' r` lands in `maximalIdealAt P'`.
  set c : F := (W_smooth W).evalAt P' r with hc_def
  have h_c_ne : c ≠ 0 := evalAt_ne_zero_of_notMem_maximalIdealAt W P' r h_notMem
  set r' : (W_smooth W).CoordinateRing :=
    r - algebraMap F (W_smooth W).CoordinateRing c with hr'_def
  have h_r'_mem : r' ∈ (W_smooth W).maximalIdealAt P' :=
    sub_algebraMap_evalAt_mem_maximalIdealAt W P' r
  -- Split `τ_k(algMap r) = τ_k(algMap r') + algMap c`; the constant `c` is preserved.
  have h_r_eq : r = r' + algebraMap F (W_smooth W).CoordinateRing c := by rw [hr'_def]; ring
  rw [h_r_eq, translateAlgEquivOfPoint_algebraMap_eq_add_algebraMap_const W _ r' c]
  -- `pV` of the constant term is `1`; the maximal-ideal term is strictly smaller.
  have h_alg_c_eq_one : (W_smooth W).pointValuation P
      (algebraMap F (W_smooth W).FunctionField c) = 1 :=
    pointValuation_algebraMap_F_eq_one_of_ne_zero W P h_c_ne
  have h_lt : (W_smooth W).pointValuation P
      (translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r')) <
      (W_smooth W).pointValuation P
        (algebraMap F (W_smooth W).FunctionField c) := by
    rw [h_alg_c_eq_one]
    exact isTranslateMaxIdealCompatible_on_CoordinateRing_some W P xk yk h_ns h r' h_r'_mem
  exact (Valuation.map_add_eq_of_lt_right _ h_lt).trans h_alg_c_eq_one

/-- For nonzero `f` with `pV P f ≤ 1`, `0 ≤ ord_P P f` — companion to
`one_le_ord_P_iff_pointValuation_lt_one`. -/
theorem zero_le_ord_P_of_pointValuation_le_one {f : (W_smooth W).FunctionField}
    (P : (W_smooth W).SmoothPoint) (hf : (W_smooth W).pointValuation P f ≤ 1) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P f := by
  by_cases hzero : f = 0
  · subst hzero
    rw [Curves.SmoothPlaneCurve.ord_P_zero]
    exact le_top
  · have hv : (W_smooth W).pointValuation P f ≠ 0 :=
      ((W_smooth W).pointValuation P).ne_zero_iff.mpr hzero
    have h_or : (W_smooth W).pointValuation P f < 1 ∨
        (W_smooth W).pointValuation P f = 1 := lt_or_eq_of_le hf
    rcases h_or with hlt | heq
    · have h_one_le : (1 : WithTop ℤ) ≤ (W_smooth W).ord_P P f :=
        (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one (P := P) hzero).mpr hlt
      have h_zero_le_one : (0 : WithTop ℤ) ≤ (1 : WithTop ℤ) := by
        have : (0 : ℤ) ≤ (1 : ℤ) := by lia
        exact_mod_cast this
      exact le_trans h_zero_le_one h_one_le
    · have h_eq_top_iff := Curves.SmoothPlaneCurve.ord_P_eq_top_iff (C := W_smooth W)
        (P := P) f
      have h_not_lt_one : ¬ (W_smooth W).pointValuation P f < 1 := by
        rw [heq]; exact lt_irrefl _
      have h_not_one_le : ¬ (1 : WithTop ℤ) ≤ (W_smooth W).ord_P P f := fun h_le ↦
        h_not_lt_one ((Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
          (P := P) hzero).mp h_le)
      unfold Curves.SmoothPlaneCurve.ord_P
      rw [dif_neg hv]
      change (0 : WithTop ℤ) ≤ ((-(WithZero.unzero hv).toAdd : ℤ) : WithTop ℤ)
      have h_unz_one : WithZero.unzero hv = 1 := by
        apply WithZero.coe_injective
        rw [WithZero.coe_unzero, WithZero.coe_one]
        exact heq
      rw [h_unz_one]
      simp

/-- Base step of the powers extension: for any `s` in the coordinate ring,
`0 ≤ ord_P P (τ_k(algMap s))`. Combines `pV ≤ 1` (Item 2) with
`zero_le_ord_P_of_pointValuation_le_one`. -/
private theorem zero_le_ord_P_translateAlgEquivOfPoint_algebraMap_of_isSome
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (s : (W_smooth W).CoordinateRing) :
    (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField s)) := by
  have h_le : (W_smooth W).pointValuation P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField s)) ≤ 1 :=
    pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome
      W P xk yk h_ns h s
  exact zero_le_ord_P_of_pointValuation_le_one W P h_le

/-- Inductive step of the powers extension: if `m` lies in the maximal ideal at
`P+k`, then `1 ≤ ord_P P (τ_k(algMap m))`. Item 3 gives `pV < 1`, which is `ord ≥ 1`
(`one_le_ord_P_iff_pointValuation_lt_one`), with the zero case handled by `ord_P_zero`. -/
private theorem one_le_ord_P_translateAlgEquivOfPoint_algebraMap_of_mem
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (m : (W_smooth W).CoordinateRing)
    (h_m : m ∈ (W_smooth W).maximalIdealAt
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)) :
    (1 : WithTop ℤ) ≤ (W_smooth W).ord_P P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField m)) := by
  set f : (W_smooth W).FunctionField :=
    (translateAlgEquivOfPoint W
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField m) with hf
  have h_pV_lt : (W_smooth W).pointValuation P f < 1 :=
    isTranslateMaxIdealCompatible_on_CoordinateRing_some
      W P xk yk h_ns h m h_m
  by_cases h_zero : f = 0
  · rw [h_zero, Curves.SmoothPlaneCurve.ord_P_zero]
    exact le_top
  · exact (Curves.SmoothPlaneCurve.one_le_ord_P_iff_pointValuation_lt_one
      (P := P) h_zero).mpr h_pV_lt

/-- **Powers extension**: `r ∈ maxIdealAt(P+k)^n` implies
`ord_P P (τ_k(algMap r)) ≥ n`. Proof via `Submodule.pow_induction_on_left'`.

Base `n = 0` uses Item 2 (`pV ≤ 1`) plus `zero_le_ord_P_of_pointValuation_le_one`.
Add case: `ord(x+y) ≥ min(ord x, ord y)`.
mem_mul case: Item 3 gives `ord(τ_k(algMap m)) ≥ 1` for `m ∈ M`, then
`ord_P_mul` adds with IH. -/
theorem ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (n : ℕ) (r : (W_smooth W).CoordinateRing)
    (h_mem : r ∈ ((W_smooth W).maximalIdealAt
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)) ^ n) :
    (n : WithTop ℤ) ≤ (W_smooth W).ord_P P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField r)) := by
  set k_pt : (W_smooth W).toAffine.Point :=
    Affine.Point.some xk yk h_ns with hk_pt
  set P' := P.translate_of_finite k_pt h with hP'
  set algC : (W_smooth W).CoordinateRing →+* (W_smooth W).FunctionField :=
    algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField with halgC
  set τ : (W_smooth W).FunctionField →+* (W_smooth W).FunctionField :=
    (translateAlgEquivOfPoint W k_pt).toAlgHom.toRingHom with hτ
  refine Submodule.pow_induction_on_left' ((W_smooth W).maximalIdealAt P')
    (C := fun i x _ ↦ (i : WithTop ℤ) ≤ (W_smooth W).ord_P P (τ (algC x)))
    ?_ ?_ ?_ h_mem
  · -- Base case: `0 ≤ ord_P P (τ_k(algMap s))`.
    intro s
    change (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (τ (algC s))
    exact zero_le_ord_P_translateAlgEquivOfPoint_algebraMap_of_isSome W P xk yk h_ns h s
  · -- Add case: `ord(x+y) ≥ min(ord x, ord y) ≥ min` of the two IHs.
    intro x y i _ _ hx_ge hy_ge
    have h_rw : τ (algC (x + y)) = τ (algC x) + τ (algC y) := by
      rw [map_add, map_add]
    rw [h_rw]
    refine le_trans (le_min hx_ge hy_ge) ?_
    exact Curves.SmoothPlaneCurve.ord_P_add_le _ _
  · -- mem_mul case: `ord(τ_k(algMap m)) ≥ 1` for `m ∈ M`, then `ord_P_mul` adds with IH.
    intro m h_m i x _ hx_ge
    have h_rw : τ (algC (m * x)) = τ (algC m) * τ (algC x) := by
      rw [map_mul, map_mul]
    rw [h_rw, Curves.SmoothPlaneCurve.ord_P_mul]
    have h_m_ord_ge : (1 : WithTop ℤ) ≤ (W_smooth W).ord_P P (τ (algC m)) :=
      one_le_ord_P_translateAlgEquivOfPoint_algebraMap_of_mem W P xk yk h_ns h m h_m
    have h_succ : ((i.succ : ℕ) : WithTop ℤ) =
        (1 : WithTop ℤ) + (i : WithTop ℤ) := by
      have : (i.succ : ℤ) = 1 + (i : ℤ) := by push_cast; lia
      exact_mod_cast this
    rw [h_succ]
    exact add_le_add h_m_ord_ge hx_ge

/-- **Symmetric powers extension**: for `s ∈ maxIdealAt(P)^n` in CoordinateRing,
`ord_P (P+k) (τ_{-k}(algMap s)) ≥ n`. This is step 1 applied at (P+k, -k);
the condition `((P+k).toAffinePoint + (-k)).IsSome` reduces to `P.IsSome`
since `(P+k) + (-k) = P` as an Affine.Point. -/
theorem ord_P_translateAlgEquivOfPoint_neg_algebraMap_ge_of_pow_mem
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (n : ℕ) (s : (W_smooth W).CoordinateRing) (h_mem : s ∈ ((W_smooth W).maximalIdealAt P) ^ n) :
    (n : WithTop ℤ) ≤ (W_smooth W).ord_P
      (P.translate_of_finite
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) h)
      ((translateAlgEquivOfPoint W
        ((Affine.Point.some xk (W.toAffine.negY xk yk)
            ((Affine.nonsingular_neg xk yk).mpr h_ns)
          : (W_smooth W).toAffine.Point)))
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField s)) := by
  set P' : (W_smooth W).SmoothPoint :=
    P.translate_of_finite (Affine.Point.some xk yk h_ns :
      (W_smooth W).toAffine.Point) h with hP'
  set yk_neg : F := W.toAffine.negY xk yk with hyk_neg
  have h_ns_neg : W.toAffine.Nonsingular xk yk_neg :=
    (Affine.nonsingular_neg xk yk).mpr h_ns
  have h_P'_plus_neg_k :
      P'.toAffinePoint +
        (Affine.Point.some xk yk_neg h_ns_neg :
          (W_smooth W).toAffine.Point) =
      P.toAffinePoint := by
    change (P.translate_of_finite (Affine.Point.some xk yk h_ns :
      (W_smooth W).toAffine.Point) h).toAffinePoint +
      (Affine.Point.some xk yk_neg h_ns_neg :
        (W_smooth W).toAffine.Point) =
      P.toAffinePoint
    rw [Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint, add_assoc]
    have h_negation : (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) +
        (Affine.Point.some xk yk_neg h_ns_neg :
          (W_smooth W).toAffine.Point) = 0 := by
      apply Affine.Point.add_of_Y_eq rfl
      rw [hyk_neg]
      exact (Affine.negY_negY xk yk).symm
    rw [h_negation, add_zero]
  have h_P'_plus_neg_k_isSome :
      (P'.toAffinePoint +
        (Affine.Point.some xk yk_neg h_ns_neg :
          (W_smooth W).toAffine.Point)).IsSome := by
    rw [h_P'_plus_neg_k]
    exact Affine.Point.some_isSome P.x P.y P.nonsingular
  have h_P'_translate :
      P'.translate_of_finite
        (Affine.Point.some xk yk_neg h_ns_neg :
          (W_smooth W).toAffine.Point) h_P'_plus_neg_k_isSome = P := by
    apply Curves.SmoothPlaneCurve.SmoothPoint.ext
    · exact Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_x
        P' _ h_P'_plus_neg_k_isSome
        (by rw [h_P'_plus_neg_k]; rfl)
    · exact Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_y
        P' _ h_P'_plus_neg_k_isSome
        (by rw [h_P'_plus_neg_k]; rfl)
  have step1 := ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem
    W P' xk yk_neg h_ns_neg h_P'_plus_neg_k_isSome n s
    (by rw [h_P'_translate]; exact h_mem)
  exact step1

/-- Translating by `-k` undoes translating by `k`: on `K(E)`, the algebra automorphism
`τ_{-k}` is a left inverse of `τ_k`. Here `-k` is `(xk, negY xk yk)`. -/
private theorem translateAlgEquivOfPoint_neg_apply_apply
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_ns_neg : W.toAffine.Nonsingular xk (W.toAffine.negY xk yk))
    (g : (W_smooth W).FunctionField) :
    (translateAlgEquivOfPoint W
        (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg :
          (W_smooth W).toAffine.Point))
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) g) = g := by
  have h_neg_pt : (Affine.Point.some xk yk h_ns : W.toAffine.Point) +
      (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg : W.toAffine.Point) =
      (Affine.Point.zero : W.toAffine.Point) :=
    add_neg_cancel (Affine.Point.some xk yk h_ns : W.toAffine.Point)
  have h_group_hom :
      translateAlgEquivOfPoint W
        ((Affine.Point.some xk yk h_ns : W.toAffine.Point) +
          (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg : W.toAffine.Point)) =
      (translateAlgEquivOfPoint W
          (Affine.Point.some xk yk h_ns : W.toAffine.Point)).trans
        (translateAlgEquivOfPoint W
          (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg : W.toAffine.Point)) :=
    translateAlgEquivOfPoint_add W _ _
  rw [h_neg_pt, translateAlgEquivOfPoint_zero] at h_group_hom
  exact (congrArg (fun (e : (W_smooth W).FunctionField ≃ₐ[F]
    (W_smooth W).FunctionField) ↦ e g) h_group_hom).symm

/-- The translate `P + k` translated back by `-k` returns to `P` at the level of the
underlying affine point: `(P.translate_of_finite k h).toAffinePoint + (-k) = P.toAffinePoint`,
where `-k` is `(xk, negY xk yk)`. -/
private theorem translate_of_finite_toAffinePoint_add_neg
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_ns_neg : W.toAffine.Nonsingular xk (W.toAffine.negY xk yk))
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h).toAffinePoint +
      (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg :
        (W_smooth W).toAffine.Point) =
    P.toAffinePoint := by
  rw [Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_toAffinePoint, add_assoc]
  have h_neg_pt : (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) +
      (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg :
        (W_smooth W).toAffine.Point) = 0 :=
    add_neg_cancel _
  rw [h_neg_pt, add_zero]

/-- An element `f ∈ K(E)` with `pointValuation P f ≤ 1` lies in the local ring at `P`, hence
is a fraction `u / q` of elements of the CoordinateRing with denominator `q ∉ maxIdealAt P`:
there exist `u, q` in the CoordinateRing with `q ∉ maxIdealAt P` and `f * algMap q = algMap u`. -/
private theorem exists_coordinateRing_repr_of_pointValuation_le_one
    (P : (W_smooth W).SmoothPoint) {f : (W_smooth W).FunctionField}
    (hf : (W_smooth W).pointValuation P f ≤ 1) :
    ∃ u q : (W_smooth W).CoordinateRing,
      q ∉ (W_smooth W).maximalIdealAt P ∧
        f * algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField q =
          algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField u := by
  obtain ⟨x_loc, hx_loc⟩ : ∃ x : (W_smooth W).localRingAt P,
      algebraMap ((W_smooth W).localRingAt P) (W_smooth W).FunctionField x = f :=
    (Curves.SmoothPlaneCurve.mem_localRingAt_image_iff_pointValuation_le_one _).mpr hf
  obtain ⟨⟨u, q⟩, hq_eq_loc⟩ := IsLocalization.surj
    ((W_smooth W).maximalIdealAt P).primeCompl x_loc
  refine ⟨u, q, q.2, ?_⟩
  have h_apply := congrArg (algebraMap ((W_smooth W).localRingAt P)
    (W_smooth W).FunctionField) hq_eq_loc
  rw [map_mul, hx_loc, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    at h_apply
  exact h_apply

/-- A CoordinateRing element outside `maxIdealAt P` is a unit at `P`: its image has `ord_P = 0`. -/
private theorem ord_P_algebraMap_eq_zero_of_notMem
    (P : (W_smooth W).SmoothPoint) {q : (W_smooth W).CoordinateRing}
    (hq : q ∉ (W_smooth W).maximalIdealAt P) :
    (W_smooth W).ord_P P (algebraMap (W_smooth W).CoordinateRing
      (W_smooth W).FunctionField q) = 0 := by
  have hq_ne_zero : q ≠ 0 := fun h_eq ↦ hq (h_eq ▸ Submodule.zero_mem _)
  by_contra h_ord_ne
  exact hq (((W_smooth W).ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt hq_ne_zero P).mp
    h_ord_ne)

/-- Multiplying by a CoordinateRing element that is a unit at `P` (i.e. `q ∉ maxIdealAt P`)
does not change the order: `ord_P P (f * algMap q) = ord_P P f`. -/
private theorem ord_P_mul_algebraMap_notMem (P : (W_smooth W).SmoothPoint)
    (f : (W_smooth W).FunctionField) {q : (W_smooth W).CoordinateRing}
    (hq : q ∉ (W_smooth W).maximalIdealAt P) :
    (W_smooth W).ord_P P (f * algebraMap (W_smooth W).CoordinateRing
      (W_smooth W).FunctionField q) = (W_smooth W).ord_P P f := by
  rw [Curves.SmoothPlaneCurve.ord_P_mul, ord_P_algebraMap_eq_zero_of_notMem W P hq, add_zero]

-- `IsIntegrallyClosed CoordinateRing` (needed for `ord_P_algebraMap_eq_count`) is supplied
-- unconditionally by `HasseWeil.Ramification.coordinateRing_isIntegrallyClosed`, so no
-- `[NeZero 2/3]` (char ≠ 2, 3) hypotheses are required here.
private theorem mem_pow_maxIdealAt_of_le_ord_P_algebraMap (P : (W_smooth W).SmoothPoint)
    {r : (W_smooth W).CoordinateRing} (hr : r ≠ 0) {n : ℕ}
    (h_le : (n : WithTop ℤ) ≤ (W_smooth W).ord_P P
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r)) :
    r ∈ ((W_smooth W).maximalIdealAt P) ^ n := by
  set M := (W_smooth W).maximalIdealAt P with hM_def
  rw [(W_smooth W).ord_P_algebraMap_eq_count P hr] at h_le
  set count_val := (Associates.mk M).count
    (Associates.mk (Ideal.span ({r} : Set (W_smooth W).CoordinateRing))).factors
    with hcount_def
  have h_nat_le : n ≤ count_val := by exact_mod_cast h_le
  have h_span_ne : Ideal.span ({r} : Set (W_smooth W).CoordinateRing) ≠ 0 := by
    rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    exact hr
  have h_assoc_ne :
      Associates.mk (Ideal.span ({r} : Set (W_smooth W).CoordinateRing)) ≠ 0 := by
    rwa [ne_eq, Associates.mk_eq_zero]
  have h_M_prime : Prime M := by
    rw [Ideal.prime_iff_isPrime ((W_smooth W).maximalIdealAt_ne_bot P)]
    exact ((W_smooth W).maximalIdealAt_isMaximal P).isPrime
  have h_M_irr : Irreducible (Associates.mk M) := by
    rw [Associates.irreducible_mk]
    exact h_M_prime.irreducible
  have h_pow_le : (Associates.mk M) ^ n ≤
      Associates.mk (Ideal.span ({r} : Set (W_smooth W).CoordinateRing)) := by
    rw [Associates.prime_pow_dvd_iff_le h_assoc_ne h_M_irr]
    exact h_nat_le
  rw [← Associates.mk_pow] at h_pow_le
  rw [Associates.mk_le_mk_iff_dvd] at h_pow_le
  have h_le_ideal :
      Ideal.span ({r} : Set (W_smooth W).CoordinateRing) ≤ M ^ n :=
    Ideal.dvd_iff_le.mp h_pow_le
  rwa [Ideal.span_singleton_le_iff_mem] at h_le_ideal

/-- CoordRing forward inequality: for nonzero `r ∈ CoordinateRing`,
`ord_(P+k) (algMap r) ≤ ord_P (τ_k (algMap r))`. -/
theorem ord_P_translateAlgEquivOfPoint_algebraMap_le_of_ne_zero
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (r : (W_smooth W).CoordinateRing) (hr : r ≠ 0) :
    (W_smooth W).ord_P
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)
      (algebraMap (W_smooth W).CoordinateRing
        (W_smooth W).FunctionField r) ≤
    (W_smooth W).ord_P P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField r)) := by
  set k_pt : (W_smooth W).toAffine.Point :=
    Affine.Point.some xk yk h_ns with hk_pt_def
  set P' := P.translate_of_finite k_pt h with hP'_def
  set n_nat : ℕ := (Associates.mk ((W_smooth W).maximalIdealAt P')).count
    (Associates.mk (Ideal.span ({r} :
      Set (W_smooth W).CoordinateRing))).factors with hn_def
  have h_ord_eq_count :
      (W_smooth W).ord_P P'
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField r) =
      ((n_nat : ℤ) : WithTop ℤ) :=
    (W_smooth W).ord_P_algebraMap_eq_count P' hr
  have h_mem : r ∈ ((W_smooth W).maximalIdealAt P') ^ n_nat := by
    apply mem_pow_maxIdealAt_of_le_ord_P_algebraMap W P' hr
    rw [h_ord_eq_count]
    exact_mod_cast le_refl (n_nat : ℤ)
  have h_step1 :
      ((n_nat : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P P
        ((translateAlgEquivOfPoint W k_pt)
          (algebraMap (W_smooth W).CoordinateRing
            (W_smooth W).FunctionField r)) := by
    have := ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_pow_mem
      W P xk yk h_ns h n_nat r h_mem
    exact_mod_cast this
  rw [h_ord_eq_count]
  exact h_step1

/-- After translating the lift `f · algMap q = algMap u` by `-k` and using `τ_{-k} ∘ τ_k = id`
(with `f = τ_k (algMap r)`), the numerator's `τ_{-k}`-image factors as
`τ_{-k}(algMap u) = algMap r · τ_{-k}(algMap q)`. Here `-k = (xk, negY xk yk)`, and the maps are
routed through `RingHom`s on `(W_smooth W).FunctionField` to fix `HMul` unification. -/
private theorem translateAlgEquivOfPoint_neg_algebraMap_numerator_eq
    (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_ns_neg : W.toAffine.Nonsingular xk (W.toAffine.negY xk yk))
    (r u q : (W_smooth W).CoordinateRing) (f : (W_smooth W).FunctionField)
    (hf : (translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r) = f)
    (h_lift : f *
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField q =
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField u) :
    letI algC : (W_smooth W).CoordinateRing →+* (W_smooth W).FunctionField :=
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField
    letI τkneg : (W_smooth W).FunctionField →+* (W_smooth W).FunctionField :=
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg :
          (W_smooth W).toAffine.Point)).toRingEquiv).toRingHom
    τkneg (algC u) = algC r * τkneg (algC q) := by
  rw [← h_lift, map_mul]
  congr 1
  rw [← hf]
  exact translateAlgEquivOfPoint_neg_apply_apply W xk yk h_ns h_ns_neg _

/-- The `τ_{-k}`-image of `algMap q` is a unit at `P + k` whenever `q` is a nonzero CoordinateRing
element that is a unit at `P` (`q ∉ maxIdealAt P`): `ord_(P+k) (τ_{-k}(algMap q)) = 0`. The point is
that `(P + k) + (-k) = P`, so `q ∉ maxIdealAt P` transports to `q ∉ maxIdealAt` of the back-translate
of `P + k` by `-k`. Here `-k = (xk, negY xk yk)`. -/
private theorem ord_P_translate_translateAlgEquivOfPoint_neg_algebraMap_eq_zero_of_notMem
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h_ns_neg : W.toAffine.Nonsingular xk (W.toAffine.negY xk yk))
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (q : (W_smooth W).CoordinateRing) (hq_ne_zero : q ≠ 0)
    (hq_notMem : q ∉ (W_smooth W).maximalIdealAt P) :
    (W_smooth W).ord_P
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg :
          (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField q)) = 0 := by
  set k_neg : (W_smooth W).toAffine.Point :=
    Affine.Point.some xk (W.toAffine.negY xk yk) h_ns_neg with hk_neg_def
  set P' := P.translate_of_finite (Affine.Point.some xk yk h_ns :
    (W_smooth W).toAffine.Point) h with hP'_def
  set τkneg : (W_smooth W).FunctionField →+* (W_smooth W).FunctionField :=
    ((translateAlgEquivOfPoint W k_neg).toRingEquiv).toRingHom with hτkneg_def
  set algC : (W_smooth W).CoordinateRing →+* (W_smooth W).FunctionField :=
    algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField with halgC_def
  -- `(P+k) + (-k) = P`, so `q ∉ maxIdealAt` of `(P+k).translate_of_finite (-k)`.
  have h_P'_plus_neg_k : P'.toAffinePoint + k_neg = P.toAffinePoint :=
    translate_of_finite_toAffinePoint_add_neg W P xk yk h_ns h_ns_neg h
  have h_P'_plus_neg_k_isSome : (P'.toAffinePoint + k_neg).IsSome := by
    rw [h_P'_plus_neg_k]; exact Affine.Point.some_isSome P.x P.y P.nonsingular
  have h_P'_translate : P'.translate_of_finite k_neg h_P'_plus_neg_k_isSome = P :=
    Curves.SmoothPlaneCurve.SmoothPoint.ext
      (Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_x P' _ _
        (by rw [h_P'_plus_neg_k]; rfl))
      (Curves.SmoothPlaneCurve.SmoothPoint.translate_of_finite_y P' _ _
        (by rw [h_P'_plus_neg_k]; rfl))
  have hq_notMem' : (q : (W_smooth W).CoordinateRing) ∉
      (W_smooth W).maximalIdealAt (P'.translate_of_finite k_neg h_P'_plus_neg_k_isSome) := by
    rw [h_P'_translate]; exact hq_notMem
  -- `τ_{-k}(algMap q)` is nonzero, hence its order is determined by its point valuation, which is
  -- `1` since `q` is a unit there.
  have h_algMap_q_ne : algC q ≠ 0 := fun h_eq ↦
    hq_ne_zero ((IsFractionRing.injective _ _) (h_eq.trans (map_zero _).symm))
  have h_τ_neg_q_ne : τkneg (algC q) ≠ 0 := fun h_eq ↦
    h_algMap_q_ne ((translateAlgEquivOfPoint W k_neg).injective (h_eq.trans (map_zero _).symm))
  exact (Curves.SmoothPlaneCurve.ord_P_eq_zero_iff_pointValuation_eq_one (W_smooth W)
    h_τ_neg_q_ne).mpr
    (pointValuation_translateAlgEquivOfPoint_algebraMap_eq_one_of_notMem
      W P' xk (W.toAffine.negY xk yk) h_ns_neg h_P'_plus_neg_k_isSome q hq_notMem')

/-- **Reverse inequality, numerator bound.** If `algMap u` is `τ_k (algMap r)` scaled by a
CoordinateRing element `q` that is a unit at `P` (`q ∉ maxIdealAt P`), then the order of the
numerator `algMap u` at `P` bounds the order of `algMap r` at `P + k`:
`ord_P (algMap u) ≤ ord_(P+k) (algMap r)`. This is the heart of the reverse inequality:
write `m = ord_P (algMap u)`; then `u ∈ maxIdealAt(P)^m`, so step 1 at `(P+k, -k)` gives
`m ≤ ord_(P+k) (τ_{-k}(algMap u))`, and `τ_{-k}(algMap u) = algMap r · τ_{-k}(algMap q)` where
the last factor has order `0` at `P+k` (it is a unit there, since `(P+k) + (-k) = P`). -/
private theorem ord_P_algebraMap_le_ord_P_translate_algebraMap_of_lift
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (r u q : (W_smooth W).CoordinateRing) (hu : u ≠ 0)
    (hq_notMem : q ∉ (W_smooth W).maximalIdealAt P)
    (f : (W_smooth W).FunctionField)
    (hf : (translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r) = f)
    (h_lift : f *
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField q =
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField u) :
    (W_smooth W).ord_P P
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField u) ≤
    (W_smooth W).ord_P
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)
      (algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField r) := by
  set P' := P.translate_of_finite (Affine.Point.some xk yk h_ns :
    (W_smooth W).toAffine.Point) h with hP'_def
  set yk_neg : F := W.toAffine.negY xk yk with hyk_neg_def
  have h_ns_neg : W.toAffine.Nonsingular xk yk_neg :=
    (Affine.nonsingular_neg xk yk).mpr h_ns
  set k_neg : (W_smooth W).toAffine.Point := Affine.Point.some xk yk_neg h_ns_neg with hk_neg_def
  set algC : (W_smooth W).CoordinateRing →+* (W_smooth W).FunctionField :=
    algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField with halgC_def
  set τkneg : (W_smooth W).FunctionField →+* (W_smooth W).FunctionField :=
    ((translateAlgEquivOfPoint W k_neg).toRingEquiv).toRingHom with hτkneg_def
  -- `m = ord_P (algMap u)` as a count exponent; then `u ∈ maxIdealAt(P)^m`.
  set m_nat : ℕ := (Associates.mk ((W_smooth W).maximalIdealAt P)).count
    (Associates.mk (Ideal.span ({u} :
      Set (W_smooth W).CoordinateRing))).factors with hm_def
  have h_ord_u_eq_count : (W_smooth W).ord_P P (algC u) = ((m_nat : ℤ) : WithTop ℤ) :=
    (W_smooth W).ord_P_algebraMap_eq_count P hu
  have h_u_mem : u ∈ ((W_smooth W).maximalIdealAt P) ^ m_nat := by
    apply mem_pow_maxIdealAt_of_le_ord_P_algebraMap W P hu
    rw [h_ord_u_eq_count]
    exact_mod_cast le_refl (m_nat : ℤ)
  -- Step 1 at `(P+k, -k)`: `m ≤ ord_{P+k} (τ_{-k}(algMap u))`.
  have h_step2 : ((m_nat : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P P' (τkneg (algC u)) := by
    have := ord_P_translateAlgEquivOfPoint_neg_algebraMap_ge_of_pow_mem
      W P xk yk h_ns h m_nat u h_u_mem
    exact_mod_cast this
  -- Apply `τ_{-k}` to the lift and cancel using `τ_{-k} ∘ τ_k = id`:
  -- `τ_{-k}(algMap u) = algMap r · τ_{-k}(algMap q)`.
  have h_τ_neg_u : τkneg (algC u) = algC r * τkneg (algC q) :=
    translateAlgEquivOfPoint_neg_algebraMap_numerator_eq W xk yk h_ns h_ns_neg r u q f hf h_lift
  -- `(P+k) + (-k) = P`, so `q ∉ maxIdealAt` of `(P+k).translate_of_finite (-k)`, hence
  -- `τ_{-k}(algMap q)` is a unit at `P+k`.
  have hq_ne_zero : q ≠ 0 := fun h_eq ↦ hq_notMem (h_eq ▸ Submodule.zero_mem _)
  have h_ord_τ_neg_q_zero : (W_smooth W).ord_P P' (τkneg (algC q)) = 0 :=
    ord_P_translate_translateAlgEquivOfPoint_neg_algebraMap_eq_zero_of_notMem
      W P xk yk h_ns h_ns_neg h q hq_ne_zero hq_notMem
  -- Conclude: `m ≤ ord_{P+k} (algMap r · τ_{-k}(algMap q)) = ord_{P+k}(algMap r)`.
  rw [h_τ_neg_u, Curves.SmoothPlaneCurve.ord_P_mul, h_ord_τ_neg_q_zero, add_zero] at h_step2
  rwa [h_ord_u_eq_count]

/-- CoordRing reverse inequality: for nonzero `r ∈ CoordinateRing`,
`ord_P (τ_k (algMap r)) ≤ ord_(P+k) (algMap r)`. -/
theorem ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (r : (W_smooth W).CoordinateRing) (hr : r ≠ 0) :
    (W_smooth W).ord_P P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField r)) ≤
    (W_smooth W).ord_P
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)
      (algebraMap (W_smooth W).CoordinateRing
        (W_smooth W).FunctionField r) := by
  set k_pt : (W_smooth W).toAffine.Point :=
    Affine.Point.some xk yk h_ns with hk_pt_def
  -- (Lean's `HMul` has trouble unifying `W.toAffine.FunctionField` vs
  -- `(W_smooth W).FunctionField`; routing the maps through `RingHom`s set on the latter fixes it.)
  set algC : (W_smooth W).CoordinateRing →+* (W_smooth W).FunctionField :=
    algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField with halgC_def
  set τk : (W_smooth W).FunctionField →+* (W_smooth W).FunctionField :=
    ((translateAlgEquivOfPoint W k_pt).toRingEquiv).toRingHom with hτk_def
  -- `f := τ_k (algMap r)` has `pointValuation P ≤ 1`, so it is a fraction `algMap u / algMap q`
  -- with `q ∉ maxIdealAt P`; the numerator `u` is nonzero.
  have h_pV_le : (W_smooth W).pointValuation P (τk (algC r)) ≤ 1 :=
    pointValuation_translateAlgEquivOfPoint_algebraMap_le_one_of_isSome W P xk yk h_ns h r
  obtain ⟨u, q, hq_notMem, h_lifted⟩ :=
    exists_coordinateRing_repr_of_pointValuation_le_one W P h_pV_le
  have h_algMapR_ne : algC r ≠ 0 := fun h_eq ↦
    hr ((IsFractionRing.injective _ _) (h_eq.trans (map_zero _).symm))
  have h_τr_ne : τk (algC r) ≠ 0 := fun h_eq ↦
    h_algMapR_ne ((translateAlgEquivOfPoint W k_pt).injective (h_eq.trans (map_zero _).symm))
  have hq_ne_zero : q ≠ 0 := fun h_eq ↦ hq_notMem (h_eq ▸ Submodule.zero_mem _)
  have h_algMap_q_ne : algC q ≠ 0 := fun h_eq ↦
    hq_ne_zero ((IsFractionRing.injective _ _) (h_eq.trans (map_zero _).symm))
  have hu_ne : u ≠ 0 := fun h_eq ↦
    (h_lifted ▸ mul_ne_zero h_τr_ne h_algMap_q_ne : algC u ≠ 0) (by rw [h_eq, map_zero])
  -- Since `algMap q` is a unit at `P`, `ord_P (τ_k (algMap r)) = ord_P (algMap u)`,
  -- and the numerator bound gives `ord_P (algMap u) ≤ ord_{P+k} (algMap r)`.
  rw [show (translateAlgEquivOfPoint W k_pt) (algC r) = τk (algC r) from rfl,
    ← ord_P_mul_algebraMap_notMem W P (τk (algC r)) hq_notMem, h_lifted]
  exact ord_P_algebraMap_le_ord_P_translate_algebraMap_of_lift
    W P xk yk h_ns h r u q hu_ne hq_notMem (τk (algC r)) rfl h_lifted

/-- CoordRing-level ord equality: for nonzero `r ∈ CoordinateRing`,
`ord_P (τ_k (algMap r)) = ord_(P+k) (algMap r)`. -/
theorem ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (r : (W_smooth W).CoordinateRing) (hr : r ≠ 0) :
    (W_smooth W).ord_P P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point))
        (algebraMap (W_smooth W).CoordinateRing
          (W_smooth W).FunctionField r)) =
    (W_smooth W).ord_P
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h)
      (algebraMap (W_smooth W).CoordinateRing
        (W_smooth W).FunctionField r) :=
  le_antisymm
    (ord_P_translateAlgEquivOfPoint_algebraMap_ge_of_ne_zero W P xk yk h_ns h r hr)
    (ord_P_translateAlgEquivOfPoint_algebraMap_le_of_ne_zero W P xk yk h_ns h r hr)

/-- A nonzero function-field element `g` is a quotient of two nonzero coordinate-ring
elements (with nonzero algebraMap images): `g = algC a / algC b`. The `DecidableEq F`
section instance is reported unused by the linter but is needed for `CoordinateRing`
instance synthesis (so it cannot be `omit`ted). -/
private theorem exists_coordinateRing_fraction_ne_zero
    (g : (W_smooth W).FunctionField) (hg : g ≠ 0) :
    ∃ a b : (W_smooth W).CoordinateRing, a ≠ 0 ∧ b ≠ 0 ∧
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField a ≠ 0 ∧
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField b ≠ 0 ∧
      g = algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField a /
        algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField b := by
  obtain ⟨a, b, hb_nzd, hab⟩ := IsFractionRing.div_surjective
    (A := (W_smooth W).CoordinateRing) g
  have hb_ne : b ≠ 0 := nonZeroDivisors.ne_zero hb_nzd
  have h_algMap_b_ne :
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField b ≠ 0 := fun h_eq ↦
    hb_ne ((IsFractionRing.injective _ _) (h_eq.trans (map_zero _).symm))
  have ha_ne : a ≠ 0 := by
    intro ha
    apply hg
    rw [← hab, ha, map_zero, zero_div]
  have h_algMap_a_ne :
      algebraMap (W_smooth W).CoordinateRing (W_smooth W).FunctionField a ≠ 0 := fun h_eq ↦
    ha_ne ((IsFractionRing.injective _ _) (h_eq.trans (map_zero _).symm))
  exact ⟨a, b, ha_ne, hb_ne, h_algMap_a_ne, h_algMap_b_ne, hab.symm⟩

/-- K(E)-level ord transport identity: for nonzero `g ∈ K(E)`,
`ord_P (τ_k g) = ord_(P+k) g`. Feeds the consumer
`isTranslateValuationCompatible_of_ord_P_eq`. -/
theorem translate_ord_eq_all_nonzero
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome)
    (g : (W_smooth W).FunctionField) (hg : g ≠ 0) :
    (W_smooth W).ord_P P
      ((translateAlgEquivOfPoint W
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)) g) =
    (W_smooth W).ord_P
      (P.translate_of_finite (Affine.Point.some xk yk h_ns :
        (W_smooth W).toAffine.Point) h) g := by
  set k_pt : (W_smooth W).toAffine.Point :=
    Affine.Point.some xk yk h_ns with hk_pt_def
  set P' := P.translate_of_finite k_pt h with hP'_def
  obtain ⟨a, b, ha_ne, hb_ne, h_algMap_a_ne, h_algMap_b_ne, hab_eq⟩ :=
    exists_coordinateRing_fraction_ne_zero W g hg
  set algC : (W_smooth W).CoordinateRing →+* (W_smooth W).FunctionField :=
    algebraMap (W_smooth W).CoordinateRing
      (W_smooth W).FunctionField with halgC_def
  have h_τ_g : (translateAlgEquivOfPoint W k_pt) g =
      (translateAlgEquivOfPoint W k_pt) (algC a) /
      (translateAlgEquivOfPoint W k_pt) (algC b) := by
    rw [hab_eq]
    exact map_div₀ (translateAlgEquivOfPoint W k_pt) _ _
  set τk : (W_smooth W).FunctionField →+* (W_smooth W).FunctionField :=
    ((translateAlgEquivOfPoint W k_pt).toRingEquiv).toRingHom with hτk_def
  have h_τk_apply : ∀ x : (W_smooth W).FunctionField,
      τk x = (translateAlgEquivOfPoint W k_pt) x := fun _ ↦ rfl
  have h_τk_a_ne : τk (algC a) ≠ 0 :=
    fun h_eq ↦ h_algMap_a_ne
      ((translateAlgEquivOfPoint W k_pt).injective (h_eq.trans (map_zero _).symm))
  have h_τk_b_ne : τk (algC b) ≠ 0 :=
    fun h_eq ↦ h_algMap_b_ne
      ((translateAlgEquivOfPoint W k_pt).injective (h_eq.trans (map_zero _).symm))
  have h_ord_τg :
      (W_smooth W).ord_P P ((translateAlgEquivOfPoint W k_pt) g) =
      (W_smooth W).ord_P P (τk (algC a)) -
      (W_smooth W).ord_P P (τk (algC b)) := by
    have h_τ_g' : (translateAlgEquivOfPoint W k_pt) g =
        τk (algC a) / τk (algC b) := h_τ_g
    rw [h_τ_g', div_eq_mul_inv, Curves.SmoothPlaneCurve.ord_P_mul,
      Curves.SmoothPlaneCurve.ord_P_inv _ h_τk_b_ne, sub_eq_add_neg]
  have h_ord_g :
      (W_smooth W).ord_P P' g =
      (W_smooth W).ord_P P' (algC a) - (W_smooth W).ord_P P' (algC b) := by
    rw [hab_eq, div_eq_mul_inv, Curves.SmoothPlaneCurve.ord_P_mul,
      Curves.SmoothPlaneCurve.ord_P_inv _ h_algMap_b_ne, sub_eq_add_neg]
  have h_eq_a :
      (W_smooth W).ord_P P (τk (algC a)) =
      (W_smooth W).ord_P P' (algC a) :=
    ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero
      W P xk yk h_ns h a ha_ne
  have h_eq_b :
      (W_smooth W).ord_P P (τk (algC b)) =
      (W_smooth W).ord_P P' (algC b) :=
    ord_P_translateAlgEquivOfPoint_algebraMap_eq_of_ne_zero
      W P xk yk h_ns h b hb_ne
  rw [h_ord_τg, h_ord_g, h_eq_a, h_eq_b]

/-- `IsTranslateValuationCompatible` for non-zero `k = some xk yk h_ns`. -/
theorem isTranslateValuationCompatible_some
    (P : (W_smooth W).SmoothPoint) (xk yk : F) (h_ns : W.toAffine.Nonsingular xk yk)
    (h : (P.toAffinePoint +
        (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point)).IsSome) :
    IsTranslateValuationCompatible W P
      (Affine.Point.some xk yk h_ns : (W_smooth W).toAffine.Point) h := by
  apply isTranslateValuationCompatible_of_ord_P_eq
  intro f hf
  exact translate_ord_eq_all_nonzero W P xk yk h_ns h f hf

/-- `IsTranslateValuationCompatible W P k h` for every `k` (the unconditional
discharge): `pointValuation P ∘ τ_k = pointValuation (P + k)` on `K(E)`. -/
theorem isTranslateValuationCompatible_all
    (P : (W_smooth W).SmoothPoint) (k : (W_smooth W).toAffine.Point)
    (h : (P.toAffinePoint + k).IsSome) :
    IsTranslateValuationCompatible W P k h := by
  apply isTranslateValuationCompatible_of_some_witness
  intro k' h_k'_ne h'
  rcases k' with _ | ⟨xk, yk, h_ns⟩
  · exact absurd rfl h_k'_ne
  · exact isTranslateValuationCompatible_some W P xk yk h_ns h'

end HasseWeil
