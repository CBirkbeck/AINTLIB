/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Hasse.PoleDivisorFallback

/-!
# Bridge at `addPullbackNumerator_negFrobenius` for 2-torsion (T-T21-2TORSION-BRIDGE)

The non-2-torsion bridge `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`
(`PoleDivisorFallback.lean:2353`) goes through `bridge_at_x_gen_of_non_2_tor`
(`PoleDivisorFallback.lean:606`), which uses
`ord_P_translateX_xy_eq_neg_two_of_non_2_tor` (`EC/TranslationOrd.lean:1379`)
as the substantive `= -2` identity at `−T` (with `T` non-2-torsion).

This file ships the **2-torsion analogue**:
`ord_P (translateX_xy W xT yT) = -2` at the smooth point `−T = T` (where
`−T = T` modulo `Nonsingular`-prop-irrelevance for 2-torsion), and
propagates it to the base bridges and the full
`bridge_at_addPullbackNumerator_negFrobenius` at 2-torsion.

The chain is:

* `ord_P_x_gen_sub_const_ge_two_at_2tor` — `ord_P (x_gen − xk) ≥ 2` from the
  curve identity `(y − yk)·A = (x − xk)·(B − a₁·yk)` at 2-torsion T with
  `ord_P (y − yk) = 1`, `ord_P A ≥ 1`, `ord_P (B − a₁·yk) = 0`.
* `ord_P_A_eq_one_at_2tor` — `ord_P A = 1` exactly via strict comparison
  `ord_P (y − yk) = 1 < 2 ≤ ord_P (a₁·(x − xk))` in `A = (y − yk) + a₁·(x − xk)`.
* `ord_P_translateSlope_xy_eq_neg_one_at_2tor` — `ord_P slope = −1` exactly
  via `slope = (B − a₁·yk) / A` with `ord = 0 − 1 = −1`.
* `ord_P_translateX_xy_eq_neg_two_at_2tor` — `ord_P translateX_xy = −2`
  exactly via `translateX_xy = slope² + rest` with strict comparison.
* `bridge_at_x_gen_of_2_tor` — bridge `ord_P (τ_{−T} x_gen) = ord_∞ x_gen`.
* `bridge_at_x_gen_pow_card_of_2_tor` — bridge for `x_gen^q`.
* `bridge_at_y_gen_of_2_tor` and `bridge_at_y_gen_pow_card_of_2_tor` —
  y-side analogues, derived via `translateY_xy` analysis.
* `bridge_at_addPullbackNumerator_negFrobenius_of_2_tor` — the full Num
  bridge at 2-torsion via the dominant-T7 strict comparison.

After this lands, the chain `T21 → T22 → T23 → T24` (L6 closer) is
unblocked: `support_card_eq_pointCount_of_two_torsion_ord_witness`
(`L6Witnesses.lean:497`) consumes the 2-torsion ord witness, and the
T22 composer becomes unconditional.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.1, III.2.
* `tickets/hasse/T-T21-2TORSION-BRIDGE.md` — the spawned sub-ticket.
* `EC/TranslationOrd.lean:2566+` — the 2-torsion `A`-factorisation and
  per-piece order bounds.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {K : Type*} [Field K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

section TwoTorBridges

variable [Fintype K]

local notation "KE" => W.toAffine.FunctionField

private lemma pi_x_gen_ne_zero_aux :
    (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact pow_ne_zero _ (x_gen_ne_zero W)

private lemma pi_y_gen_ne_zero_aux (hq : 2 ≤ Fintype.card K) :
    (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 := fun h_zero => by
  have h_top : (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (y_gen W)) = ⊤ := by
    rw [h_zero]; exact (W_smooth W).ordAtInfty_zero
  rw [ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq] at h_top
  exact WithTop.coe_ne_top h_top

set_option linter.unusedDecidableInType false in
omit [Fintype K] in
/-- **`ord_P (x_gen − xk) ≥ 2` at smooth 2-torsion `T`** via the curve
identity `(y − yk)·A = (x − xk)·(B − a₁·yk)` and the ord facts at
2-torsion. -/
theorem ord_P_x_gen_sub_const_ge_two_at_2tor (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) (h_2_tor : yk = W.toAffine.negY xk yk) :
    ((2 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap K KE xk) := by
  set P := negSmoothPoint W xk yk h_ns with hP_def
  have h_id := curve_identity_translate W xk yk h_ns.1
  have h_yd_ord : (W_smooth W).ord_P P (y_gen W - algebraMap K KE yk) =
      ((1 : ℤ) : WithTop ℤ) := by
    rw [show yk = W.toAffine.negY xk yk from h_2_tor]
    exact ord_P_y_gen_sub_negY_const_eq_one_of_2_tor W xk yk h_ns h_2_tor
  have h_A_ge : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃) :=
    one_le_ord_P_A_at_2tor W xk yk h_ns h_2_tor
  have h_Bma_ord : (W_smooth W).ord_P P
      (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
        algebraMap K KE xk ^ 2 +
        algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
        algebraMap K KE W.a₄ -
        algebraMap K KE W.a₁ * algebraMap K KE yk) = 0 :=
    ord_P_B_minus_a1_yk_eq_zero_at_2tor W xk yk h_ns h_2_tor
  have h_LHS_mul : (W_smooth W).ord_P P
      ((y_gen W - algebraMap K KE yk) *
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃)) =
      (W_smooth W).ord_P P (y_gen W - algebraMap K KE yk) +
      (W_smooth W).ord_P P
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃) :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  have h_LHS_ord : ((2 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P P
      ((y_gen W - algebraMap K KE yk) *
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃)) := by
    rw [h_LHS_mul, h_yd_ord]
    exact add_le_add (le_refl _) h_A_ge
  have h_RHS_ord : ((2 : ℤ) : WithTop ℤ) ≤ (W_smooth W).ord_P P
      ((x_gen W - algebraMap K KE xk) *
        (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
          algebraMap K KE xk ^ 2 +
          algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * algebraMap K KE yk)) := h_id ▸ h_LHS_ord
  have h_mul_eq : (W_smooth W).ord_P P
      ((x_gen W - algebraMap K KE xk) *
        (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
          algebraMap K KE xk ^ 2 +
          algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * algebraMap K KE yk)) =
      (W_smooth W).ord_P P (x_gen W - algebraMap K KE xk) +
        (W_smooth W).ord_P P
          (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
            algebraMap K KE xk ^ 2 +
            algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
            algebraMap K KE W.a₄ -
            algebraMap K KE W.a₁ * algebraMap K KE yk) :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  rw [h_mul_eq, h_Bma_ord, add_zero] at h_RHS_ord
  exact h_RHS_ord

set_option linter.unusedDecidableInType false in
omit [Fintype K] in
/-- **`ord_P A = 1` exactly at smooth 2-torsion `T`** via strict comparison
`ord_P (y − yk) = 1 < 2 ≤ ord_P (a₁·(x − xk))` in the factorisation
`A = (y − yk) + a₁·(x − xk)`. -/
theorem ord_P_A_eq_one_at_2tor (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃) =
      ((1 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns with hP_def
  rw [A_factorization_at_2tor W xk yk h_2_tor]
  have h_yd_ord : (W_smooth W).ord_P P (y_gen W - algebraMap K KE yk) =
      ((1 : ℤ) : WithTop ℤ) := by
    rw [show yk = W.toAffine.negY xk yk from h_2_tor]
    exact ord_P_y_gen_sub_negY_const_eq_one_of_2_tor W xk yk h_ns h_2_tor
  have h_xd_ge : ((2 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (x_gen W - algebraMap K KE xk) :=
    ord_P_x_gen_sub_const_ge_two_at_2tor W xk yk h_ns h_2_tor
  have h_a1_nonneg : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (algebraMap K KE W.a₁) :=
    ord_P_algebraMap_F_nonneg W P W.a₁
  have h_prod_eq : (W_smooth W).ord_P P
      (algebraMap K KE W.a₁ * (x_gen W - algebraMap K KE xk)) =
      (W_smooth W).ord_P P (algebraMap K KE W.a₁) +
        (W_smooth W).ord_P P (x_gen W - algebraMap K KE xk) :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  have h_prod_ge : ((2 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (algebraMap K KE W.a₁ * (x_gen W - algebraMap K KE xk)) := by
    rw [h_prod_eq]
    have h := add_le_add h_a1_nonneg h_xd_ge
    rwa [zero_add] at h
  have h_strict : (W_smooth W).ord_P P (y_gen W - algebraMap K KE yk) <
      (W_smooth W).ord_P P
        (algebraMap K KE W.a₁ * (x_gen W - algebraMap K KE xk)) := by
    rw [h_yd_ord]
    refine lt_of_lt_of_le ?_ h_prod_ge
    exact_mod_cast (show (1 : ℤ) < 2 by norm_num)
  have h_add := SmoothPlaneCurve.ord_P_add_eq_of_lt h_strict
  exact h_add.trans h_yd_ord

set_option linter.unusedDecidableInType false in
omit [Fintype K] in
/-- **`ord_P slope = -1` exactly at smooth 2-torsion `T`** via
`slope = (B − a₁·yk) / A` with `ord = 0 − 1 = −1` (using the
sharpened `ord_P A = 1`). -/
theorem ord_P_translateSlope_xy_eq_neg_one_at_2tor (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateSlope_xy W xk yk) = ((-1 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns with hP_def
  set Bma : KE := x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
      algebraMap K KE xk ^ 2 +
      algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
      algebraMap K KE W.a₄ -
      algebraMap K KE W.a₁ * algebraMap K KE yk with hBma_def
  set A : KE := y_gen W + algebraMap K KE yk +
      algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃ with hA_def
  have h_id : (y_gen W - algebraMap K KE yk) * A =
      (x_gen W - algebraMap K KE xk) * Bma := by
    rw [hA_def, hBma_def]
    exact curve_identity_translate W xk yk h_ns.1
  have h_A_ord : (W_smooth W).ord_P P A = ((1 : ℤ) : WithTop ℤ) := by
    rw [hA_def]; exact ord_P_A_eq_one_at_2tor W xk yk h_ns h_2_tor
  have h_Bma_ord : (W_smooth W).ord_P P Bma = 0 := by
    rw [hBma_def]; exact ord_P_B_minus_a1_yk_eq_zero_at_2tor W xk yk h_ns h_2_tor
  have h_x_ne : x_gen W - algebraMap K KE xk ≠ 0 :=
    x_gen_sub_const_ne_zero W xk
  have h_Bma_ne : Bma ≠ 0 := fun h_zero => by
    have h_top : (W_smooth W).ord_P P Bma = ⊤ :=
      (SmoothPlaneCurve.ord_P_eq_top_iff _).mpr h_zero
    rw [h_Bma_ord] at h_top
    simp at h_top
  have h_A_ne : A ≠ 0 := fun h_zero => by
    have h_top : (W_smooth W).ord_P P A = ⊤ :=
      (SmoothPlaneCurve.ord_P_eq_top_iff _).mpr h_zero
    rw [h_A_ord] at h_top
    simp at h_top
  have h_slope_eq : translateSlope_xy W xk yk = Bma / A := by
    rw [translateSlope_xy_eq, div_eq_div_iff h_x_ne h_A_ne]
    linear_combination h_id
  rw [h_slope_eq, div_eq_mul_inv]
  have h_mul : (W_smooth W).ord_P P (Bma * A⁻¹) =
      (W_smooth W).ord_P P Bma + (W_smooth W).ord_P P A⁻¹ :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  have h_inv : (W_smooth W).ord_P P A⁻¹ = -(W_smooth W).ord_P P A :=
    SmoothPlaneCurve.ord_P_inv (P := P) _ h_A_ne
  rw [h_mul, h_inv, h_Bma_ord, h_A_ord, zero_add]
  rfl

set_option linter.unusedDecidableInType false in
omit [Fintype K] in
/-- **`ord_P (translateX_xy) = -2` exactly at smooth 2-torsion `T`**:
`translateX_xy = slope² + (a₁·slope − a₂ − x_gen − xk)`. With
`ord_P slope = −1` exactly, `ord_P (slope²) = −2`, and the rest has
`ord_P ≥ −1 > −2`, strict comparison closes. -/
theorem ord_P_translateX_xy_eq_neg_two_at_2tor (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateX_xy W xk yk) = ((-2 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns with hP_def
  set s : KE := translateSlope_xy W xk yk with hs_def
  set rest : KE := (W_KE W).a₁ * s + (-(W_KE W).a₂ +
      -x_gen W + -algebraMap K KE xk) with hrest_def
  set sq2 : KE := s * s with hsq_def
  have h_s_ord : (W_smooth W).ord_P P s = ((-1 : ℤ) : WithTop ℤ) :=
    ord_P_translateSlope_xy_eq_neg_one_at_2tor W xk yk h_ns h_2_tor
  have h_s_ne : s ≠ 0 := fun h_zero => by
    have h_top : (W_smooth W).ord_P P s = ⊤ := by
      rw [h_zero]; exact SmoothPlaneCurve.ord_P_zero
    rw [h_s_ord] at h_top
    exact absurd h_top WithTop.coe_ne_top
  have h_sq_mul : (W_smooth W).ord_P P sq2 =
      (W_smooth W).ord_P P s + (W_smooth W).ord_P P s := by
    rw [hsq_def]
    exact SmoothPlaneCurve.ord_P_mul (P := P) s s
  have h_sq_ord : (W_smooth W).ord_P P sq2 = ((-2 : ℤ) : WithTop ℤ) := by
    rw [h_sq_mul, h_s_ord]
    rfl
  have h_W_KE_a1 : (W_KE W).a₁ = algebraMap K KE W.a₁ := rfl
  have h_W_KE_a2 : (W_KE W).a₂ = algebraMap K KE W.a₂ := rfl
  have h_a1s_ord : ((-1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P ((W_KE W).a₁ * s) := by
    rw [h_W_KE_a1]
    by_cases ha1 : W.a₁ = 0
    · have h_zero : algebraMap K KE W.a₁ * s = 0 := by
        rw [ha1, map_zero, zero_mul]
      have h_top : (W_smooth W).ord_P P (algebraMap K KE W.a₁ * s) = ⊤ := by
        rw [h_zero]; exact SmoothPlaneCurve.ord_P_zero
      rw [h_top]; exact le_top
    · have h_a1_ord : (W_smooth W).ord_P P (algebraMap K KE W.a₁) = 0 :=
        (W_smooth W).ord_P_algebraMap_F_of_ne_zero ha1 P
      have h_mul : (W_smooth W).ord_P P (algebraMap K KE W.a₁ * s) =
          (W_smooth W).ord_P P (algebraMap K KE W.a₁) +
          (W_smooth W).ord_P P s :=
        SmoothPlaneCurve.ord_P_mul (P := P) _ _
      rw [h_mul, h_a1_ord, zero_add, h_s_ord]
  have h_a2_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (-(W_KE W).a₂) := by
    rw [h_W_KE_a2]
    have h_neg : (W_smooth W).ord_P P (-algebraMap K KE W.a₂) =
        (W_smooth W).ord_P P (algebraMap K KE W.a₂) :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg]
    exact ord_P_algebraMap_F_nonneg W P W.a₂
  have h_xgen_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (-x_gen W) := by
    have h_neg : (W_smooth W).ord_P P (-x_gen W) =
        (W_smooth W).ord_P P (x_gen W) :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg]
    exact ord_P_x_gen_nonneg W P
  have h_xk_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (-algebraMap K KE xk) := by
    have h_neg : (W_smooth W).ord_P P (-algebraMap K KE xk) =
        (W_smooth W).ord_P P (algebraMap K KE xk) :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg]
    exact ord_P_algebraMap_F_nonneg W P xk
  have h_const_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (-(W_KE W).a₂ + -x_gen W + -algebraMap K KE xk) := by
    have h12 := SmoothPlaneCurve.ord_P_add_le (P := P)
      (-(W_KE W).a₂) (-x_gen W)
    have h12' : (0 : WithTop ℤ) ≤
        (W_smooth W).ord_P P (-(W_KE W).a₂ + -x_gen W) :=
      le_trans (le_min h_a2_nn h_xgen_nn) h12
    have h123 := SmoothPlaneCurve.ord_P_add_le (P := P)
      (-(W_KE W).a₂ + -x_gen W) (-algebraMap K KE xk)
    exact le_trans (le_min h12' h_xk_nn) h123
  have h_const_ge_neg_one : ((-1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (-(W_KE W).a₂ + -x_gen W + -algebraMap K KE xk) := by
    refine le_trans ?_ h_const_nn
    exact_mod_cast (show (-1 : ℤ) ≤ 0 by norm_num)
  have h_rest_ord : ((-1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P rest := by
    rw [hrest_def]
    have h_sum := SmoothPlaneCurve.ord_P_add_le (P := P)
      ((W_KE W).a₁ * s)
      (-(W_KE W).a₂ + -x_gen W + -algebraMap K KE xk)
    exact le_trans (le_min h_a1s_ord h_const_ge_neg_one) h_sum
  have h_lt : (W_smooth W).ord_P P sq2 < (W_smooth W).ord_P P rest := by
    rw [h_sq_ord]
    refine lt_of_lt_of_le ?_ h_rest_ord
    exact_mod_cast (show (-2 : ℤ) < -1 by norm_num)
  have h_unfold : translateX_xy W xk yk = sq2 + rest := by
    change translateX_xy W xk yk = s * s +
      ((W_KE W).a₁ * s + (-(W_KE W).a₂ +
        -x_gen W + -algebraMap K KE xk))
    unfold translateX_xy
    rw [WeierstrassCurve.Affine.addX]
    ring
  rw [h_unfold]
  have h_add := SmoothPlaneCurve.ord_P_add_eq_of_lt h_lt
  exact h_add.trans h_sq_ord

set_option linter.unusedDecidableInType false in
/-- **Bridge at `x_gen` for 2-torsion `T`** (the y-side analogue of
`ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two` for non-2-torsion):
at the smooth point `T` (= `−T` modulo prop-irrelevance, since 2T = 0),
`ord_P T (τ_{−T} (x_gen)) = -2`.

Composes `ord_P_translateX_xy_eq_neg_two_at_2tor` with
`translateAlgEquivOfPoint_some_apply_x_gen` and the negation-involution
identity at the SmoothPoint level. -/
theorem ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two_at_2tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W)) = ((-2 : ℤ) : WithTop ℤ) := by
  rw [neg_some_eq_some W xT yT h_ns]
  rw [translateAlgEquivOfPoint_some_apply_x_gen W xT (W.toAffine.negY xT yT)
    ((Affine.nonsingular_neg xT yT).mpr h_ns)]
  have h_negY_negY : W.toAffine.negY xT (W.toAffine.negY xT yT) = yT :=
    W.toAffine.negY_negY xT yT
  have h_2_tor_neg : W.toAffine.negY xT yT =
      W.toAffine.negY xT (W.toAffine.negY xT yT) := by
    rw [h_negY_negY]
    exact h_2_tor.symm
  have h_ord : (W_smooth W).ord_P
      (negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns))
      (translateX_xy W xT (W.toAffine.negY xT yT)) = ((-2 : ℤ) : WithTop ℤ) :=
    ord_P_translateX_xy_eq_neg_two_at_2tor W xT (W.toAffine.negY xT yT)
      ((Affine.nonsingular_neg xT yT).mpr h_ns) h_2_tor_neg
  have h_smoothPt_eq :
      negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns) =
      ({ x := xT, y := yT, nonsingular := h_ns } :
        (W_smooth W).SmoothPoint) := by
    apply Curves.SmoothPlaneCurve.SmoothPoint.ext
    · rfl
    · exact h_negY_negY
  rw [← h_smoothPt_eq]
  exact h_ord

/-- **Bridge at `f = x_gen` for 2-torsion `T`** (clean version): the analog of
`bridge_at_x_gen_of_non_2_tor` for 2-torsion. Composes the 2-torsion `ord_T`
value with the shipped `ordAtInfty_x_gen = -2`. -/
theorem bridge_at_x_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W) := by
  rw [ord_T_translateAlgEquivOfPoint_neg_x_gen_eq_neg_two_at_2tor W xT yT h_ns h_2_tor]
  rw [show ((W_smooth W).ordAtInfty (x_gen W)) = ((-2 : ℤ) : WithTop ℤ) from
    ordAtInfty_x_gen W]

/-- **Bridge at `f = x_gen^q` for 2-torsion `T`**: composes the 2-tor x_gen base
bridge with the generic `ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base`
to lift to `x_gen^q`. Analog of `bridge_at_x_gen_pow_card_of_non_2_tor`. -/
theorem bridge_at_x_gen_pow_card_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) :=
  ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ (x_gen W) (x_gen_ne_zero W)
    (bridge_at_x_gen_of_2_tor W xT yT h_ns h_2_tor) (Fintype.card K)

/-- **Bridge at `f = x_gen^q - x_gen` for 2-torsion `T`**: composes the strict-
comparison sub theorem with the bridges for `x_gen^q` and `x_gen` at 2-torsion,
using the strict inequality from `ordAtInfty_x_gen_pow_card_lt_x_gen`.
Analog of `bridge_at_x_gen_pow_card_sub_x_gen_of_non_2_tor`. -/
theorem bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W ^ Fintype.card K - x_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K - x_gen W) :=
  ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_x_gen_pow_card_of_2_tor W xT yT h_ns h_2_tor)
    (bridge_at_x_gen_of_2_tor W xT yT h_ns h_2_tor)
    (Conditional.ordAtInfty_x_gen_pow_card_lt_x_gen W hq)

/-- **Bridge at `f = x_gen - x_gen^q` for 2-torsion `T`**: applies the neg-bridge
to `bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor`. Mirrors
`bridge_at_x_gen_sub_x_gen_pow_card_of_non_2_tor`. -/
theorem bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W - x_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (x_gen W - x_gen W ^ Fintype.card K) := by
  have h_eq : x_gen W - x_gen W ^ Fintype.card K =
      -(x_gen W ^ Fintype.card K - x_gen W) := by ring
  rw [h_eq]
  exact ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
    W _ _ _
    (bridge_at_x_gen_pow_card_sub_x_gen_of_2_tor W xT yT h_ns h_2_tor hq)

/-- **Bridge at `(negFrobeniusIsog W).pullback x_gen` for 2-torsion `T`**:
direct corollary of `bridge_at_x_gen_pow_card_of_2_tor` via the identity
`negFrobeniusIsog.pullback x_gen = x_gen^q`. Mirrors
`bridge_at_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`. -/
theorem bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact bridge_at_x_gen_pow_card_of_2_tor W xT yT h_ns h_2_tor

/-- **Bridge at the slope denominator `x_gen − negFrob.pullback x_gen`** for
2-torsion `T`. Mirrors `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_non_2_tor`. -/
theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  exact bridge_at_x_gen_sub_x_gen_pow_card_of_2_tor W xT yT h_ns h_2_tor hq

/-- **Bridge at `(x_gen - (negFrob).pullback x_gen)^2` (slope-denominator squared)**
for 2-torsion `T`. Pow on the just-shipped bridge for `x_gen - negFrob.pullback x_gen`.
Mirrors `bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`. -/
theorem bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2)) =
      (W_smooth W).ordAtInfty
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) :=
  ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ _
    (x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W)
    (bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_of_2_tor
      W xT yT h_ns h_2_tor hq) 2

/-- **Bridge at `((negFrob).pullback x_gen)^2` for 2-torsion `T`**: pow on
the just-shipped bridge for `(negFrob).pullback x_gen`. Mirrors the non-2-tor
version (`bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`). -/
theorem bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (x_gen W) ^ 2)) =
      (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) := by
  have h_pix_ne := pi_x_gen_ne_zero_aux W
  exact ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ _ h_pix_ne
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor W xT yT h_ns h_2_tor) 2

/-- **Bridge at T7 = `x_gen · ((negFrob).pullback x_gen)^2`** (the dominant
term of the reduced numerator) for 2-torsion `T`: mul on bridges for `x_gen`
and `((negFrob).pullback x_gen)^2`. -/
theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2)) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) := by
  have h_pix_sq_ne : (negFrobeniusIsog W).pullback (x_gen W) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (pi_x_gen_ne_zero_aux W)
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W ⟨xT, yT, h_ns⟩ _ _ _ (x_gen_ne_zero W) h_pix_sq_ne
    (bridge_at_x_gen_of_2_tor W xT yT h_ns h_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor W xT yT h_ns h_2_tor)

/-- **Bridge at T6 = `x_gen² · (negFrob).pullback x_gen`** for 2-torsion `T`:
mul on bridges for `x_gen²` (pow) and `(negFrob).pullback x_gen` (shipped). -/
theorem bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_x_sq_ne : x_gen W ^ 2 ≠ 0 := pow_ne_zero _ (x_gen_ne_zero W)
  have h_pix_ne := pi_x_gen_ne_zero_aux W
  have h_x_sq_bridge : (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
      (translateAlgEquivOfPoint W
        (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point) (x_gen W ^ 2)) =
      (W_smooth W).ordAtInfty (x_gen W ^ 2) :=
    ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
      W _ _ _ (x_gen_ne_zero W)
      (bridge_at_x_gen_of_2_tor W xT yT h_ns h_2_tor) 2
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ h_x_sq_ne h_pix_ne h_x_sq_bridge
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor W xT yT h_ns h_2_tor)

/-- **Bridge at `x_gen · (negFrob).pullback x_gen`** (occurring in T1 and T8) for
2-torsion `T`: mul on bridges for `x_gen` and `(negFrob).pullback x_gen`. -/
theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  have h_pix_ne := pi_x_gen_ne_zero_aux W
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W ⟨xT, yT, h_ns⟩ _ _ _ (x_gen_ne_zero W) h_pix_ne
    (bridge_at_x_gen_of_2_tor W xT yT h_ns h_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor W xT yT h_ns h_2_tor)

set_option linter.unusedDecidableInType false in
omit [Fintype K] in
/-- **`ord_P (x_gen − xk) = 2` EXACTLY at smooth 2-torsion `T`** via the curve
identity `(y − yk)·A = (x − xk)·(B − a₁·yk)` with the EXACT `ord_P A = 1`
(shipped at `ord_P_A_eq_one_at_2tor`) and `ord_P (B − a₁·yk) = 0` (shipped at
`ord_P_B_minus_a1_yk_eq_zero_at_2tor`). Tightens the shipped `≥ 2` to equality. -/
theorem ord_P_x_gen_sub_const_eq_two_at_2tor (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (x_gen W - algebraMap K KE xk) = ((2 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns with hP_def
  have h_id := curve_identity_translate W xk yk h_ns.1
  have h_yd_ord : (W_smooth W).ord_P P (y_gen W - algebraMap K KE yk) =
      ((1 : ℤ) : WithTop ℤ) := by
    rw [show yk = W.toAffine.negY xk yk from h_2_tor]
    exact ord_P_y_gen_sub_negY_const_eq_one_of_2_tor W xk yk h_ns h_2_tor
  have h_A_eq : (W_smooth W).ord_P P
      (y_gen W + algebraMap K KE yk +
        algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃) =
      ((1 : ℤ) : WithTop ℤ) :=
    ord_P_A_eq_one_at_2tor W xk yk h_ns h_2_tor
  have h_Bma_ord : (W_smooth W).ord_P P
      (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
        algebraMap K KE xk ^ 2 +
        algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
        algebraMap K KE W.a₄ -
        algebraMap K KE W.a₁ * algebraMap K KE yk) = 0 :=
    ord_P_B_minus_a1_yk_eq_zero_at_2tor W xk yk h_ns h_2_tor
  have h_LHS_mul : (W_smooth W).ord_P P
      ((y_gen W - algebraMap K KE yk) *
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃)) =
      (W_smooth W).ord_P P (y_gen W - algebraMap K KE yk) +
      (W_smooth W).ord_P P
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃) :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  have h_LHS_ord : (W_smooth W).ord_P P
      ((y_gen W - algebraMap K KE yk) *
        (y_gen W + algebraMap K KE yk +
          algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃)) =
      ((2 : ℤ) : WithTop ℤ) := by
    rw [h_LHS_mul, h_yd_ord, h_A_eq]; rfl
  have h_RHS_ord : (W_smooth W).ord_P P
      ((x_gen W - algebraMap K KE xk) *
        (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
          algebraMap K KE xk ^ 2 +
          algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * algebraMap K KE yk)) =
      ((2 : ℤ) : WithTop ℤ) := h_id ▸ h_LHS_ord
  have h_mul_eq : (W_smooth W).ord_P P
      ((x_gen W - algebraMap K KE xk) *
        (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
          algebraMap K KE xk ^ 2 +
          algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * algebraMap K KE yk)) =
      (W_smooth W).ord_P P (x_gen W - algebraMap K KE xk) +
        (W_smooth W).ord_P P
          (x_gen W ^ 2 + x_gen W * algebraMap K KE xk +
            algebraMap K KE xk ^ 2 +
            algebraMap K KE W.a₂ * (x_gen W + algebraMap K KE xk) +
            algebraMap K KE W.a₄ -
            algebraMap K KE W.a₁ * algebraMap K KE yk) :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  rw [h_mul_eq, h_Bma_ord, add_zero] at h_RHS_ord
  exact h_RHS_ord

omit [Fintype K] in
/-- Nonnegativity of `ord_P` of the `T3` coefficient `yd·(a₂ + 2x + xk') − a₁²·yd`, given the basic
order data.  Extracted from `ord_P_translateY_xy_eq_neg_three_at_2tor` to keep its per-term `ord_P`
bound bookkeeping under the default heartbeat budget. -/
theorem ord_P_translateY_T3_coef_nonneg
    {P : (W_smooth W).SmoothPoint} {yd a1 a2 xk' : KE}
    (h_yd_ord : (W_smooth W).ord_P P yd = ((1 : ℤ) : WithTop ℤ))
    (h_xg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W))
    (h_a1_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a1)
    (h_a2_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a2)
    (h_xk_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P xk') :
    (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (yd * (a2 + (2 : KE) * x_gen W + xk') - a1 ^ 2 * yd) := by
  have h_mul1 : (W_smooth W).ord_P P (yd * (a2 + (2 : KE) * x_gen W + xk')) =
      (W_smooth W).ord_P P yd +
        (W_smooth W).ord_P P (a2 + (2 : KE) * x_gen W + xk') :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  have h_sum_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (a2 + (2 : KE) * x_gen W + xk') := by
    have h12 : min ((W_smooth W).ord_P P a2)
          ((W_smooth W).ord_P P ((2 : KE) * x_gen W)) ≤
        (W_smooth W).ord_P P (a2 + (2 : KE) * x_gen W) :=
      SmoothPlaneCurve.ord_P_add_le (P := P) _ _
    have h_2x_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P ((2 : KE) * x_gen W) := by
      have h_mul : (W_smooth W).ord_P P ((2 : KE) * x_gen W) =
          (W_smooth W).ord_P P (2 : KE) +
            (W_smooth W).ord_P P (x_gen W) :=
        SmoothPlaneCurve.ord_P_mul (P := P) _ _
      rw [h_mul]
      have h_two_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (2 : KE) := by
        have h_two_eq : (2 : KE) = algebraMap K KE 2 := by rw [map_ofNat]
        rw [h_two_eq]; exact ord_P_algebraMap_F_nonneg W P 2
      calc (0 : WithTop ℤ) = 0 + 0 := by rw [zero_add]
        _ ≤ (W_smooth W).ord_P P (2 : KE) +
              (W_smooth W).ord_P P (x_gen W) := add_le_add h_two_nn h_xg_nn
    have h12' : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (a2 + (2 : KE) * x_gen W) :=
      (le_min h_a2_nn h_2x_nn).trans h12
    have h123 : min ((W_smooth W).ord_P P (a2 + (2 : KE) * x_gen W))
          ((W_smooth W).ord_P P xk') ≤
        (W_smooth W).ord_P P (a2 + (2 : KE) * x_gen W + xk') :=
      SmoothPlaneCurve.ord_P_add_le (P := P) _ _
    exact (le_min h12' h_xk_nn).trans h123
  have h_mul1' : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (yd * (a2 + (2 : KE) * x_gen W + xk')) := by
    rw [h_mul1, h_yd_ord]
    calc ((1 : ℤ) : WithTop ℤ) = ((1 : ℤ) : WithTop ℤ) + 0 := by rw [add_zero]
      _ ≤ ((1 : ℤ) : WithTop ℤ) +
            (W_smooth W).ord_P P (a2 + (2 : KE) * x_gen W + xk') :=
          add_le_add (le_refl _) h_sum_nn
  have h_mul2 : (W_smooth W).ord_P P (a1 ^ 2 * yd) =
      (W_smooth W).ord_P P (a1 ^ 2) + (W_smooth W).ord_P P yd :=
    SmoothPlaneCurve.ord_P_mul (P := P) _ _
  have h_a1sq_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (a1 ^ 2) := by
    have h_pow : (W_smooth W).ord_P P (a1 ^ 2) =
        (2 : ℕ) • (W_smooth W).ord_P P a1 :=
      SmoothPlaneCurve.ord_P_pow (P := P) a1 2
    rw [h_pow]
    calc (0 : WithTop ℤ) = (2 : ℕ) • (0 : WithTop ℤ) := by simp
      _ ≤ (2 : ℕ) • (W_smooth W).ord_P P a1 := nsmul_le_nsmul_right h_a1_nn 2
  have h_a1sq_yd_le_one : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (a1 ^ 2 * yd) := by
    rw [h_mul2, h_yd_ord]
    calc ((1 : ℤ) : WithTop ℤ) = 0 + ((1 : ℤ) : WithTop ℤ) := by rw [zero_add]
      _ ≤ (W_smooth W).ord_P P (a1 ^ 2) + ((1 : ℤ) : WithTop ℤ) :=
          add_le_add h_a1sq_nn (le_refl _)
  have h_neg_a1sq_yd_le_one : ((1 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (-(a1 ^ 2 * yd)) := by
    have h_neg_eq : (W_smooth W).ord_P P (-(a1 ^ 2 * yd)) =
        (W_smooth W).ord_P P (a1 ^ 2 * yd) :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg_eq]; exact h_a1sq_yd_le_one
  change (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P
      (yd * (a2 + (2 : KE) * x_gen W + xk') + -(a1 ^ 2 * yd))
  have h_add := SmoothPlaneCurve.ord_P_add_le (P := P)
    (yd * (a2 + (2 : KE) * x_gen W + xk')) (-(a1 ^ 2 * yd))
  have h_min_ge_zero : (0 : WithTop ℤ) ≤
      min ((W_smooth W).ord_P P (yd * (a2 + (2 : KE) * x_gen W + xk')))
          ((W_smooth W).ord_P P (-(a1 ^ 2 * yd))) := by
    apply le_min
    · exact le_trans (by exact_mod_cast (show (0 : ℤ) ≤ 1 by norm_num)) h_mul1'
    · exact le_trans (by exact_mod_cast (show (0 : ℤ) ≤ 1 by norm_num))
        h_neg_a1sq_yd_le_one
  exact h_min_ge_zero.trans h_add

omit [Fintype K] in
/-- Nonnegativity of `ord_P` of the `T4` coefficient `−y + a₁·(a₂ + x + xk') − a₃`, given the basic
order data.  Extracted from `ord_P_translateY_xy_eq_neg_three_at_2tor` to keep its per-term `ord_P`
bound bookkeeping under the default heartbeat budget. -/
theorem ord_P_translateY_T4_coef_nonneg
    {P : (W_smooth W).SmoothPoint} {a1 a2 a3 xk' : KE}
    (h_xg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W))
    (h_yg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (y_gen W))
    (h_a1_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a1)
    (h_a2_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a2)
    (h_a3_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a3)
    (h_xk_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P xk') :
    (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) := by
  have h_neg_yg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (-y_gen W) := by
    have h_neg_eq : (W_smooth W).ord_P P (-y_gen W) =
        (W_smooth W).ord_P P (y_gen W) :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg_eq]; exact h_yg_nn
  have h_a2xxk_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (a2 + x_gen W + xk') := by
    have h12 : min ((W_smooth W).ord_P P a2) ((W_smooth W).ord_P P (x_gen W)) ≤
        (W_smooth W).ord_P P (a2 + x_gen W) :=
      SmoothPlaneCurve.ord_P_add_le (P := P) _ _
    have h12' : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (a2 + x_gen W) :=
      (le_min h_a2_nn h_xg_nn).trans h12
    have h123 : min ((W_smooth W).ord_P P (a2 + x_gen W))
          ((W_smooth W).ord_P P xk') ≤
        (W_smooth W).ord_P P (a2 + x_gen W + xk') :=
      SmoothPlaneCurve.ord_P_add_le (P := P) _ _
    exact (le_min h12' h_xk_nn).trans h123
  have h_a1mul_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (a1 * (a2 + x_gen W + xk')) := by
    have h_mul : (W_smooth W).ord_P P (a1 * (a2 + x_gen W + xk')) =
        (W_smooth W).ord_P P a1 +
          (W_smooth W).ord_P P (a2 + x_gen W + xk') :=
      SmoothPlaneCurve.ord_P_mul (P := P) _ _
    rw [h_mul]
    calc (0 : WithTop ℤ) = 0 + 0 := by rw [zero_add]
      _ ≤ (W_smooth W).ord_P P a1 +
            (W_smooth W).ord_P P (a2 + x_gen W + xk') :=
          add_le_add h_a1_nn h_a2xxk_nn
  have h_neg_a3_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (-a3) := by
    have h_neg_eq : (W_smooth W).ord_P P (-a3) =
        (W_smooth W).ord_P P a3 :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg_eq]; exact h_a3_nn
  have h12 : min ((W_smooth W).ord_P P (-y_gen W))
        ((W_smooth W).ord_P P (a1 * (a2 + x_gen W + xk'))) ≤
      (W_smooth W).ord_P P (-y_gen W + a1 * (a2 + x_gen W + xk')) :=
    SmoothPlaneCurve.ord_P_add_le (P := P) _ _
  have h12' : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P (-y_gen W + a1 * (a2 + x_gen W + xk')) :=
    (le_min h_neg_yg_nn h_a1mul_nn).trans h12
  have h_diff_eq : -y_gen W + a1 * (a2 + x_gen W + xk') - a3 =
      -y_gen W + a1 * (a2 + x_gen W + xk') + (-a3) := by ring
  rw [h_diff_eq]
  have h123 : min ((W_smooth W).ord_P P (-y_gen W + a1 * (a2 + x_gen W + xk')))
        ((W_smooth W).ord_P P (-a3)) ≤
      (W_smooth W).ord_P P
        (-y_gen W + a1 * (a2 + x_gen W + xk') + (-a3)) :=
    SmoothPlaneCurve.ord_P_add_le (P := P) _ _
  exact (le_min h12' h_neg_a3_nn).trans h123

set_option linter.unusedDecidableInType false in
omit [Fintype K] in
/-- **`ord_P (translateY_xy) = -3` at smooth 2-torsion `T`** via the algebraic
identity `translateY_xy_mul_cube_eq` and the 2-tor ord values
`ord_P (yd) = 1` (shipped at `ord_P_y_gen_sub_negY_const_eq_one_of_2_tor`)
+ `ord_P (xd) = 2` exactly (shipped at `ord_P_x_gen_sub_const_eq_two_at_2tor`).
At 2-tor the RHS dominant is `-yd³` with ord = 3, all other RHS terms have
ord ≥ 4 (strict); LHS = `translateY · xd³` has ord = `ord(translateY) + 6`,
forcing `ord(translateY) = -3`. Mirrors the non-2-tor proof at
`EC/TranslationOrd.lean:1536`. -/
theorem ord_P_translateY_xy_eq_neg_three_at_2tor (xk yk : K)
    (h_ns : W.toAffine.Nonsingular xk yk) (h_2_tor : yk = W.toAffine.negY xk yk) :
    (W_smooth W).ord_P (negSmoothPoint W xk yk h_ns)
        (translateY_xy W xk yk) = ((-3 : ℤ) : WithTop ℤ) := by
  set P := negSmoothPoint W xk yk h_ns with hP_def
  set yd := y_gen W - algebraMap K KE yk with hyd_def
  set xd := x_gen W - algebraMap K KE xk with hxd_def
  set a1 := algebraMap K KE W.a₁ with ha1_def
  set a2 := algebraMap K KE W.a₂ with ha2_def
  set a3 := algebraMap K KE W.a₃ with ha3_def
  set xk' := algebraMap K KE xk with hxk'_def
  have h_xd_ne : xd ≠ 0 := x_gen_sub_const_ne_zero W xk
  have h_xd_ord_eq : (W_smooth W).ord_P P xd = ((2 : ℤ) : WithTop ℤ) := by
    rw [hxd_def]
    exact ord_P_x_gen_sub_const_eq_two_at_2tor W xk yk h_ns h_2_tor
  have h_yd_ord : (W_smooth W).ord_P P yd = ((1 : ℤ) : WithTop ℤ) := by
    rw [hyd_def, show yk = W.toAffine.negY xk yk from h_2_tor]
    exact ord_P_y_gen_sub_negY_const_eq_one_of_2_tor W xk yk h_ns h_2_tor
  have h_xg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (x_gen W) :=
    ord_P_x_gen_nonneg W P
  have h_a1_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a1 :=
    ord_P_algebraMap_F_nonneg W P W.a₁
  have h_a2_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a2 :=
    ord_P_algebraMap_F_nonneg W P W.a₂
  have h_a3_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P a3 :=
    ord_P_algebraMap_F_nonneg W P W.a₃
  have h_xk_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P xk' :=
    ord_P_algebraMap_F_nonneg W P xk
  have h_yg_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (y_gen W) := by
    by_cases hf : y_gen W = 0
    · rw [hf]
      rw [show ((W_smooth W).ord_P P (0 : KE)) = ⊤ from
          SmoothPlaneCurve.ord_P_zero]
      exact le_top
    · have h_v_le : (W_smooth W).pointValuation P (y_gen W) ≤ 1 :=
        pointValuation_y_gen_le_one W P
      have hv : (W_smooth W).pointValuation P (y_gen W) ≠ 0 :=
        ((W_smooth W).pointValuation P).ne_zero_iff.mpr hf
      unfold SmoothPlaneCurve.ord_P
      rw [dif_neg hv]
      rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
          WithTop.coe_le_coe]
      have h_unz_le : WithZero.unzero hv ≤ 1 := by
        rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]
        exact h_v_le
      have h_toAdd : (WithZero.unzero hv).toAdd ≤ 0 := by
        have h1 : ((1 : Multiplicative ℤ)).toAdd = (0 : ℤ) := rfl
        have h2 : Multiplicative.toAdd (WithZero.unzero hv) ≤
            Multiplicative.toAdd (1 : Multiplicative ℤ) := h_unz_le
        rw [h1] at h2; exact h2
      omega
  -- ord(yd^3) = 3 (at 2-tor — replaces non-2-tor's = 0).
  have h_yd_cube : (W_smooth W).ord_P P (yd^3) = ((3 : ℤ) : WithTop ℤ) := by
    have h_pow : (W_smooth W).ord_P P (yd^3) =
        (3 : ℕ) • (W_smooth W).ord_P P yd :=
      SmoothPlaneCurve.ord_P_pow (P := P) yd 3
    rw [h_pow, h_yd_ord]; rfl
  have h_yd_sq : (W_smooth W).ord_P P (yd^2) = ((2 : ℤ) : WithTop ℤ) := by
    have h_pow : (W_smooth W).ord_P P (yd^2) =
        (2 : ℕ) • (W_smooth W).ord_P P yd :=
      SmoothPlaneCurve.ord_P_pow (P := P) yd 2
    rw [h_pow, h_yd_ord]; rfl
  have h_xd_sq_eq : (W_smooth W).ord_P P (xd^2) = ((4 : ℤ) : WithTop ℤ) := by
    have h_pow : (W_smooth W).ord_P P (xd^2) =
        (2 : ℕ) • (W_smooth W).ord_P P xd :=
      SmoothPlaneCurve.ord_P_pow (P := P) xd 2
    rw [h_pow, h_xd_ord_eq]; rfl
  have h_xd_cube_eq : (W_smooth W).ord_P P (xd^3) = ((6 : ℤ) : WithTop ℤ) := by
    have h_pow : (W_smooth W).ord_P P (xd^3) =
        (3 : ℕ) • (W_smooth W).ord_P P xd :=
      SmoothPlaneCurve.ord_P_pow (P := P) xd 3
    rw [h_pow, h_xd_ord_eq]; rfl
  -- T2 = -2·a1·yd²·xd, ord ≥ 4 at 2-tor (vs ≥ 1 at non-2-tor).
  have h_T2 : ((4 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P (-((2 : KE) * a1 * yd^2 * xd)) := by
    have h_neg : (W_smooth W).ord_P P (-((2 : KE) * a1 * yd^2 * xd)) =
        (W_smooth W).ord_P P ((2 : KE) * a1 * yd^2 * xd) :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg]
    have h_mul₁ : (W_smooth W).ord_P P ((2 : KE) * a1 * yd^2 * xd) =
        (W_smooth W).ord_P P ((2 : KE) * a1 * yd^2) +
          (W_smooth W).ord_P P xd :=
      SmoothPlaneCurve.ord_P_mul (P := P) _ _
    have h_mul₂ : (W_smooth W).ord_P P ((2 : KE) * a1 * yd^2) =
        (W_smooth W).ord_P P ((2 : KE) * a1) +
          (W_smooth W).ord_P P (yd^2) :=
      SmoothPlaneCurve.ord_P_mul (P := P) _ _
    rw [h_mul₁, h_mul₂, h_yd_sq, h_xd_ord_eq]
    have h_2a1_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P ((2 : KE) * a1) := by
      have h_mul : (W_smooth W).ord_P P ((2 : KE) * a1) =
          (W_smooth W).ord_P P (2 : KE) +
            (W_smooth W).ord_P P a1 :=
        SmoothPlaneCurve.ord_P_mul (P := P) _ _
      rw [h_mul]
      have h_two_nn : (0 : WithTop ℤ) ≤ (W_smooth W).ord_P P (2 : KE) := by
        have h_two_eq : (2 : KE) = algebraMap K KE 2 := by rw [map_ofNat]
        rw [h_two_eq]
        exact ord_P_algebraMap_F_nonneg W P 2
      calc (0 : WithTop ℤ)
          = 0 + 0 := by rw [zero_add]
        _ ≤ (W_smooth W).ord_P P (2 : KE) +
              (W_smooth W).ord_P P a1 :=
            add_le_add h_two_nn h_a1_nn
    have h_assoc : (W_smooth W).ord_P P ((2 : KE) * a1) +
        ((2 : ℤ) : WithTop ℤ) + ((2 : ℤ) : WithTop ℤ) =
        (W_smooth W).ord_P P ((2 : KE) * a1) +
          (((2 : ℤ) : WithTop ℤ) + ((2 : ℤ) : WithTop ℤ)) :=
      add_assoc _ _ _
    rw [h_assoc]
    calc ((4 : ℤ) : WithTop ℤ)
        = 0 + (((2 : ℤ) : WithTop ℤ) + ((2 : ℤ) : WithTop ℤ)) := by rfl
      _ ≤ (W_smooth W).ord_P P ((2 : KE) * a1) +
            (((2 : ℤ) : WithTop ℤ) + ((2 : ℤ) : WithTop ℤ)) :=
          add_le_add h_2a1_nn (le_refl _)
  have h_T3_coef_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) :=
    ord_P_translateY_T3_coef_nonneg W h_yd_ord h_xg_nn h_a1_nn h_a2_nn h_xk_nn
  have h_T3 : ((4 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2) := by
    have h_mul : (W_smooth W).ord_P P
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2) =
        (W_smooth W).ord_P P (yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) +
          (W_smooth W).ord_P P (xd^2) :=
      SmoothPlaneCurve.ord_P_mul (P := P) _ _
    rw [h_mul, h_xd_sq_eq]
    calc ((4 : ℤ) : WithTop ℤ) = 0 + ((4 : ℤ) : WithTop ℤ) := by rw [zero_add]
      _ ≤ (W_smooth W).ord_P P (yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) +
            ((4 : ℤ) : WithTop ℤ) :=
          add_le_add h_T3_coef_nn (le_refl _)
  have h_T4_coef_nn : (0 : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) :=
    ord_P_translateY_T4_coef_nonneg W h_xg_nn h_yg_nn h_a1_nn h_a2_nn h_a3_nn h_xk_nn
  have h_T4 : ((6 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        ((-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3) := by
    have h_mul : (W_smooth W).ord_P P
          ((-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3) =
        (W_smooth W).ord_P P (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) +
          (W_smooth W).ord_P P (xd^3) :=
      SmoothPlaneCurve.ord_P_mul (P := P) _ _
    rw [h_mul, h_xd_cube_eq]
    calc ((6 : ℤ) : WithTop ℤ) = 0 + ((6 : ℤ) : WithTop ℤ) := by rw [zero_add]
      _ ≤ (W_smooth W).ord_P P (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) +
            ((6 : ℤ) : WithTop ℤ) :=
          add_le_add h_T4_coef_nn (le_refl _)
  -- ord(-yd³) = 3 (at 2-tor, this is the DOMINANT term).
  have h_neg_yd_cube : (W_smooth W).ord_P P (-(yd^3)) = ((3 : ℤ) : WithTop ℤ) := by
    have h_neg_eq : (W_smooth W).ord_P P (-(yd^3)) =
        (W_smooth W).ord_P P (yd^3) :=
      SmoothPlaneCurve.ord_P_neg (P := P) _
    rw [h_neg_eq]; exact h_yd_cube
  have h_T234 : ((4 : ℤ) : WithTop ℤ) ≤
      (W_smooth W).ord_P P
        (-((2 : KE) * a1 * yd^2 * xd) +
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
            (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3)) := by
    have h_T34_le_four : ((4 : ℤ) : WithTop ℤ) ≤
        (W_smooth W).ord_P P
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
            (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3) := by
      have h_T4_le_four : ((4 : ℤ) : WithTop ℤ) ≤
          (W_smooth W).ord_P P
            ((-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3) :=
        le_trans (by exact_mod_cast (show (4 : ℤ) ≤ 6 by norm_num)) h_T4
      have h_add := SmoothPlaneCurve.ord_P_add_le (P := P)
        ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2)
        ((-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3)
      exact (le_min h_T3 h_T4_le_four).trans h_add
    have h_add := SmoothPlaneCurve.ord_P_add_le (P := P)
      (-((2 : KE) * a1 * yd^2 * xd))
      ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
        (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3)
    exact (le_min h_T2 h_T34_le_four).trans h_add
  have h_strict : (W_smooth W).ord_P P (-(yd^3)) <
      (W_smooth W).ord_P P
        (-((2 : KE) * a1 * yd^2 * xd) +
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
            (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3)) := by
    rw [h_neg_yd_cube]
    exact lt_of_lt_of_le (by exact_mod_cast (show (3 : ℤ) < 4 by norm_num))
      h_T234
  have h_RHS' : (W_smooth W).ord_P P
      (-(yd^3) +
        (-((2 : KE) * a1 * yd^2 * xd) +
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
            (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3))) =
      ((3 : ℤ) : WithTop ℤ) :=
    (SmoothPlaneCurve.ord_P_add_eq_of_lt h_strict).trans h_neg_yd_cube
  have h_id : translateY_xy W xk yk * xd^3 =
      -(yd^3) +
        (-((2 : KE) * a1 * yd^2 * xd) +
          ((yd * (a2 + (2 : KE) * x_gen W + xk') - a1^2 * yd) * xd^2 +
            (-y_gen W + a1 * (a2 + x_gen W + xk') - a3) * xd^3)) := by
    rw [hyd_def, hxd_def, ha1_def, ha2_def, ha3_def, hxk'_def,
        translateY_xy_mul_cube_eq W xk yk]
    ring
  have h_LHS_ord : (W_smooth W).ord_P P (translateY_xy W xk yk * xd^3) =
      ((3 : ℤ) : WithTop ℤ) := h_id ▸ h_RHS'
  have h_split₁ : (W_smooth W).ord_P P (translateY_xy W xk yk * xd^3) =
      (W_smooth W).ord_P P (translateY_xy W xk yk) +
      (W_smooth W).ord_P P (xd^3) :=
    SmoothPlaneCurve.ord_P_mul (P := P) (translateY_xy W xk yk) (xd^3)
  rw [h_split₁, h_xd_cube_eq] at h_LHS_ord
  -- h_LHS_ord : ord_P translateY + 6 = 3 ⟹ ord_P translateY = -3.
  have h_tY_ne : translateY_xy W xk yk ≠ 0 := by
    intro h_zero
    rw [h_zero] at h_LHS_ord
    rw [show ((W_smooth W).ord_P P (0 : KE)) = ⊤ from
        Curves.SmoothPlaneCurve.ord_P_zero] at h_LHS_ord
    simp at h_LHS_ord
  have h_tY_ne_top : (W_smooth W).ord_P P (translateY_xy W xk yk) ≠ ⊤ :=
    (SmoothPlaneCurve.ord_P_eq_top_iff _).not.mpr h_tY_ne
  cases ht_case : (W_smooth W).ord_P P (translateY_xy W xk yk) with
  | top => exact absurd ht_case h_tY_ne_top
  | coe k =>
      rw [ht_case] at h_LHS_ord
      have h_int_eq : k + 6 = 3 := by
        have h_sum : ((k + 6 : ℤ) : WithTop ℤ) = ((3 : ℤ) : WithTop ℤ) := by
          rw [show ((k + 6 : ℤ) : WithTop ℤ) =
            ((k : ℤ) : WithTop ℤ) + ((6 : ℤ) : WithTop ℤ) from by
              push_cast; ring]
          exact h_LHS_ord
        exact_mod_cast h_sum
      have h_k_eq : k = -3 := by omega
      exact_mod_cast h_k_eq

/-- **Type abbreviation for the y-side substantive value at 2-torsion T**:
`ord_P (translateY_xy) = -3` at the negated point. This is the single
substantive witness the y-side chain reduces to.

⟶ Now DISCHARGEABLE via `ord_P_translateY_xy_eq_neg_three_at_2tor` (just shipped). -/
abbrev TwoTorYValueWitness (xT yT : K) (h_ns : W.toAffine.Nonsingular xT yT) : Prop :=
  (W_smooth W).ord_P
      (negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns))
      (translateY_xy W xT (W.toAffine.negY xT yT)) =
    ((-3 : ℤ) : WithTop ℤ)

set_option linter.unusedDecidableInType false in
omit [Fintype K] in
/-- **Discharge `TwoTorYValueWitness` from the substantive y-side lemma**: at smooth
2-torsion `T`, the y-side ord = -3 value follows directly from
`ord_P_translateY_xy_eq_neg_three_at_2tor` applied at the negated coordinates. -/
theorem twoTorYValueWitness_discharge (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    TwoTorYValueWitness W xT yT h_ns := by
  have h_2_tor_neg : W.toAffine.negY xT yT =
      W.toAffine.negY xT (W.toAffine.negY xT yT) := by
    rw [W.toAffine.negY_negY]; exact h_2_tor.symm
  exact ord_P_translateY_xy_eq_neg_three_at_2tor W xT (W.toAffine.negY xT yT)
    ((Affine.nonsingular_neg xT yT).mpr h_ns) h_2_tor_neg

/-- **Bridge at `f = y_gen` for 2-torsion `T` (witness-parametric)**: given the
y-side ord value `ord_P (translateY_xy) = -3` at the negated point, produces
the bridge. Mirrors `ord_T_translateAlgEquivOfPoint_neg_y_gen_eq_neg_three` and
`bridge_at_y_gen_of_non_2_tor` for the 2-tor case. -/
theorem bridge_at_y_gen_of_2_tor_of_witness (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (_h_2_tor : yT = W.toAffine.negY xT yT)
    (h_value : (W_smooth W).ord_P
        (negSmoothPoint W xT (W.toAffine.negY xT yT)
          ((Affine.nonsingular_neg xT yT).mpr h_ns))
        (translateY_xy W xT (W.toAffine.negY xT yT)) =
          ((-3 : ℤ) : WithTop ℤ)) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W)) =
      (W_smooth W).ordAtInfty (y_gen W) := by
  rw [neg_some_eq_some W xT yT h_ns]
  rw [translateAlgEquivOfPoint_some_apply_y_gen W xT (W.toAffine.negY xT yT)
    ((Affine.nonsingular_neg xT yT).mpr h_ns)]
  have h_smoothPt_eq :
      negSmoothPoint W xT (W.toAffine.negY xT yT)
        ((Affine.nonsingular_neg xT yT).mpr h_ns) =
      ({ x := xT, y := yT, nonsingular := h_ns } :
        (W_smooth W).SmoothPoint) := by
    apply Curves.SmoothPlaneCurve.SmoothPoint.ext
    · rfl
    · exact W.toAffine.negY_negY xT yT
  rw [← h_smoothPt_eq]
  rw [h_value]
  rw [show ((W_smooth W).ordAtInfty (y_gen W)) = ((-3 : ℤ) : WithTop ℤ) from
    ordAtInfty_y_gen W]

/-- **Bridge at `x_gen + (negFrob).pullback x_gen`** for 2-torsion `T`: at the
x-side this corresponds to T1's `a₄·(x + π·x)` building block. -/
theorem bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [negFrobeniusIsog_pullback_x_gen, frobeniusIsog_pullback_apply]
  have h_lt : (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) <
      (W_smooth W).ordAtInfty (x_gen W) :=
    Conditional.ordAtInfty_x_gen_pow_card_lt_x_gen W hq
  -- `x_gen + x_gen^q = x_gen^q + x_gen` (commutative); use add_comm.
  rw [add_comm]
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W ⟨xT, yT, h_ns⟩ _ _ _
    (bridge_at_x_gen_pow_card_of_2_tor W xT yT h_ns h_2_tor)
    (bridge_at_x_gen_of_2_tor W xT yT h_ns h_2_tor)
    h_lt

/-- **Bridge at `f = y_gen^q` for 2-torsion `T` (witness-parametric)**: pow on
the witness-parametric y-side base bridge. Analog of `bridge_at_y_gen_pow_card_of_non_2_tor`. -/
theorem bridge_at_y_gen_pow_card_of_2_tor_of_witness (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (h_y_value : TwoTorYValueWitness W xT yT h_ns) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) :=
  ord_P_translateAlgEquivOfPoint_pow_eq_ordAtInfty_of_base
    W ⟨xT, yT, h_ns⟩ _ (y_gen W) (y_gen_ne_zero W)
    (bridge_at_y_gen_of_2_tor_of_witness W xT yT h_ns h_2_tor h_y_value)
    (Fintype.card K)

/-- **Bridge at `f = y_gen - (negFrob).pullback y_gen` for 2-torsion `T`
(witness-parametric)**: composes the y-side base bridge `bridge_at_y_gen_of_2_tor_of_witness`
and its pow variant via the strict-comparison helper (since ord_∞(y_gen^q) = -3q < -3 =
ord_∞(y_gen) for q ≥ 2). Mirrors the non-2-tor structure modulo the witness parameter. -/
theorem bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (h_y_value : TwoTorYValueWitness W xT yT h_ns)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W - y_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (y_gen W - y_gen W ^ Fintype.card K) := by
  have h_eq : y_gen W - y_gen W ^ Fintype.card K =
      -(y_gen W ^ Fintype.card K - y_gen W) := by ring
  rw [h_eq]
  refine ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
    W _ _ _ ?_
  have h_lt : (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) <
      (W_smooth W).ordAtInfty (y_gen W) := by
    have h_pow_eq : (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) =
        (((Fintype.card K : ℤ) * (-3 : ℤ) : ℤ) : WithTop ℤ) :=
      (W_smooth W).ordAtInfty_pow_of_ord_eq (y_gen_ne_zero W) (-3 : ℤ)
        (Fintype.card K) (ordAtInfty_y_gen W)
    rw [h_pow_eq, ordAtInfty_y_gen W]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    have h_lhs_neg : ((Fintype.card K : ℤ) * (-3 : ℤ) : ℤ) = -(3 * (Fintype.card K : ℤ)) := by
      ring
    rw [show (((Fintype.card K : ℤ) * (-3 : ℤ) : ℤ) : WithTop ℤ) =
          ((-(3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) by rw [h_lhs_neg]]
    rw [show ((-3 : ℤ) : WithTop ℤ) = ((-(3 : ℤ) : ℤ) : WithTop ℤ) by norm_cast]
    rw [WithTop.coe_lt_coe]
    linarith
  exact ord_P_translateAlgEquivOfPoint_sub_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_y_gen_pow_card_of_2_tor_of_witness W xT yT h_ns h_2_tor h_y_value)
    (bridge_at_y_gen_of_2_tor_of_witness W xT yT h_ns h_2_tor h_y_value)
    h_lt

/-- **Bridge at `f = y_gen` for 2-torsion `T` (UNCONDITIONAL)**: composes the
witness-parametric form with `twoTorYValueWitness_discharge`. The y-side base
bridge at 2-tor is now unconditional. -/
theorem bridge_at_y_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W)) =
      (W_smooth W).ordAtInfty (y_gen W) :=
  bridge_at_y_gen_of_2_tor_of_witness W xT yT h_ns h_2_tor
    (twoTorYValueWitness_discharge W xT yT h_ns h_2_tor)

/-- **Bridge at `f = y_gen^q` for 2-torsion `T` (UNCONDITIONAL)**: pow on the
just-shipped unconditional y-side base bridge. -/
theorem bridge_at_y_gen_pow_card_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) :=
  bridge_at_y_gen_pow_card_of_2_tor_of_witness W xT yT h_ns h_2_tor
    (twoTorYValueWitness_discharge W xT yT h_ns h_2_tor)

/-- **Bridge at `f = y_gen - y_gen^q` for 2-torsion `T` (UNCONDITIONAL)**. -/
theorem bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W - y_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (y_gen W - y_gen W ^ Fintype.card K) :=
  bridge_at_y_gen_sub_y_gen_pow_card_of_2_tor_of_witness W xT yT h_ns h_2_tor
    (twoTorYValueWitness_discharge W xT yT h_ns h_2_tor) hq

/-- **Bridge at `(negFrob).pullback y_gen` for 2-torsion `T` (UNCONDITIONAL)**:
mirrors `bridge_at_negFrobeniusIsog_pullback_y_gen_of_non_2_tor` (`PoleDivisorFallback.lean:1034`)
using the now-unconditional 2-tor y-side bridges. The pullback expands as
`-y_gen^q - a₁·x_gen^q - a₃`; strict-comparison isolates `-y_gen^q` with ord `-3q`
as the dominant term. -/
theorem bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (y_gen W)) := by
  rw [Conditional.negFrobeniusIsog_pullback_y_gen_eq_pow_form]
  set P : (W_smooth W).SmoothPoint := ⟨xT, yT, h_ns⟩ with hP
  set k : W.toAffine.Point := -(Affine.Point.some xT yT h_ns) with hk
  have h_y_pow_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k (y_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (y_gen W ^ Fintype.card K) :=
    bridge_at_y_gen_pow_card_of_2_tor W xT yT h_ns h_2_tor
  have h_neg_y_pow_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k (-(y_gen W ^ Fintype.card K))) =
      (W_smooth W).ordAtInfty (-(y_gen W ^ Fintype.card K)) :=
    ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
      W P k _ h_y_pow_bridge
  have h_x_pow_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k (x_gen W ^ Fintype.card K)) =
      (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) :=
    bridge_at_x_gen_pow_card_of_2_tor W xT yT h_ns h_2_tor
  have h_xq_ne : x_gen W ^ Fintype.card K ≠ 0 :=
    pow_ne_zero _ (x_gen_ne_zero W)
  have h_a1xq_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K)) :=
    ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
      W P k W.toAffine.a₁ _ h_xq_ne h_x_pow_bridge
  have h_neg_a1xq_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K)))) =
      (W_smooth W).ordAtInfty
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K))) :=
    ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
      W P k _ h_a1xq_bridge
  have h_a3_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) :=
    ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty
      W P k W.toAffine.a₃
  have h_neg_a3_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) =
      (W_smooth W).ordAtInfty
        (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃) :=
    ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
      W P k _ h_a3_bridge
  have h_regroup : -(y_gen W ^ Fintype.card K) -
        algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K) -
        algebraMap K W.toAffine.FunctionField W.toAffine.a₃ =
      -(y_gen W ^ Fintype.card K) +
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W ^ Fintype.card K)) +
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) := by ring
  rw [h_regroup]
  have h_rest_bridge : (W_smooth W).ord_P P
      (translateAlgEquivOfPoint W k
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) +
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃))) =
      (W_smooth W).ordAtInfty
        (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) +
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃)) := by
    by_cases ha1 : W.toAffine.a₁ = 0
    · have h_a1_zero : algebraMap K W.toAffine.FunctionField W.toAffine.a₁ = 0 := by
        rw [ha1, map_zero]
      rw [h_a1_zero, zero_mul, neg_zero, zero_add]
      exact h_neg_a3_bridge
    · have h_a1_ne : algebraMap K W.toAffine.FunctionField W.toAffine.a₁ ≠ 0 :=
        fun h => ha1 (FaithfulSMul.algebraMap_injective K
          W.toAffine.FunctionField (h.trans (map_zero _).symm))
      have h_mul_eq : (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) =
          (W_smooth W).ordAtInfty
            (algebraMap K W.toAffine.FunctionField W.toAffine.a₁) +
          (W_smooth W).ordAtInfty (x_gen W ^ Fintype.card K) :=
        (W_smooth W).ordAtInfty_mul h_a1_ne h_xq_ne
      have h_a1_ord_zero : (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁) = 0 :=
        (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha1
      have h_a1xq_ord : (W_smooth W).ordAtInfty
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W ^ Fintype.card K)) =
          (((Fintype.card K : ℤ) * (-2 : ℤ) : ℤ) : WithTop ℤ) := by
        rw [h_mul_eq, h_a1_ord_zero, zero_add,
            Conditional.ordAtInfty_x_gen_pow_card_eq W]
      have h_neg_a1xq_eq : (W_smooth W).ordAtInfty
          (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K))) =
          (W_smooth W).ordAtInfty
            (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K)) :=
        (W_smooth W).ordAtInfty_neg _
      have h_neg_a1xq_ord : (W_smooth W).ordAtInfty
          (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K))) =
          (((Fintype.card K : ℤ) * (-2 : ℤ) : ℤ) : WithTop ℤ) :=
        h_neg_a1xq_eq.trans h_a1xq_ord
      have h_neg_a3_eq : (W_smooth W).ordAtInfty
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃) =
          (W_smooth W).ordAtInfty
            (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) :=
        (W_smooth W).ordAtInfty_neg _
      have h_neg_a3_ord_le : (W_smooth W).ordAtInfty
          (-(algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
              (x_gen W ^ Fintype.card K))) <
          (W_smooth W).ordAtInfty
          (-algebraMap K W.toAffine.FunctionField W.toAffine.a₃) := by
        rw [h_neg_a1xq_ord, h_neg_a3_eq]
        by_cases ha3 : W.toAffine.a₃ = 0
        · rw [ha3, map_zero]
          rw [show ((W_smooth W).ordAtInfty (0 : W.toAffine.FunctionField)) = ⊤
              from (W_smooth W).ordAtInfty_zero]
          exact WithTop.coe_lt_top _
        · have h_a3_ord_zero : (W_smooth W).ordAtInfty
              (algebraMap K W.toAffine.FunctionField W.toAffine.a₃) = 0 :=
            (W_smooth W).ordAtInfty_algebraMap_F_nonzero ha3
          rw [h_a3_ord_zero]
          rw [show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
              WithTop.coe_lt_coe]
          have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
          linarith
      exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
        W P k _ _ h_neg_a1xq_bridge h_neg_a3_bridge h_neg_a3_ord_le
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W P k _ _ h_neg_y_pow_bridge h_rest_bridge
    (Conditional.ordAtInfty_neg_y_gen_pow_card_lt_rest W hq)

/-- **Bridge at T1 = `a₄ · (x_gen + (negFrob).pullback x_gen)` for 2-torsion `T` (UNCONDITIONAL)**:
const_mul on the strict-add bridge (already shipped). -/
theorem bridge_at_T1_a4_x_add_pi_x_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₄ *
          (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))) :=
  ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ W.toAffine.a₄ _
    (Conditional.x_gen_add_negFrobeniusIsog_pullback_x_gen_ne_zero W hq)
    (bridge_at_x_gen_add_negFrobeniusIsog_pullback_x_gen_of_2_tor W xT yT h_ns h_2_tor hq)

omit [Fintype K] in
/-- **Bridge at T2 = `(2 : K(E)) · a₆` for 2-torsion `T` (UNCONDITIONAL)**: trivial
constant bridge via algebraMap. -/
theorem bridge_at_T2_two_a6_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (_h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((2 : W.toAffine.FunctionField) *
            algebraMap K W.toAffine.FunctionField W.toAffine.a₆)) =
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₆) := by
  have h_eq : (2 : W.toAffine.FunctionField) *
      algebraMap K W.toAffine.FunctionField W.toAffine.a₆ =
      algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₆) := by
    rw [map_mul, map_ofNat]
  rw [h_eq]
  exact ord_P_translateAlgEquivOfPoint_algebraMap_eq_ordAtInfty
    W _ _ (2 * W.toAffine.a₆)

/-- **Bridge at `y_gen + (negFrob).pullback y_gen` for 2-torsion `T` (UNCONDITIONAL)**:
strict-add with `(negFrob).pullback y_gen` having strictly smaller ord (-3q < -3).
Used in T3 of the Num decomposition. -/
theorem bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)) := by
  rw [show y_gen W + (negFrobeniusIsog W).pullback (y_gen W) =
      (negFrobeniusIsog W).pullback (y_gen W) + y_gen W from by ring]
  have h_lt : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (y_gen W)) <
      (W_smooth W).ordAtInfty (y_gen W) := by
    rw [ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq,
        ordAtInfty_y_gen W]
    change (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) <
        (((-3 : ℤ) : ℤ) : WithTop ℤ)
    rw [WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor W xT yT h_ns h_2_tor hq)
    (bridge_at_y_gen_of_2_tor W xT yT h_ns h_2_tor) h_lt

/-- **Bridge at `y_gen · (negFrob).pullback y_gen` for 2-torsion `T` (UNCONDITIONAL)**:
mul on bridges for y_gen and (negFrob).pullback y_gen. Building block for T4. -/
theorem bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (y_gen W * (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) := by
  have h_piy_ne := pi_y_gen_ne_zero_aux W hq
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ (y_gen_ne_zero W) h_piy_ne
    (bridge_at_y_gen_of_2_tor W xT yT h_ns h_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor W xT yT h_ns h_2_tor hq)

/-- **Bridge at T4 = `(2 : K(E)) · y_gen · (negFrob).pullback y_gen` for 2-torsion `T`
(UNCONDITIONAL)**: const_mul on the y·πy bridge. -/
theorem bridge_at_T4_two_y_pi_y_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((2 : W.toAffine.FunctionField) * y_gen W *
            (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) * y_gen W *
          (negFrobeniusIsog W).pullback (y_gen W)) := by
  rw [show (2 : W.toAffine.FunctionField) * y_gen W *
      (negFrobeniusIsog W).pullback (y_gen W) =
      algebraMap K W.toAffine.FunctionField (2 : K) *
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) from by
    rw [map_ofNat]; ring]
  have h_y_pi_y_ne : y_gen W * (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 :=
    mul_ne_zero (y_gen_ne_zero W) (pi_y_gen_ne_zero_aux W hq)
  exact ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ (2 : K) _ h_y_pi_y_ne
    (bridge_at_y_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor W xT yT h_ns h_2_tor hq)

/-- **Bridge at T8 = `(2 : K(E)) · a₂ · x_gen · (negFrob).pullback x_gen` for 2-torsion
`T` (UNCONDITIONAL)**: regroup and const_mul on x·πx bridge. -/
theorem bridge_at_T8_two_a2_x_pi_x_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((2 : W.toAffine.FunctionField) *
            algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
            x_gen W * (negFrobeniusIsog W).pullback (x_gen W))) =
      (W_smooth W).ordAtInfty
        ((2 : W.toAffine.FunctionField) *
          algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
          x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) := by
  rw [show (2 : W.toAffine.FunctionField) *
      algebraMap K W.toAffine.FunctionField W.toAffine.a₂ *
      x_gen W * (negFrobeniusIsog W).pullback (x_gen W) =
      algebraMap K W.toAffine.FunctionField (2 * W.toAffine.a₂) *
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W)) from by
    rw [map_mul, map_ofNat]; ring]
  have h_x_pi_x_ne : x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    mul_ne_zero (x_gen_ne_zero W) (pi_x_gen_ne_zero_aux W)
  exact ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ (2 * W.toAffine.a₂) _ h_x_pi_x_ne
    (bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor W xT yT h_ns h_2_tor)

/-- **Bridge at `x_gen · (negFrob).pullback y_gen` for 2-torsion `T` (UNCONDITIONAL)**:
mul on x_gen and (negFrob).pullback y_gen. Building block for T5. -/
theorem bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W))) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) := by
  have h_piy_ne := pi_y_gen_ne_zero_aux W hq
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ (x_gen_ne_zero W) h_piy_ne
    (bridge_at_x_gen_of_2_tor W xT yT h_ns h_2_tor)
    (bridge_at_negFrobeniusIsog_pullback_y_gen_of_2_tor W xT yT h_ns h_2_tor hq)

/-- **Bridge at `(negFrob).pullback x_gen · y_gen` for 2-torsion `T` (UNCONDITIONAL)**:
mul on (negFrob).pullback x_gen and y_gen. Building block for T5. -/
theorem bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
  have h_pix_ne := pi_x_gen_ne_zero_aux W
  exact ord_P_translateAlgEquivOfPoint_mul_eq_ordAtInfty_of_each
    W _ _ _ _ h_pix_ne (y_gen_ne_zero W)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_of_2_tor W xT yT h_ns h_2_tor)
    (bridge_at_y_gen_of_2_tor W xT yT h_ns h_2_tor)

/-- **Bridge at `x_gen · (negFrob).pullback y_gen + (negFrob).pullback x_gen · y_gen`
for 2-torsion `T` (UNCONDITIONAL)**: strict-add with x·πy strictly smaller. -/
theorem bridge_at_x_pi_y_add_pi_x_y_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) =
      (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
  have h_piy_ne := pi_y_gen_ne_zero_aux W hq
  have h_pix_ne := pi_x_gen_ne_zero_aux W
  have h_xy_mul_split : (W_smooth W).ordAtInfty
      (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
      (W_smooth W).ordAtInfty (x_gen W) +
        (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (y_gen W)) :=
    (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_piy_ne
  have h_xy_ord : (W_smooth W).ordAtInfty
      (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
      (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) := by
    rw [h_xy_mul_split, ordAtInfty_x_gen W,
        ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq]
    change (((-2 : ℤ) : ℤ) : WithTop ℤ) +
        (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
        (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add]
    congr 1
    ring
  have h_pxy_mul_split : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W)) +
        (W_smooth W).ordAtInfty (y_gen W) :=
    (W_smooth W).ordAtInfty_mul h_pix_ne (y_gen_ne_zero W)
  have h_pxy_ord : (W_smooth W).ordAtInfty
      ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
      (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) := by
    rw [h_pxy_mul_split, ordAtInfty_negFrobeniusIsog_pullback_x_gen W,
        ordAtInfty_y_gen W]
    change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) +
        (((-3 : ℤ) : ℤ) : WithTop ℤ) =
        (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ)
    rw [← WithTop.coe_add]
    congr 1
  have h_lt : (W_smooth W).ordAtInfty
      (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) <
      (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
    rw [h_xy_ord, h_pxy_ord, WithTop.coe_lt_coe]
    have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    linarith
  exact ord_P_translateAlgEquivOfPoint_add_eq_ordAtInfty_of_strict_lt
    W _ _ _ _
    (bridge_at_x_gen_mul_negFrobeniusIsog_pullback_y_gen_of_2_tor W xT yT h_ns h_2_tor hq)
    (bridge_at_negFrobeniusIsog_pullback_x_gen_mul_y_gen_of_2_tor W xT yT h_ns h_2_tor) h_lt

/-- **Bridge at T5 = `a₁ · (x · π·y + π·x · y)` for 2-torsion `T` (UNCONDITIONAL)**:
const_mul on the strict-add bridge. -/
theorem bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
            (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
              (negFrobeniusIsog W).pullback (x_gen W) * y_gen W))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₁ *
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
            (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)) := by
  have h_sum_ne : x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
      (negFrobeniusIsog W).pullback (x_gen W) * y_gen W ≠ 0 := by
    intro h_zero
    have h_top : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) = ⊤ := by
      rw [h_zero]; exact (W_smooth W).ordAtInfty_zero
    have h_piy_ne := pi_y_gen_ne_zero_aux W hq
    have h_pix_ne := pi_x_gen_ne_zero_aux W
    have h_xy_mul_split : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
        (W_smooth W).ordAtInfty (x_gen W) +
          (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_piy_ne
    have h_xy_ord : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
        (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ) := by
      rw [h_xy_mul_split, ordAtInfty_x_gen W,
          ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq]
      change (((-2 : ℤ) : ℤ) : WithTop ℤ) +
          (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
          (((-3 * (Fintype.card K : ℤ) - 2) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
      ring
    have h_pxy_mul_split : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W)) +
          (W_smooth W).ordAtInfty (y_gen W) :=
      (W_smooth W).ordAtInfty_mul h_pix_ne (y_gen_ne_zero W)
    have h_pxy_ord : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ) := by
      rw [h_pxy_mul_split, ordAtInfty_negFrobeniusIsog_pullback_x_gen W,
          ordAtInfty_y_gen W]
      change (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) +
          (((-3 : ℤ) : ℤ) : WithTop ℤ) =
          (((-2 * (Fintype.card K : ℤ) - 3) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
    have h_lt : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) <
        (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W) := by
      rw [h_xy_ord, h_pxy_ord]
      rw [WithTop.coe_lt_coe]
      have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
      linarith
    have h_sum_eq : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W) =
        (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (y_gen W)) :=
      (W_smooth W).ordAtInfty_add_eq_of_lt h_lt
    rw [h_sum_eq, h_xy_ord] at h_top
    exact WithTop.coe_ne_top h_top
  exact ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ W.toAffine.a₁ _ h_sum_ne
    (bridge_at_x_pi_y_add_pi_x_y_of_2_tor W xT yT h_ns h_2_tor hq)

/-- **Bridge at T3 = `a₃ · (y_gen + (negFrob).pullback y_gen)` for 2-torsion `T`
(UNCONDITIONAL)**: const_mul on the y+πy strict-add bridge. -/
theorem bridge_at_T3_a3_y_add_pi_y_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
            (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)))) =
      (W_smooth W).ordAtInfty
        (algebraMap K W.toAffine.FunctionField W.toAffine.a₃ *
          (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))) :=
  ord_P_translateAlgEquivOfPoint_const_mul_eq_ordAtInfty_of_base
    W _ _ W.toAffine.a₃ _
    (Conditional.y_gen_add_negFrobeniusIsog_pullback_y_gen_ne_zero W hq)
    (bridge_at_y_gen_add_negFrobeniusIsog_pullback_y_gen_of_2_tor W xT yT h_ns h_2_tor hq)

/-- **Bridge at `addPullbackNumerator_negFrobenius`** for 2-torsion T
under `hq`, **UNCONDITIONAL**.

Mirror of `bridge_at_addPullbackNumerator_negFrobenius_of_non_2_tor`: apply
`ord_P_translateAlgEquivOfPoint_sum_dominant` with dom = T7 (x · π·x²,
ord = -2-4q) and the same seven other terms; the per-term bridges are the
2-torsion versions just shipped, and the strict-comparison framework is
identical because the `ordAtInfty_T*_ge` bounds are universal in T. -/
theorem bridge_at_addPullbackNumerator_negFrobenius_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (addPullbackNumerator_negFrobenius W)) =
      (W_smooth W).ordAtInfty
        (addPullbackNumerator_negFrobenius W) := by
  rw [addPullbackNumerator_negFrobenius_eq_reduced]
  unfold addPullbackNumerator_reduced_negFrobenius
  rw [Conditional.reduced_form_eq_dom_plus_list W]
  have hq' : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  apply ord_P_translateAlgEquivOfPoint_sum_dominant
  · exact bridge_at_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor
      W xT yT h_ns h_2_tor
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with hT1 | hT2 | hT3 | hT4 | hT5 | hT6 | hT8
    · exact hT1 ▸ bridge_at_T1_a4_x_add_pi_x_of_2_tor
        W xT yT h_ns h_2_tor hq
    · exact hT2 ▸ bridge_at_T2_two_a6_of_2_tor W xT yT h_ns h_2_tor
    · exact hT3 ▸ ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
        W _ _ _ (bridge_at_T3_a3_y_add_pi_y_of_2_tor
          W xT yT h_ns h_2_tor hq)
    · exact hT4 ▸ ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
        W _ _ _ (bridge_at_T4_two_y_pi_y_of_2_tor
          W xT yT h_ns h_2_tor hq)
    · exact hT5 ▸ ord_P_translateAlgEquivOfPoint_neg_eq_ordAtInfty_of_base
        W _ _ _ (bridge_at_T5_a1_x_pi_y_add_pi_x_y_of_2_tor
          W xT yT h_ns h_2_tor hq)
    · exact hT6 ▸
        bridge_at_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen_of_2_tor
          W xT yT h_ns h_2_tor
    · exact hT8 ▸ bridge_at_T8_two_a2_x_pi_x_of_2_tor
        W xT yT h_ns h_2_tor
  · intro f hf
    have h_pix_ne := pi_x_gen_ne_zero_aux W
    have h_pix_sq_ne : (negFrobeniusIsog W).pullback (x_gen W) ^ 2 ≠ 0 :=
      pow_ne_zero _ h_pix_ne
    have h_pix_sq_ord : (W_smooth W).ordAtInfty
        ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
        (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
      have h_pow : (W_smooth W).ordAtInfty
          ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
          (2 : ℕ) • (W_smooth W).ordAtInfty
            ((negFrobeniusIsog W).pullback (x_gen W)) :=
        (W_smooth W).ordAtInfty_pow h_pix_ne 2
      rw [h_pow, ordAtInfty_negFrobeniusIsog_pullback_x_gen W]
      change (2 : ℕ) • (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
          (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
      rw [two_nsmul, ← WithTop.coe_add]
      congr 1; ring
    have h_T7_mul : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
        (W_smooth W).ordAtInfty (x_gen W) +
          (W_smooth W).ordAtInfty
            ((negFrobeniusIsog W).pullback (x_gen W) ^ 2) :=
      (W_smooth W).ordAtInfty_mul (x_gen_ne_zero W) h_pix_sq_ne
    have h_T7_ord : (W_smooth W).ordAtInfty
        (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) =
        (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
      rw [h_T7_mul, ordAtInfty_x_gen W, h_pix_sq_ord]
      show (((-2 : ℤ) : ℤ) : WithTop ℤ) +
          (((-4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) =
          (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
      rw [← WithTop.coe_add]
      congr 1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    have h_int_lt : (-2 - 4 * (Fintype.card K : ℤ)) <
        (-3 - 3 * (Fintype.card K : ℤ)) := by linarith
    have h_lt_helper : ∀ {x : WithTop ℤ},
        (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤ x →
        (W_smooth W).ordAtInfty
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W) ^ 2) < x := by
      intro x hx
      rw [h_T7_ord]
      exact Conditional.withTop_int_lt_of_lt_of_le h_int_lt hx
    rcases hf with hT1 | hT2 | hT3 | hT4 | hT5 | hT6 | hT8
    · exact hT1 ▸ h_lt_helper (Conditional.ordAtInfty_T1_ge W hq)
    · exact hT2 ▸ h_lt_helper (Conditional.ordAtInfty_T2_ge W hq)
    · exact hT3 ▸ h_lt_helper (Conditional.ordAtInfty_neg_T3_ge W hq)
    · exact hT4 ▸ h_lt_helper (Conditional.ordAtInfty_neg_T4_ge W hq)
    · exact hT5 ▸ h_lt_helper (Conditional.ordAtInfty_neg_T5_ge W hq)
    · exact hT6 ▸ h_lt_helper (Conditional.ordAtInfty_T6_ge W hq)
    · exact hT8 ▸ h_lt_helper (Conditional.ordAtInfty_T8_ge W hq)

/-- **Bridge at `addPullback_x W (negFrobeniusIsog W)`** for 2-torsion T
under `hq`, **UNCONDITIONAL**.  Discharges the
`bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num` Conditional consumer
with the just-shipped 2-tor Num bridge.

Note: `bridge_at_addPullback_x_negFrobenius_of_bridge_at_Num` requires a
non-2-torsion hypothesis only for its appeal to
`bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_non_2_tor`.  For
the 2-torsion side we apply the same composition but with the 2-torsion
analogue of the denominator bridge (the square is bridge-trivial because
it inherits via Conditional.bridge_at_div). -/
theorem bridge_at_addPullback_x_negFrobenius_of_2_tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        (translateAlgEquivOfPoint W
          (-(Affine.Point.some xT yT h_ns) : W.toAffine.Point)
          (addPullback_x W (negFrobeniusIsog W))) =
      (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)) := by
  have h_pix_ne : x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  have h_pix_sq_ne : (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 h_pix_ne
  have h_div_eq : addPullback_x W (negFrobeniusIsog W) =
      addPullbackNumerator_negFrobenius W /
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    rw [addPullbackNumerator_negFrobenius_eq W,
        mul_div_cancel_left₀ _ h_pix_sq_ne]
  rw [h_div_eq]
  have h_Num_ord_eq : (W_smooth W).ordAtInfty
      (addPullbackNumerator_negFrobenius W) =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [addPullbackNumerator_negFrobenius_eq_reduced]
    exact ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq W hq
  have h_Num_ne : addPullbackNumerator_negFrobenius W ≠ 0 := fun h => by
    have h_top : (W_smooth W).ordAtInfty
        (addPullbackNumerator_negFrobenius W) = ⊤ := by
      rw [h]; exact (W_smooth W).ordAtInfty_zero
    rw [h_Num_ord_eq] at h_top
    exact WithTop.coe_ne_top h_top
  exact ord_P_translateAlgEquivOfPoint_div_eq_ordAtInfty_of_each
    W ⟨xT, yT, h_ns⟩ _ _ _
    h_Num_ne
    h_pix_sq_ne
    (bridge_at_addPullbackNumerator_negFrobenius_of_2_tor
      W xT yT h_ns h_2_tor hq)
    (bridge_at_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_of_2_tor
      W xT yT h_ns h_2_tor hq)

/-- **LEMMA 3 UNCONDITIONAL AT 2-TORSION** (Pole at every 2-torsion kernel point):
`ord_T(γ.pullback x_gen) = -2` at any 2-torsion T = (xT, yT) ∈ E(F_q),
for `γ = isogOneSub_negFrobenius`.

Companion to `lemma3_pole_at_T_unconditional`; takes 2-torsion T instead. -/
theorem lemma3_pole_at_T_at_2tor (xT yT : K)
    (h_ns : W.toAffine.Nonsingular xT yT) (h_2_tor : yT = W.toAffine.negY xT yT)
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ord_P (⟨xT, yT, h_ns⟩ : (W_smooth W).SmoothPoint)
        ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  apply Conditional.Conditional.lemma3_pole_at_T_of_bridge_and_invariance
    W xT yT h_ns hq
  · exact bridge_at_addPullback_x_negFrobenius_of_2_tor
      W xT yT h_ns h_2_tor hq
  · have h_neg_T_in_ker : -(Affine.Point.some xT yT h_ns) ∈
        (isogOneSub_negFrobenius W hq).kernel := by
      change (isogOneSub_negFrobenius W hq).toAddMonoidHom
        (-(Affine.Point.some xT yT h_ns)) = 0
      rw [isogOneSub_negFrobenius_toAddMonoidHom, AddMonoidHom.sub_apply, AddMonoidHom.id_apply]
      change (-(Affine.Point.some xT yT h_ns)) - (-(Affine.Point.some xT yT h_ns)) = 0
      exact sub_self _
    exact (xy_family_isogOneSub_negFrobenius W hq
      ⟨-(Affine.Point.some xT yT h_ns), h_neg_T_in_ker⟩).1

end TwoTorBridges

end HasseWeil
