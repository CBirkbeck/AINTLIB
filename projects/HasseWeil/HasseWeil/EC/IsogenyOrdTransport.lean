/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.TranslateOrdInfty

/-!
# General DVR order-transport along a field hom (Silverman II.2.5, the unramified case)

This file isolates the *purely valuation-theoretic* core of the order-transport
`ord_P (φ g) = ord_Q g` for an injective field homomorphism `φ : K(C) → K(C)` and a pair of smooth
points `P` (source) and `Q` (target).  It is the abstract DVR-transport step (Step 1 of the
divisor-pullback brief): once one knows

* **(same place)** the comap valuation `(pointValuation Q).comap φ` is `Valuation.IsEquiv` to
  `pointValuation P` — i.e. `φ` carries the valuation ring of `Q` onto that of `P`; and
* **(unramified, `e = 1`)** `ord_P (φ t) = 1` for a *single* uniformizer `t` at `Q`,

the value-precise identity `ord_P (φ g) = ord_Q g` holds for **all** `g` (no ramification factor).
The two inputs are genuinely independent: the first is "same place / same valuation ring", the
second is the normalization `e = 1` (the ramification index), which for `[ℓ]` is the geometric
content of separability.

The main export is `ord_P_comap_eq_of_isEquiv_of_uniformizer`, plus the small valuation glue
lemmas it rests on (re-derived here, Fintype-free, so the file is independent of the
`[Fintype K]`-scoped versions in `Hasse/L6Witnesses.lean`).

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.2.5–2.6, III.4.10c.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [DecidableEq F]

namespace Curves.SmoothPlaneCurve

variable (C : SmoothPlaneCurve F)

/-- **`pointValuation` is surjective onto `ℤᵐ⁰`** at a smooth point `P`.  (Fintype-free
re-derivation of `Hasse/L6Witnesses.lean`'s `pointValuation_surjective`.)  The local ring is a DVR
with a uniformizer `t` (`ord_P t = 1`) realising `exp (-1)`; values are integer powers of it. -/
theorem pointValuation_surjective' (P : C.SmoothPoint) :
    Function.Surjective (C.pointValuation P) := by
  obtain ⟨t, ht⟩ := C.exists_uniformizer P
  rw [SmoothPlaneCurve.Uniformizer] at ht
  have ht_ne : t ≠ 0 := by
    intro h; rw [h, SmoothPlaneCurve.ord_P_zero] at ht; exact WithTop.top_ne_one ht
  have hone : C.ord_P P t = ((1 : ℤ) : WithTop ℤ) := by rw [ht]; rfl
  have hvt : C.pointValuation P t = WithZero.exp (-1 : ℤ) :=
    pointValuation_eq_exp_neg_of_ord_P_eq ht_ne hone
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  · refine ⟨t ^ (-(WithZero.log z)), ?_⟩
    rw [map_zpow₀, hvt, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, neg_neg,
      WithZero.exp_log hz]

end Curves.SmoothPlaneCurve

/-- **Two surjective `ℤᵐ⁰`-valued valuations that are equivalent are equal.**  (Fintype-free
re-derivation of `Hasse/L6Witnesses.lean`'s `Valuation.isEquiv_iff_eq_of_surjective_withZeroInt`.)
The order-isomorphism of value groups underlying `IsEquiv` is forced to be the identity because the
only positive divisor of `1` in `ℤ` is `1`. -/
theorem Valuation.isEquiv_eq_of_surjective_withZeroInt
    {E : Type*} [Field E] (v w : Valuation E (WithZero (Multiplicative ℤ)))
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) :
    v = w := by
  obtain ⟨e, he⟩ := hv (WithZero.exp 1)
  have hvpow : ∀ k : ℤ, v (e ^ k) = WithZero.exp k := by
    intro k; rw [map_zpow₀, he, ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
  have hwe0 : w e ≠ 0 :=
    ((h.eq_zero).ne).mp (by rw [he]; exact WithZero.exp_ne_zero)
  have key : ∀ x : E, v x ≠ 0 → w x = (w e) ^ (WithZero.log (v x)) := by
    intro x hx
    set m := WithZero.log (v x) with hm
    have hvu : v (x * e ^ (-m)) = 1 := by
      rw [map_mul, hvpow (-m), ← WithZero.exp_log hx, ← hm, ← WithZero.exp_add,
        add_neg_cancel, WithZero.exp_zero]
    have hwu : w (x * e ^ (-m)) = 1 := (h.eq_one_iff_eq_one).mp hvu
    rw [map_mul, map_zpow₀, zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hwe0)] at hwu
    exact hwu
  have h1we : (1 : WithZero (Multiplicative ℤ)) < w e := by
    rw [← h.one_lt_iff_one_lt, he, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  obtain ⟨x₁, hx₁⟩ := hw (WithZero.exp 1)
  have hvx₁ : v x₁ ≠ 0 :=
    ((h.eq_zero).ne).mpr (by rw [hx₁]; exact WithZero.exp_ne_zero)
  have hk := key x₁ hvx₁
  rw [hx₁] at hk
  have hlog : (1 : ℤ) = WithZero.log (v x₁) * WithZero.log (w e) := by
    have h2 : WithZero.log (WithZero.exp (1 : ℤ)) =
        WithZero.log ((w e) ^ (WithZero.log (v x₁))) := by rw [hk]
    rwa [WithZero.log_exp, WithZero.log_zpow, smul_eq_mul] at h2
  have hc1 : WithZero.log (w e) = 1 := by
    have hdvd : WithZero.log (w e) ∣ 1 := ⟨_, by rw [hlog]; ring⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with hh | hh
    · exact hh
    · -- `w e > 1` forces `log (w e) > 0`, ruling out `-1`.
      exfalso
      have hpos : 0 < WithZero.log (w e) := by
        have := (WithZero.lt_log_iff_exp_lt hwe0 (a := (0 : ℤ))).mpr (by rwa [WithZero.exp_zero])
        simpa using this
      omega
  apply _root_.Valuation.ext
  intro x
  rcases eq_or_ne (v x) 0 with hx0 | hx0
  · rw [hx0, (h.eq_zero).mp hx0]
  · rw [key x hx0, ← WithZero.exp_log hwe0, hc1, ← WithZero.exp_zsmul, smul_eq_mul, mul_one,
      WithZero.exp_log hx0]

namespace Curves.SmoothPlaneCurve

variable (C : SmoothPlaneCurve F)

/-- **The comap valuation `(pointValuation P).comap φ` is surjective**, given the single
unramifiedness datum `ord_P (φ t) = 1` for a uniformizer `t` at `Q` (i.e. `e = 1`).  Its values run
over `{exp (-n) : n}` via the powers `φ(t)^n`.  This is the half of the value-precise identity that
encodes the normalization. -/
theorem comap_pointValuation_surjective_of_ord_eq_one
    {E : Type*} [Field E] (φ : E →+* C.FunctionField)
    {P : C.SmoothPoint} {t : E}
    (ht : C.ord_P P (φ t) = ((1 : ℤ) : WithTop ℤ)) :
    Function.Surjective ((C.pointValuation P).comap φ) := by
  have hφt_ne : φ t ≠ 0 := by
    intro h; rw [h, SmoothPlaneCurve.ord_P_zero] at ht; exact WithTop.top_ne_coe ht
  have hvt : (C.pointValuation P).comap φ t = WithZero.exp (-1 : ℤ) := by
    rw [_root_.Valuation.comap_apply]
    exact pointValuation_eq_exp_neg_of_ord_P_eq hφt_ne ht
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  · refine ⟨t ^ (-(WithZero.log z)), ?_⟩
    rw [map_zpow₀, hvt, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one, neg_neg,
      WithZero.exp_log hz]

/-- **General DVR order-transport (value-precise), the unramified case.**

Let `φ : E → K(C)` be a ring hom from a field `E`, `P` a smooth point of `C`, and
`v_Q : Valuation E ℤᵐ⁰` a *surjective* valuation on `E`.  If

* the comap valuation `(pointValuation P).comap φ` is `Valuation.IsEquiv` to `v_Q` (**same place**),
  and
* `ord_P (φ t) = 1` for a single `t` (`φ t` a uniformizer at `P`; with `t` a uniformizer at `Q`
  this is the **`e = 1`** normalization),

then `(pointValuation P).comap φ = v_Q` *as valuations* (not merely equivalent).  Reading off `ord`,
this yields `ord_P (φ g) = ord_Q g` for all `g` with no ramification factor.

This packages Step 1 of the divisor-pullback brief: the entire affine/infinity order-transport for
a separable isogeny reduces to discharging the two displayed inputs. -/
theorem comap_pointValuation_eq_of_isEquiv_of_ord_eq_one
    {E : Type*} [Field E] (φ : E →+* C.FunctionField) (P : C.SmoothPoint)
    (v_Q : _root_.Valuation E (WithZero (Multiplicative ℤ))) (hv_Q : Function.Surjective v_Q)
    (h_equiv : ((C.pointValuation P).comap φ).IsEquiv v_Q)
    {t : E}
    (ht_ord : C.ord_P P (φ t) = ((1 : ℤ) : WithTop ℤ)) :
    (C.pointValuation P).comap φ = v_Q :=
  Valuation.isEquiv_eq_of_surjective_withZeroInt _ _
    (comap_pointValuation_surjective_of_ord_eq_one C φ ht_ord) hv_Q h_equiv

end Curves.SmoothPlaneCurve

end HasseWeil
