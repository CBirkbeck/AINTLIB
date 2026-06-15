/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback.Differential
import HasseWeil.BridgeFrobenius
import HasseWeil.HahnSeriesAux

/-!
# Silverman IV.1.4 scaffold for the leading-coefficient bridge

Substantive computation toward closing BRIDGE-001 / BRIDGE-003 for the
specific case `γ = isogOneSub_negFrobenius`. The deliverable target is
the leading-coefficient identity:

```
PowerSeries.coeff 1 (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = 1
```

which equivalently says:

```
(localExpand W (addPullbackAlgHom_negFrobenius W hq (localParam W))).coeff (1 : ℤ) = 1
```

where `localParam W = -x_gen / y_gen` is the local parameter at the point at
infinity `O`.

## Decomposition

The substantive piece breaks into:

1. **Order computation** — `ord (γ.pullback localParam) = 1` at infinity.
   Direct from `ord (addPullback_x) = -2` (`ord_addPullback_x_negFrobenius`,
   existing) and `ord (addPullback_y) = -3` (analog, this file).
2. **Leading-coefficient computation** — extract the coefficient of `t¹` in
   the Laurent expansion. The key formula (at the formal-group leading order):
   `coeff 1 (formal γ) = 1 - (coeff q (formal id) * coeff 1 (formal frobeniusIsog))`.
   Specializes via `formalIsogenySeries_id = X` (coeff 1 = 1) and
   `formalIsogenySeries_frobenius = X^q` (coeff 1 = 0 for q ≥ 2),
   giving `coeff 1 = 1 + 0 = 1`.

## Sub-helpers shipped here

* `ord_addPullback_y_negFrobenius` — `ord (addPullback_y W (negFrobeniusIsog W)) = -3`.
* `ord_localParam_pullback_negFrobenius` — `ord (γ.pullback localParam) = 1`.
* `formalIsogenySeries_isogOneSub_negFrobenius_constantCoeff` — the
  `constantCoeff = 0` fact (genuine isogeny).

## References

* Silverman, *The Arithmetic of Elliptic Curves*, IV.1.4 (formal group law
  agreement with the addition formula's local expansion).
-/

open WeierstrassCurve PowerSeries LaurentSeries

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- **Order of `-addPullback_x / addPullback_y = 1` at infinity (axiom-clean,
witness-parametric)**: given `ord (addPullback_x) = -2` and `ord (addPullback_y)
= -3`, the local-parameter form `-addPullback_x / addPullback_y` (which equals
`γ.pullback (localParam W)` once the addition-pullback γ is realized as a ring
hom) has order `1` at infinity.

Substantive content of Silverman IV.1.4's leading-order claim: since
`γ.pullback (localParam) = γ.pullback (-x_gen / y_gen) = -γ.pullback(x_gen) /
γ.pullback(y_gen) = -addPullback_x / addPullback_y` for any ring-hom realization
of γ, the order-1 fact reduces to the purely arithmetic
`ord(-a / b) = ord(a) - ord(b) = -2 - (-3) = 1`.

Witness-parametric: plugs the existing axiom-clean
`ord_addPullback_x_negFrobenius` and the (currently sorry-bearing)
`ord_addPullback_y_negFrobenius` into a closed-form ord computation. -/
theorem ord_neg_addPullback_x_div_y_negFrobenius
    (h_x : (W_smooth W).ordAtInfty (addPullback_x W (negFrobeniusIsog W)) =
      ((-2 : ℤ) : WithTop ℤ))
    (h_y : (W_smooth W).ordAtInfty (addPullback_y W (negFrobeniusIsog W)) =
      ((-3 : ℤ) : WithTop ℤ)) :
    (W_smooth W).ordAtInfty
      (-(addPullback_x W (negFrobeniusIsog W)) /
        addPullback_y W (negFrobeniusIsog W)) =
      ((1 : ℤ) : WithTop ℤ) := by
  have h_y_ne : addPullback_y W (negFrobeniusIsog W) ≠ 0 := by
    intro h
    have ht : (W_smooth W).ordAtInfty (addPullback_y W (negFrobeniusIsog W)) = ⊤ := by
      rw [h]; exact (W_smooth W).ordAtInfty_zero
    rw [h_y] at ht
    exact WithTop.coe_ne_top ht
  have h_neg_x : (W_smooth W).ordAtInfty
      (-(addPullback_x W (negFrobeniusIsog W))) =
      ((-2 : ℤ) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_neg _).trans h_x
  exact ((W_smooth W).ord_div_concrete h_y_ne (-2) (-3) h_neg_x h_y).trans rfl

/-- **IV.1.4 step 1 unconditional**: `ord(-addPullback_x / addPullback_y) = 1`
at infinity for the negFrobenius case (q ≥ 2, any characteristic). Combines
the witness-parametric `ord_neg_addPullback_x_div_y_negFrobenius` with the
two axiom-clean witnesses `ord_addPullback_x_negFrobenius` and the new
`ord_addPullback_y_negFrobenius`.

This is the substantive ord-1 conclusion of Silverman IV.1.4 step 1. The
ord-1 fact for `γ.pullback (localParam W)` follows once the addition-pullback
ring hom γ is realized via `addPullbackAlgHom_negFrobenius W hq`. -/
theorem ord_neg_addPullback_x_div_y_negFrobenius_unconditional
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty
      (-(addPullback_x W (negFrobeniusIsog W)) /
        addPullback_y W (negFrobeniusIsog W)) =
      ((1 : ℤ) : WithTop ℤ) :=
  ord_neg_addPullback_x_div_y_negFrobenius W
    (ord_addPullback_x_negFrobenius W hq)
    (ord_addPullback_y_negFrobenius W hq)

/-- **`(negFrob).pullback localParam = ((mulByInt(-1)).pullback localParam)^q`**
(axiom-clean). Direct from `negFrob = mulByInt(-1) ∘ frobenius` and
`frobenius.pullback = (·)^q`. -/
theorem negFrobeniusIsog_pullback_localParam_eq_pow :
    (negFrobeniusIsog W).pullback (localParam W) =
      ((mulByInt W.toAffine (-1)).pullback (localParam W)) ^ Fintype.card K := by
  unfold negFrobeniusIsog
  rw [Isogeny.comp_algebraMap_eq, frobeniusIsog_pullback_apply]

/-- **Closed form for `(mulByInt(-1)).pullback localParam`** (axiom-clean).
The σ-action on the local parameter `t = -x/y` evaluates to
`x_gen / (y_gen + a₁·x_gen + a₃)`. From `mulByInt_pullback_x_neg_one`
(σ fixes `x_gen`) and `mulByInt_pullback_y_neg_one` (σ sends `y_gen` to
`-y_gen - a₁·x_gen - a₃`). -/
theorem mulByInt_neg_one_pullback_localParam :
    (mulByInt W.toAffine (-1)).pullback (localParam W) =
      x_gen W / (y_gen W + algebraMap K KE W.a₁ * x_gen W +
        algebraMap K KE W.a₃) := by
  unfold localParam
  rw [map_div₀, map_neg, mulByInt_pullback_x_neg_one, mulByInt_pullback_y_neg_one]
  -- Goal: -x_gen / (-y_gen - a₁·x_gen - a₃) = x_gen / (y_gen + a₁·x_gen + a₃)
  rw [show -y_gen W - algebraMap K KE W.a₁ * x_gen W -
        algebraMap K KE W.a₃ =
        -(y_gen W + algebraMap K KE W.a₁ * x_gen W +
          algebraMap K KE W.a₃) from by ring]
  rw [neg_div_neg_eq]

/-- **`ord((negFrobeniusIsog W).pullback (localParam W)) = q`** at infinity
(axiom-clean). Direct from the chain rule on `localParam = -x_gen/y_gen`:
`(negFrob).pullback localParam = -(negFrob).pullback x_gen / (negFrob).pullback y_gen`,
combined with `ord((negFrob).pb x_gen) = -2q` and `ord((negFrob).pb y_gen) = -3q`
(both existing axiom-clean), gives `ord = -2q - (-3q) = q`.

This computes the order of the local-parameter image under `−π` directly (i.e.,
without going through the addition-pullback γ). For q ≥ 2 this gives ord ≥ 2,
which is the substantive content needed to conclude
`coeff 1 (formal (negFrobeniusIsog W)) = 0`. -/
theorem ord_negFrobeniusIsog_pullback_localParam (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (localParam W)) =
      ((Fintype.card K : ℤ) : WithTop ℤ) := by
  have hX_ord : (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (x_gen W)) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) :=
    ordAtInfty_negFrobeniusIsog_pullback_x_gen W
  have hY_ord : (W_smooth W).ordAtInfty ((negFrobeniusIsog W).pullback (y_gen W)) =
      ((-3 * (Fintype.card K : ℤ)) : WithTop ℤ) :=
    ordAtInfty_negFrobeniusIsog_pullback_y_gen W hq
  have h_eq : (negFrobeniusIsog W).pullback (localParam W) =
      -((negFrobeniusIsog W).pullback (x_gen W)) /
      (negFrobeniusIsog W).pullback (y_gen W) := by
    unfold localParam
    rw [map_div₀, map_neg]
  rw [h_eq]
  have hY_ne : (negFrobeniusIsog W).pullback (y_gen W) ≠ 0 := by
    intro h
    rw [h] at hY_ord
    exact WithTop.top_ne_coe ((W_smooth W).ordAtInfty_zero.symm.trans hY_ord)
  have h_neg_x_ord : (W_smooth W).ordAtInfty
      (-((negFrobeniusIsog W).pullback (x_gen W))) =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) :=
    ((W_smooth W).ordAtInfty_neg _).trans hX_ord
  refine ((W_smooth W).ord_div_concrete hY_ne
    (-2 * (Fintype.card K : ℤ)) (-3 * (Fintype.card K : ℤ))
    h_neg_x_ord hY_ord).trans ?_
  congr 1
  ring

/-- **`constantCoeff (formal id) = 0` (axiom-clean, scaffold extraction)**:
direct from `formalIsogenySeries_id = X`. -/
@[simp] theorem constantCoeff_formalIsogenySeries_id :
    PowerSeries.constantCoeff (formalIsogenySeries W (Isogeny.id W.toAffine)) = 0 := by
  rw [formalIsogenySeries_id, PowerSeries.constantCoeff_X]

/-- **`constantCoeff (formal frobenius) = 0` (axiom-clean, scaffold extraction)**:
direct from `formalIsogenySeries_frobenius = X^q` for `q ≥ 1`. -/
@[simp] theorem constantCoeff_formalIsogenySeries_frobenius
    (h : 1 ≤ Fintype.card K) :
    PowerSeries.constantCoeff (formalIsogenySeries W (frobeniusIsog W)) = 0 := by
  rw [formalIsogenySeries_frobenius, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_X_pow]
  exact if_neg (by omega)

/-- **Orderbound for denominator's lower terms**: the orderTop of
`HahnSeries.C a₁ * formalX + HahnSeries.C a₃` is ≥ -2 in `LaurentSeries K`
(since each term has orderTop ≥ -2). -/
private theorem orderTop_a₁_formalX_plus_a₃_ge_neg_two :
    ((-2 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C W.a₁ * formalX W +
        HahnSeries.C W.a₃ : LaurentSeries K).orderTop := by
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · -- -2 ≤ orderTop (C a₁ * formalX)
    rw [HahnSeries.orderTop_mul]
    -- -2 ≤ orderTop (C a₁) + orderTop formalX
    rw [formalX_orderTop]
    by_cases ha₁ : W.a₁ = 0
    · rw [ha₁, map_zero, HahnSeries.orderTop_zero, top_add]; exact le_top
    · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₁]
      rw [show ((0 : ℤ) : WithTop ℤ) + ((-2 : ℤ) : WithTop ℤ) =
          ((-2 : ℤ) : WithTop ℤ) from by push_cast; ring_nf; rfl]
  · -- -2 ≤ orderTop (C a₃)
    by_cases ha₃ : W.a₃ = 0
    · rw [ha₃, map_zero, HahnSeries.orderTop_zero]; exact le_top
    · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₃]
      exact_mod_cast (by norm_num : (-2 : ℤ) ≤ 0)

/-- **orderTop of the localExpand of the denominator = -3**: in
`LaurentSeries K`, `formalY + C a₁ * formalX + C a₃` has orderTop = -3,
since `formalY` (orderTop = -3) strictly dominates the other terms
(orderTop ≥ -2). -/
theorem orderTop_localExpand_y_gen_plus_a₁_x_gen_plus_a₃ :
    (formalY W + HahnSeries.C W.a₁ * formalX W +
        HahnSeries.C W.a₃ : LaurentSeries K).orderTop =
      ((-3 : ℤ) : WithTop ℤ) := by
  rw [show (formalY W + HahnSeries.C W.a₁ * formalX W +
        HahnSeries.C W.a₃ : LaurentSeries K) =
        (formalY W) + (HahnSeries.C W.a₁ * formalX W +
          HahnSeries.C W.a₃) from by ring]
  rw [HahnSeries.orderTop_add_eq_left]
  · exact formalY_orderTop W
  · rw [formalY_orderTop]
    refine lt_of_lt_of_le ?_ (orderTop_a₁_formalX_plus_a₃_ge_neg_two W)
    exact_mod_cast (by norm_num : (-3 : ℤ) < -2)

/-- **orderTop of `localExpand((mulByInt(-1)).pullback (localParam W)) = 1`**
(axiom-clean). The σ-image of the local parameter has orderTop = 1 in
`LaurentSeries K`: from the closed form `σ(t) = formalX / denom` (with
`denom = formalY + C(a₁)·formalX + C(a₃)` in LaurentSeries K), and:
* `orderTop formalX = -2`
* `orderTop denom = -3` (formalY dominates)
the multiplicative identity `(formalX / denom) · denom = formalX`
+ `orderTop_mul` give `orderTop (formalX / denom) + (-3) = -2`, hence
`orderTop (formalX / denom) = 1`. -/
theorem orderTop_localExpand_mulByInt_neg_one_pullback_localParam :
    (localExpand W ((mulByInt W.toAffine (-1)).pullback (localParam W))).orderTop =
      ((1 : ℤ) : WithTop ℤ) := by
  rw [mulByInt_neg_one_pullback_localParam W, map_div₀]
  rw [localExpand_x_gen, map_add, map_add, map_mul, localExpand_y_gen, localExpand_x_gen,
    localExpand_algebraMap, localExpand_algebraMap]
  rw [HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_C]
  set denom_le : LaurentSeries K :=
    formalY W + HahnSeries.C W.a₁ * formalX W +
      HahnSeries.C W.a₃ with hdenom_def
  have h_denom_orderTop : denom_le.orderTop = ((-3 : ℤ) : WithTop ℤ) :=
    orderTop_localExpand_y_gen_plus_a₁_x_gen_plus_a₃ W
  have h_denom_ne : denom_le ≠ 0 := by
    intro h
    rw [h, HahnSeries.orderTop_zero] at h_denom_orderTop
    exact WithTop.coe_ne_top h_denom_orderTop.symm
  -- Goal: (formalX W / denom_le).orderTop = ((1 : ℤ) : WithTop ℤ).
  have h_mul : (formalX W / denom_le) * denom_le = formalX W :=
    div_mul_cancel₀ _ h_denom_ne
  have h_mul_ord : ((formalX W / denom_le) * denom_le).orderTop = (formalX W).orderTop := by
    rw [h_mul]
  rw [HahnSeries.orderTop_mul] at h_mul_ord
  rw [h_denom_orderTop, formalX_orderTop W] at h_mul_ord
  -- h_mul_ord : orderTop (formalX / denom_le) + ↑(-3) = ↑(-2).
  -- Solve: orderTop (formalX / denom_le) = ↑(-2) - ↑(-3) = ↑1.
  have h_target : (formalX W / denom_le).orderTop +
      ((-3 : ℤ) : WithTop ℤ) = ((-2 : ℤ) : WithTop ℤ) := h_mul_ord
  -- Extract the value.
  have h_ne_top : (formalX W / denom_le).orderTop ≠ ⊤ := by
    intro h
    rw [h, top_add] at h_target
    exact WithTop.top_ne_coe h_target
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h_ne_top
  rw [← hn] at h_target
  rw [← WithTop.coe_add] at h_target
  have hn_eq : n + (-3) = -2 := by exact_mod_cast h_target
  have : n = 1 := by omega
  rw [← hn]
  exact_mod_cast this

/-- **`coeff 1 (formal negFrob) = 0` (witness-parametric on orderTop ≥ 1)**:
given that `localExpand((mulByInt(-1)).pullback (localParam W))` has
`orderTop ≥ 1` (i.e., the σ-image of the local parameter is itself a
uniformizer at infinity), the q-th power has orderTop ≥ q ≥ 2 (for q ≥ 2),
so `coeff 1 = 0`. -/
theorem coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness
    (hq : 2 ≤ Fintype.card K)
    (h_orderTop : ((1 : ℤ) : WithTop ℤ) ≤
      (localExpand W ((mulByInt W.toAffine (-1)).pullback (localParam W))).orderTop) :
    PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) = 0 := by
  rw [formalIsogenySeries_coeff, negFrobeniusIsog_pullback_localParam_eq_pow, map_pow]
  -- Goal: ((localExpand σ_lp)^q).coeff (1 : ℤ) = 0.
  -- We'll show orderTop ≥ q ≥ 2 > 1, then apply coeff_eq_zero_of_lt_orderTop.
  set S := localExpand W ((mulByInt W.toAffine (-1)).pullback (localParam W))
  have h_smul_one : Fintype.card K • ((1 : ℤ) : WithTop ℤ) =
      ((Fintype.card K : ℤ) : WithTop ℤ) := by simp
  have h_pow_orderTop : ((Fintype.card K : ℤ) : WithTop ℤ) ≤ (S ^ Fintype.card K).orderTop := by
    have h_smul : Fintype.card K • S.orderTop ≤ (S ^ Fintype.card K).orderTop :=
      HahnSeries.orderTop_nsmul_le_orderTop_pow
    refine le_trans ?_ h_smul
    rw [← h_smul_one]
    exact nsmul_le_nsmul_right h_orderTop (Fintype.card K)
  have h_lt : ((1 : ℤ) : WithTop ℤ) < (S ^ Fintype.card K).orderTop := by
    refine lt_of_lt_of_le ?_ h_pow_orderTop
    exact_mod_cast (by linarith : (1 : ℤ) < (Fintype.card K : ℤ))
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop h_lt

/-- **`constantCoeff (formal negFrob) = 0` (axiom-clean, unconditional)** for q ≥ 1.

Same orderTop argument as `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`,
but for `coeff 0` (= constantCoeff). Holds for any q ≥ 1 (since orderTop ≥ q ≥ 1 > 0).

This discharges the `h_β_const` hypothesis of
`formalIsogenySeries_add_coeff_one_via_FGL` (`FormalIsogenySeries.lean`)
for β = negFrobeniusIsog. -/
@[simp] theorem constantCoeff_formalIsogenySeries_negFrobeniusIsog
    (hq : 1 ≤ Fintype.card K) :
    PowerSeries.constantCoeff (formalIsogenySeries W (negFrobeniusIsog W)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalIsogenySeries_coeff,
    negFrobeniusIsog_pullback_localParam_eq_pow, map_pow]
  set S := localExpand W ((mulByInt W.toAffine (-1)).pullback (localParam W))
  have h_S_orderTop : ((1 : ℤ) : WithTop ℤ) ≤ S.orderTop :=
    (orderTop_localExpand_mulByInt_neg_one_pullback_localParam W).symm.le
  have h_smul_one : Fintype.card K • ((1 : ℤ) : WithTop ℤ) =
      ((Fintype.card K : ℤ) : WithTop ℤ) := by simp
  have h_pow_orderTop : ((Fintype.card K : ℤ) : WithTop ℤ) ≤ (S ^ Fintype.card K).orderTop := by
    have h_smul : Fintype.card K • S.orderTop ≤ (S ^ Fintype.card K).orderTop :=
      HahnSeries.orderTop_nsmul_le_orderTop_pow
    refine le_trans ?_ h_smul
    rw [← h_smul_one]
    exact nsmul_le_nsmul_right h_S_orderTop (Fintype.card K)
  have h_lt : ((0 : ℤ) : WithTop ℤ) < (S ^ Fintype.card K).orderTop := by
    refine lt_of_lt_of_le ?_ h_pow_orderTop
    exact_mod_cast (by linarith : (0 : ℤ) < (Fintype.card K : ℤ))
  exact HahnSeries.coeff_eq_zero_of_lt_orderTop h_lt

/-- **`coeff 1 (formal negFrob) = 0` (axiom-clean, unconditional)** for q ≥ 2.

Discharges the orderTop witness in
`coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness` using
the axiom-clean `orderTop_localExpand_mulByInt_neg_one_pullback_localParam = 1`.

This is the cascade collapse: with this `coeff 1 (formal negFrob) = 0`
in hand, the `h_negfrob` hypothesis of
`coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_witnesses`
(helper 4 from previous batch) discharges, leaving only the BRIDGE-003
leading-coefficient additivity to close IV.1.4 step 2 unconditionally. -/
theorem coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero
    (hq : 2 ≤ Fintype.card K) :
    PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) = 0 :=
  coeff_one_formalIsogenySeries_negFrobeniusIsog_of_orderTop_witness W hq
    (orderTop_localExpand_mulByInt_neg_one_pullback_localParam W).symm.le

/-- **BRIDGE-001 for `negFrobeniusIsog` (axiom-clean, UNCONDITIONAL)** for q ≥ 2.

Both sides equal 0:
* LHS: `omegaPullbackCoeff(negFrob) = 0` (axiom-clean, Differential.lean)
* RHS: `algebraMap (coeff 1 (formal negFrob)) = algebraMap 0 = 0` (axiom-clean,
  prior commit `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero`).

This BRIDGE-001 instance is one of the three needed by the additivity bridge
`omegaPullbackCoeff_add_of_leading_witness` for the
`γ = id + (-π)` case. Combined with `omegaPullbackCoeff_eq_formalIsogenyLeading_id`
(axiom-clean, FormalIsogenySeries.lean), the only remaining BRIDGE-001 is for
`γ = isogOneSub_negFrobenius` itself. -/
theorem omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog
    (hq : 2 ≤ Fintype.card K) :
    omegaPullbackCoeff W (negFrobeniusIsog W) =
      algebraMap K W.toAffine.FunctionField
        (PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W))) := by
  rw [coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero W hq, map_zero]
  exact omegaPullbackCoeff_negFrobeniusIsog W

/-- **Leading-coefficient closure for `isogOneSub_negFrobenius` (axiom-clean,
witness-parametric)**: from
* the additivity decomposition `h_add : coeff 1 (formal (id + (-π))) =
  coeff 1 (formal id) + coeff 1 (formal (-π))` (Silverman IV.1.4 / formal
  group law leading-order additivity), and
* `h_negfrob : coeff 1 (formal (-π)) = 0` (Silverman III.5.5 inseparability
  on `−π = mulByInt(-1) ∘ π`),
combine with the existing axiom-clean `coeff_one_formalIsogenySeries_id = 1`
to conclude `coeff 1 (formal (id + (-π))) = 1`.

This is Silverman IV.1.4's substantive arithmetic content for the
`isogOneSub_negFrobenius` case, factored as a witness consumer that
plumbs the (still-missing) BRIDGE-003 leading-order additivity and the
(also missing but Frobenius-flavored) `(-π)` linear-coeff vanishing into
the closed-form `1 + 0 = 1`. -/
theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_witnesses
    (hq : 2 ≤ Fintype.card K)
    (h_add : PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)))
    (h_negfrob : PowerSeries.coeff 1
        (formalIsogenySeries W (negFrobeniusIsog W)) = 0) :
    PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = 1 := by
  rw [h_add, coeff_one_formalIsogenySeries_id, h_negfrob, add_zero]

/-- **IV.1.4 step 2: closer (axiom-clean, witness-parametric on h_add ONLY)**.

With `coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero` (axiom-clean
unconditional from the localExpand → orderTop bridge), `h_negfrob` is
discharged automatically. The remaining hypothesis `h_add` is the
BRIDGE-003 leading-coefficient additivity for the specific
`id + (-π)` decomposition.

Once BRIDGE-003 is closed for this case, `coeff 1 (formal γ) = 1` ships
unconditionally and feeds directly into the omega-pullback Witness #1
chain (commits 45-48). -/
theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_h_add
    (hq : 2 ≤ Fintype.card K)
    (h_add : PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W))) :
    PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = 1 :=
  coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_of_witnesses W hq h_add
    (coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero W hq)

/-- **`coeff 1 (formal isogOneSub_negFrobenius) = 1` (axiom-clean,
witness-parametric on BRIDGE-003 for our case)**: given the BRIDGE-003
identity `formal γ = subst F (formal id, formal negFrob)` for our case,
applies `coeff_one_subst_bivariate` (axiom-clean from FormalIsogenySeries.lean)
+ the formal group law's leading coefficients + the axiom-clean constantCoeff
witnesses to conclude.

Closes IV.1.4 step 2 unconditionally up to one named witness: BRIDGE-003 for
`id + (-π)`. -/
theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_003 :
      formalIsogenySeries W (isogOneSub_negFrobenius W hq) =
        MvPowerSeries.subst
          (![formalIsogenySeries W (Isogeny.id W.toAffine),
             formalIsogenySeries W (negFrobeniusIsog W)] :
            Fin 2 → PowerSeries K)
          (formalGroupLaw W).toMvPowerSeries) :
    PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = 1 := by
  rw [h_bridge_003]
  rw [coeff_one_subst_bivariate (formalGroupLaw W).toMvPowerSeries
    (formalGroupLaw_coeff_single_zero_one W)
    (formalGroupLaw_coeff_single_one_one W)
    (constantCoeff_formalGroupLaw W)
    (formalIsogenySeries W (Isogeny.id W.toAffine))
    (formalIsogenySeries W (negFrobeniusIsog W))
    (constantCoeff_formalIsogenySeries_id W)
    (constantCoeff_formalIsogenySeries_negFrobeniusIsog W (by omega))]
  rw [coeff_one_formalIsogenySeries_id W,
    coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero W hq, add_zero]

/-- **Witness #1 omega-coefficient closer (axiom-clean, witness-parametric on
BRIDGE-001 for γ + leading-additivity)**: takes BRIDGE-001 for the addition
isogeny γ = `isogOneSub_negFrobenius` and the leading-coefficient additivity
for `id + (-π)`, and produces `omegaPullbackCoeff(γ) = 1`.

Composes:
* `omegaPullbackCoeff_add_of_leading_witness` (axiom-clean, FormalIsogenySeries.lean)
* `omegaPullbackCoeff_eq_formalIsogenyLeading_id` (axiom-clean)
* `omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog` (axiom-clean,
  this file)
* `omegaPullbackCoeff_id`, `omegaPullbackCoeff_negFrobeniusIsog`
  (axiom-clean, prior commits)

Result: `omegaPullbackCoeff(γ) = omegaPullbackCoeff(id) + omegaPullbackCoeff(negFrob)
= 1 + 0 = 1`. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq))))
    (h_leading_add : PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W))) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 := by
  have h_omega_add := omegaPullbackCoeff_add_of_leading_witness W
    (Isogeny.id W.toAffine) (negFrobeniusIsog W) (isogOneSub_negFrobenius W hq)
    (omegaPullbackCoeff_eq_formalIsogenyLeading_id W)
    (omegaPullbackCoeff_eq_formalIsogenyLeading_negFrobeniusIsog W hq)
    h_bridge_γ h_leading_add
  rw [h_omega_add, omegaPullbackCoeff_id W, omegaPullbackCoeff_negFrobeniusIsog W,
    add_zero]

/-- **Witness #1 (witness-parametric on BRIDGE-001 for γ + leading-additivity,
axiom-clean)**: separability of `isogOneSub_negFrobenius W hq`, taking only
the BRIDGE-001 for γ + leading-coefficient additivity. T-II-4-004 absorbed.

Once BRIDGE-001 for γ + the leading-additivity (= BRIDGE-003 specialization)
land, this fires the unconditional Witness #1 of the Hasse-Weil bound. -/
theorem isogOneSub_negFrobenius_isSeparable_of_bridge_and_leading
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq))))
    (h_leading_add : PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W))) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  isogOneSub_negFrobenius_isSeparable_of_h_coeff_only W hq
    (omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading W hq
      h_bridge_γ h_leading_add)

/-- **Witness #1 closer (axiom-clean) taking BRIDGE-001 for γ + BRIDGE-003
for our case**: with both substantive witnesses in hand, produces
`(isogOneSub_negFrobenius W hq).IsSeparable`.

Chain:
1. BRIDGE-003 for our case → `coeff 1 (formal γ) = 1`
   (via `coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003`).
2. Leading-additivity follows trivially: `1 = 1 + 0`.
3. BRIDGE-001 for γ + leading-additivity → `omegaPullbackCoeff(γ) = 1`
   (via the existing `isogOneSub_negFrobenius_isSeparable_of_bridge_and_leading`).
4. T-II-4-004 (axiom-clean) → IsSeparable. -/
theorem isogOneSub_negFrobenius_isSeparable_of_bridge_001_γ_and_bridge_003
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_001_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq))))
    (h_bridge_003 :
      formalIsogenySeries W (isogOneSub_negFrobenius W hq) =
        MvPowerSeries.subst
          (![formalIsogenySeries W (Isogeny.id W.toAffine),
             formalIsogenySeries W (negFrobeniusIsog W)] :
            Fin 2 → PowerSeries K)
          (formalGroupLaw W).toMvPowerSeries) :
    (isogOneSub_negFrobenius W hq).IsSeparable := by
  have h_coeff_γ : PowerSeries.coeff 1
      (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = 1 :=
    coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003
      W hq h_bridge_003
  have h_leading_add :
      PowerSeries.coeff 1 (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) := by
    rw [h_coeff_γ, coeff_one_formalIsogenySeries_id W,
      coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero W hq, add_zero]
  exact isogOneSub_negFrobenius_isSeparable_of_bridge_and_leading W hq
    h_bridge_001_γ h_leading_add

/-- **omegaPullbackCoeff(γ) = 1 axiom-clean given BRIDGE-001 for γ + BRIDGE-003 for our case**.
Direct consequence: derives `coeff 1 (formal γ) = 1` from BRIDGE-003 via the
just-shipped via_bridge_003 closer, then leading-additivity follows trivially
(both sides = 1), then the existing
`omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading`
fires. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_bridge_001_γ_and_bridge_003
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_001_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq))))
    (h_bridge_003 :
      formalIsogenySeries W (isogOneSub_negFrobenius W hq) =
        MvPowerSeries.subst
          (![formalIsogenySeries W (Isogeny.id W.toAffine),
             formalIsogenySeries W (negFrobeniusIsog W)] :
            Fin 2 → PowerSeries K)
          (formalGroupLaw W).toMvPowerSeries) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 := by
  have h_coeff_γ : PowerSeries.coeff 1
      (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = 1 :=
    coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_via_bridge_003
      W hq h_bridge_003
  have h_leading_add :
      PowerSeries.coeff 1 (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) := by
    rw [h_coeff_γ, coeff_one_formalIsogenySeries_id W,
      coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero W hq, add_zero]
  exact omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading W hq
    h_bridge_001_γ h_leading_add

/-- **Sub-helper 1**: `localExpand(x_gen - π·x_gen) = formalX - formalX^q`
(axiom-clean). Direct from `localExpand` ring hom + `frobeniusIsog_pullback_apply`. -/
theorem localExpand_x_gen_sub_frobenius_pullback_x_gen :
    localExpand W (x_gen W - (frobeniusIsog W).pullback (x_gen W)) =
      formalX W - (formalX W) ^ Fintype.card K := by
  rw [frobeniusIsog_pullback_apply, map_sub, map_pow, localExpand_x_gen]

/-- **Sub-helper 2**: `(formalX - formalX^q).orderTop = -2q` for q ≥ 2.
For q ≥ 2, `formalX^q` strictly dominates `formalX` (orderTop -2q < -2),
so by `orderTop_add_eq_right`, the sum's orderTop = orderTop(-formalX^q) = -2q. -/
theorem orderTop_formalX_sub_formalX_pow (hq : 2 ≤ Fintype.card K) :
    (formalX W - (formalX W) ^ Fintype.card K : LaurentSeries K).orderTop =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [sub_eq_add_neg]
  have hX_orderTop : (formalX W).orderTop = ((-2 : ℤ) : WithTop ℤ) := formalX_orderTop W
  have hX_pow_orderTop : ((formalX W) ^ Fintype.card K : LaurentSeries K).orderTop =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) :=
    formalX_pow_orderTop W (Fintype.card K)
  have hX_neg_pow_orderTop :
      (-((formalX W) ^ Fintype.card K) : LaurentSeries K).orderTop =
      ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
    rw [HahnSeries.orderTop_neg, hX_pow_orderTop]
  have h_lt : (-((formalX W) ^ Fintype.card K) : LaurentSeries K).orderTop <
      (formalX W).orderTop := by
    rw [hX_neg_pow_orderTop, hX_orderTop]
    have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    refine WithTop.coe_lt_coe.mpr ?_
    push_cast
    nlinarith
  rw [HahnSeries.orderTop_add_eq_right h_lt, hX_neg_pow_orderTop]

/-- **Sub-helper 3**: `localExpand((x_gen - π·x_gen)²) = (formalX - formalX^q)²`.
Direct from `localExpand` ring hom + `localExpand_x_gen_sub_frobenius_pullback_x_gen`. -/
theorem localExpand_x_gen_sub_frob_pullback_x_gen_sq :
    localExpand W ((x_gen W - (frobeniusIsog W).pullback (x_gen W)) ^ 2) =
      (formalX W - (formalX W) ^ Fintype.card K) ^ 2 := by
  rw [map_pow, localExpand_x_gen_sub_frobenius_pullback_x_gen]

/-- **Sub-helper 4**: `((formalX - formalX^q)²).orderTop = -4q` for q ≥ 2.
By `orderTop_mul` + `orderTop_formalX_sub_formalX_pow`. -/
theorem orderTop_formalX_sub_formalX_pow_sq (hq : 2 ≤ Fintype.card K) :
    ((formalX W - (formalX W) ^ Fintype.card K) ^ 2 : LaurentSeries K).orderTop =
      ((-4 * (Fintype.card K : ℤ)) : WithTop ℤ) := by
  rw [sq, HahnSeries.orderTop_mul, orderTop_formalX_sub_formalX_pow W hq]
  -- Goal: ((-2 * K : ℤ) : WithTop ℤ) + ((-2 * K : ℤ) : WithTop ℤ) = ((-4 * K : ℤ) : WithTop ℤ)
  rw [show ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) +
        ((-2 * (Fintype.card K : ℤ)) : WithTop ℤ) =
        (((-2 * (Fintype.card K : ℤ) + -2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
      from (WithTop.coe_add _ _).symm]
  congr 1
  ring

/-- **Sub-helper 5**: `localExpand(x_gen · (π·x_gen)²) = formalX^(2q+1)`.
The dominant term of `addPullbackNumerator_reduced_negFrobenius` at infinity. -/
theorem localExpand_x_gen_mul_frob_pullback_x_gen_sq :
    localExpand W (x_gen W * (frobeniusIsog W).pullback (x_gen W) ^ 2) =
      (formalX W) ^ (2 * Fintype.card K + 1) := by
  rw [frobeniusIsog_pullback_apply, ← pow_mul, map_mul, map_pow, localExpand_x_gen]
  ring

/-- **Sub-helper 6**: `(formalX^(2q+1)).orderTop = -4q - 2` for q ≥ 1.
Direct from `formalX_pow_orderTop`. -/
theorem orderTop_formalX_pow_two_q_plus_one :
    ((formalX W) ^ (2 * Fintype.card K + 1) : LaurentSeries K).orderTop =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [formalX_pow_orderTop]
  congr 1
  push_cast
  ring

/-- **Sub-helper 7**: `(formalX^(2q+1)).leadingCoeff = 1`.
Direct from `formalX_pow_leadingCoeff`. -/
theorem leadingCoeff_formalX_pow_two_q_plus_one :
    ((formalX W) ^ (2 * Fintype.card K + 1) : LaurentSeries K).leadingCoeff = 1 :=
  formalX_pow_leadingCoeff W (2 * Fintype.card K + 1)

/-- **Sub-helper 8**: `(localExpand(x_gen · (π·x_gen)²)).orderTop = -2 - 4q`. Composes
the dominant-term identification with the orderTop computation. -/
theorem orderTop_localExpand_x_gen_mul_frob_pullback_x_gen_sq :
    (localExpand W (x_gen W * (frobeniusIsog W).pullback (x_gen W) ^ 2)).orderTop =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [localExpand_x_gen_mul_frob_pullback_x_gen_sq W]
  exact orderTop_formalX_pow_two_q_plus_one W

/-- **Sub-helper 9**: `(localExpand(x_gen · (π·x_gen)²)).leadingCoeff = 1`. The
leading coefficient at infinity of the dominant term is 1 (rather than 0 or
some other value), which feeds into the leading-coefficient analysis for
`addPullback_x` and ultimately `coeff 1 (formal γ) = 1`. -/
theorem leadingCoeff_localExpand_x_gen_mul_frob_pullback_x_gen_sq :
    (localExpand W (x_gen W * (frobeniusIsog W).pullback (x_gen W) ^ 2)).leadingCoeff = 1 := by
  rw [localExpand_x_gen_mul_frob_pullback_x_gen_sq W]
  exact leadingCoeff_formalX_pow_two_q_plus_one W

/-- **Sub-helper 10**: `(formalY^n).orderTop = -3 * n`.
Mirror of `formalX_pow_orderTop`. -/
theorem formalY_pow_orderTop (n : ℕ) :
    ((formalY W) ^ n : LaurentSeries K).orderTop =
      (((-3 * n : ℤ)) : WithTop ℤ) := by
  induction n with
  | zero =>
    rw [pow_zero]
    change (1 : LaurentSeries K).orderTop = _
    rw [HahnSeries.orderTop_one]
    rfl
  | succ k ih =>
    rw [pow_succ, HahnSeries.orderTop_mul, ih, formalY_orderTop]
    rw [show ((((-3 : ℤ) * (k : ℤ)) : ℤ) : WithTop ℤ) +
          ((-3 : ℤ) : WithTop ℤ) =
          (((((-3 : ℤ) * (k : ℤ) + (-3 : ℤ)) : ℤ)) : WithTop ℤ)
        from (WithTop.coe_add _ _).symm]
    congr 1
    push_cast
    ring

/-- **Sub-helper 11**: `localExpand(y_gen · π·y_gen) = formalY · formalY^q`.
Direct from `localExpand` ring hom + `frobeniusIsog_pullback_apply`. -/
theorem localExpand_y_gen_mul_frob_pullback_y_gen :
    localExpand W (y_gen W * (frobeniusIsog W).pullback (y_gen W)) =
      formalY W * (formalY W) ^ Fintype.card K := by
  rw [frobeniusIsog_pullback_apply, map_mul, map_pow, localExpand_y_gen]

/-- **Sub-helper 12**: `(formalY · formalY^q).orderTop = -3 - 3q` for q ≥ 1.
Direct from `orderTop_mul` + `formalY_orderTop` + `formalY_pow_orderTop`. -/
theorem orderTop_formalY_mul_formalY_pow :
    (formalY W * (formalY W) ^ Fintype.card K : LaurentSeries K).orderTop =
      (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [HahnSeries.orderTop_mul, formalY_orderTop, formalY_pow_orderTop, ← WithTop.coe_add,
    show ((-3 : ℤ) + -3 * (Fintype.card K : ℤ)) = -3 - 3 * (Fintype.card K : ℤ) from by ring]

/-- **Sub-helper 13**: `localExpand(x_gen² · π·x_gen) = formalX^(q+2)`.
The "term 6" of `addPullbackNumerator_reduced_negFrobenius`: `x² · π·x` with
orderTop -4 - 2q (sub-dominant). -/
theorem localExpand_x_gen_sq_mul_frob_pullback_x_gen :
    localExpand W (x_gen W ^ 2 * (frobeniusIsog W).pullback (x_gen W)) =
      (formalX W) ^ (Fintype.card K + 2) := by
  rw [frobeniusIsog_pullback_apply, ← pow_add, map_pow, localExpand_x_gen]
  congr 1
  ring

/-- **Sub-helper 14**: `(formalX^(q+2)).orderTop = -4 - 2q`. -/
theorem orderTop_formalX_pow_q_plus_two :
    ((formalX W) ^ (Fintype.card K + 2) : LaurentSeries K).orderTop =
      (((-4 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [formalX_pow_orderTop]
  congr 1
  push_cast
  ring

/-- **Sub-helper 15**: `localExpand(x_gen · π·x_gen) = formalX^(q+1)`.
The "x · π·x" component (used in term 8 of `addPullbackNumerator_reduced`). -/
theorem localExpand_x_gen_mul_frob_pullback_x_gen :
    localExpand W (x_gen W * (frobeniusIsog W).pullback (x_gen W)) =
      (formalX W) ^ (Fintype.card K + 1) := by
  rw [frobeniusIsog_pullback_apply, map_mul, map_pow, localExpand_x_gen,
    show Fintype.card K + 1 = 1 + Fintype.card K from by ring, pow_add, pow_one]

/-- **Sub-helper 16**: `(formalX^(q+1)).orderTop = -2 - 2q`. -/
theorem orderTop_formalX_pow_q_plus_one :
    ((formalX W) ^ (Fintype.card K + 1) : LaurentSeries K).orderTop =
      (((-2 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [formalX_pow_orderTop]
  congr 1
  push_cast
  ring

/-- **Sub-helper 17**: `localExpand(x_gen + π·x_gen) = formalX + formalX^q`.
Term 1's "x + π·x" component (used in `a₄ · (x + π·x)`). -/
theorem localExpand_x_gen_add_frob_pullback_x_gen :
    localExpand W (x_gen W + (frobeniusIsog W).pullback (x_gen W)) =
      formalX W + (formalX W) ^ Fintype.card K := by
  rw [frobeniusIsog_pullback_apply, map_add, map_pow, localExpand_x_gen]

/-- **Sub-helper 18**: `(formalX + formalX^q).orderTop ≥ -2q` for q ≥ 1.
Via `min_orderTop_le_orderTop_add` + `formalX_orderTop` + `formalX_pow_orderTop`. -/
theorem orderTop_formalX_add_formalX_pow_ge_neg_two_q (hq : 2 ≤ Fintype.card K) :
    (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (formalX W + (formalX W) ^ Fintype.card K : LaurentSeries K).orderTop := by
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · -- -2q ≤ orderTop formalX = -2
    rw [formalX_orderTop]
    have h_q : (1 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast (le_of_lt (by exact_mod_cast hq))
    refine WithTop.coe_le_coe.mpr ?_
    nlinarith
  · -- -2q ≤ orderTop formalX^q = -2q
    rw [formalX_pow_orderTop]

/-- **Sub-helper 19**: `localExpand(y_gen + π·y_gen) = formalY + formalY^q`.
Term 3's "y + π·y" component (used in `a₃ · (y + π·y)`). -/
theorem localExpand_y_gen_add_frob_pullback_y_gen :
    localExpand W (y_gen W + (frobeniusIsog W).pullback (y_gen W)) =
      formalY W + (formalY W) ^ Fintype.card K := by
  rw [frobeniusIsog_pullback_apply, map_add, map_pow, localExpand_y_gen]

/-- **Sub-helper 20**: `(formalY + formalY^q).orderTop ≥ -3q` for q ≥ 1.
Via `min_orderTop_le_orderTop_add` + `formalY_orderTop` + `formalY_pow_orderTop`. -/
theorem orderTop_formalY_add_formalY_pow_ge_neg_three_q (hq : 2 ≤ Fintype.card K) :
    (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (formalY W + (formalY W) ^ Fintype.card K : LaurentSeries K).orderTop := by
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · rw [formalY_orderTop]
    have h_q : (1 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast (le_of_lt (by exact_mod_cast hq))
    refine WithTop.coe_le_coe.mpr ?_
    nlinarith
  · rw [formalY_pow_orderTop]

/-- **Sub-helper 21**: `localExpand(x · π·y) = formalX · formalY^q`. -/
theorem localExpand_x_gen_mul_frob_pullback_y_gen :
    localExpand W (x_gen W * (frobeniusIsog W).pullback (y_gen W)) =
      formalX W * (formalY W) ^ Fintype.card K := by
  rw [frobeniusIsog_pullback_apply, map_mul, map_pow, localExpand_x_gen, localExpand_y_gen]

/-- **Sub-helper 22**: `(formalX · formalY^q).orderTop = -2 - 3q`. -/
theorem orderTop_formalX_mul_formalY_pow :
    (formalX W * (formalY W) ^ Fintype.card K : LaurentSeries K).orderTop =
      (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [HahnSeries.orderTop_mul, formalX_orderTop, formalY_pow_orderTop, ← WithTop.coe_add,
    show ((-2 : ℤ) + (-3 : ℤ) * (Fintype.card K : ℤ)) =
        -2 - 3 * (Fintype.card K : ℤ) from by ring]

/-- **Sub-helper 23**: `localExpand(π·x · y) = formalX^q · formalY`. -/
theorem localExpand_frob_pullback_x_gen_mul_y_gen :
    localExpand W ((frobeniusIsog W).pullback (x_gen W) * y_gen W) =
      (formalX W) ^ Fintype.card K * formalY W := by
  rw [frobeniusIsog_pullback_apply, map_mul, map_pow, localExpand_x_gen, localExpand_y_gen]

/-- **Sub-helper 24**: `(formalX^q · formalY).orderTop = -3 - 2q`. -/
theorem orderTop_formalX_pow_mul_formalY :
    ((formalX W) ^ Fintype.card K * formalY W : LaurentSeries K).orderTop =
      (((-3 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [HahnSeries.orderTop_mul, formalX_pow_orderTop, formalY_orderTop, ← WithTop.coe_add,
    show ((-2 : ℤ) * (Fintype.card K : ℤ) + (-3 : ℤ)) =
        -3 - 2 * (Fintype.card K : ℤ) from by ring]

/-- **Sub-helper 25**: `(formalX·formalY^q + formalX^q·formalY).orderTop ≥ -2 - 3q`
for q ≥ 2. Via `min_orderTop_le_orderTop_add`, since `-2-3q ≤ min(-2-3q, -3-2q)` for q ≥ 2. -/
theorem orderTop_formalX_mul_formalY_pow_plus_formalX_pow_mul_formalY_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (formalX W * (formalY W) ^ Fintype.card K +
        (formalX W) ^ Fintype.card K * formalY W : LaurentSeries K).orderTop := by
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · rw [orderTop_formalX_mul_formalY_pow]
  · rw [orderTop_formalX_pow_mul_formalY]
    have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    refine WithTop.coe_le_coe.mpr ?_
    nlinarith

/-- **Sub-helper 26**: `(HahnSeries.C c).orderTop ≥ 0` for any `c : K`.
Helper for term 2 (`2·a₆`) and similar constant-coefficient bounds. -/
theorem orderTop_HahnSeries_C_ge_zero (c : K) :
    (0 : WithTop ℤ) ≤ (HahnSeries.C c : LaurentSeries K).orderTop := by
  by_cases hc : c = 0
  · rw [hc, map_zero, HahnSeries.orderTop_zero]
    exact le_top
  · rw [HahnSeries.C_apply, HahnSeries.orderTop_single hc]
    rfl

/-- **Sub-helper 27**: `localExpand W (algebraMap K KE c) = HahnSeries.C c`.
Direct from `localExpand_algebraMap` + `HahnSeries.ofPowerSeries_C`. The
constant-coefficient bridge: `algebraMap K KE` factors through `localExpand`
to give a constant Hahn series. -/
theorem localExpand_algebraMap_eq_C (c : K) :
    localExpand W (algebraMap K KE c) = HahnSeries.C c := by
  rw [localExpand_algebraMap]
  exact HahnSeries.ofPowerSeries_C c

/-- **Sub-helper 28**: `(localExpand W (algebraMap K KE c * f)).orderTop ≥
(localExpand W f).orderTop`. The constant factor `algebraMap K KE c` has
orderTop ≥ 0 in the local expansion (it's a constant Hahn series), so
multiplication by it does not decrease the orderTop. Bridge for terms 1, 3, 5
of `addPullbackNumerator_reduced_negFrobenius` (the `aᵢ · ...` terms). -/
theorem orderTop_localExpand_algebraMap_mul_ge (c : K) (f : KE) :
    (localExpand W f).orderTop ≤
      (localExpand W (algebraMap K KE c * f)).orderTop := by
  rw [map_mul, localExpand_algebraMap_eq_C, HahnSeries.orderTop_mul]
  have hC := orderTop_HahnSeries_C_ge_zero (K := K) c
  calc (localExpand W f).orderTop
      = 0 + (localExpand W f).orderTop := (zero_add _).symm
    _ ≤ (HahnSeries.C c : LaurentSeries K).orderTop + (localExpand W f).orderTop := by
        gcongr

/-- **Sub-helper 29**: `(localExpand W (2 * f)).orderTop ≥ (localExpand W f).orderTop`.
Bridge for terms 4, 7 of `addPullbackNumerator_reduced_negFrobenius` (the `2·...`
terms). Uses `2 * f = f + f` to dodge characteristic-2 considerations. -/
theorem orderTop_localExpand_two_mul_ge (f : KE) :
    (localExpand W f).orderTop ≤ (localExpand W ((2 : KE) * f)).orderTop := by
  rw [show ((2 : KE) * f) = f + f from by ring, map_add]
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  exact le_min (le_refl _) (le_refl _)

/-- **Sub-helper 30**: `(localExpand W (-f)).orderTop = (localExpand W f).orderTop`.
Negation preserves orderTop. -/
theorem orderTop_localExpand_neg (f : KE) :
    (localExpand W (-f)).orderTop = (localExpand W f).orderTop := by
  rw [map_neg, HahnSeries.orderTop_neg]

/-- **Sub-helper 31**:
`localExpand((negFrob).pullback y_gen) = -formalY^q - C(a₁)·formalX^q - C(a₃)`.
Direct from `negFrobeniusIsog_pullback_y_gen` + ring-hom facts. -/
theorem localExpand_negFrobeniusIsog_pullback_y_gen :
    localExpand W ((negFrobeniusIsog W).pullback (y_gen W)) =
      -((formalY W) ^ Fintype.card K) -
        HahnSeries.C W.a₁ * (formalX W) ^ Fintype.card K -
        HahnSeries.C W.a₃ := by
  rw [negFrobeniusIsog_pullback_y_gen, map_sub, map_sub, map_neg, map_mul,
    frobeniusIsog_pullback_apply, frobeniusIsog_pullback_apply, map_pow, map_pow,
    localExpand_y_gen, localExpand_x_gen, localExpand_algebraMap_eq_C,
    localExpand_algebraMap_eq_C]

/-- **Sub-helper 32**: `(C(a₁)·formalX^q + C(a₃)).orderTop ≥ -2q` for q ≥ 1. -/
theorem orderTop_C_a₁_mul_formalX_pow_plus_C_a₃_ge :
    (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C W.a₁ * (formalX W) ^ Fintype.card K +
        HahnSeries.C W.a₃ : LaurentSeries K).orderTop := by
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · -- C(a₁) · formalX^q has orderTop ≥ -2q
    rw [HahnSeries.orderTop_mul, formalX_pow_orderTop]
    by_cases ha₁ : W.a₁ = 0
    · rw [ha₁, map_zero, HahnSeries.orderTop_zero, top_add]
      exact le_top
    · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₁]
      push_cast
      ring_nf
      rw [zero_add]
  · -- C(a₃) has orderTop ≥ -2q (since orderTop ≥ 0 ≥ -2q)
    refine le_trans ?_ (orderTop_HahnSeries_C_ge_zero W.a₃)
    refine WithTop.coe_le_coe.mpr ?_
    have : (Fintype.card K : ℤ) ≥ 0 := by positivity
    nlinarith

/-- **Sub-helper 33**: `(localExpand((negFrob).pullback y_gen)).orderTop = -3q`
for q ≥ 2. The `formalY^q` term dominates strictly. -/
theorem orderTop_localExpand_negFrobeniusIsog_pullback_y_gen
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W ((negFrobeniusIsog W).pullback (y_gen W))).orderTop =
      (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [localExpand_negFrobeniusIsog_pullback_y_gen W]
  -- Goal: orderTop(-formalY^q - C(a₁)·formalX^q - C(a₃)) = -3q
  rw [show -((formalY W) ^ Fintype.card K) -
        HahnSeries.C W.a₁ * (formalX W) ^ Fintype.card K -
        HahnSeries.C W.a₃ =
        (-((formalY W) ^ Fintype.card K)) +
          (-(HahnSeries.C W.a₁ * (formalX W) ^ Fintype.card K +
            HahnSeries.C W.a₃))
      from by ring]
  have h_neg_y_pow : (-((formalY W) ^ Fintype.card K) : LaurentSeries K).orderTop =
      (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.orderTop_neg, formalY_pow_orderTop]
  have h_rest_ge : (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (-(HahnSeries.C W.a₁ * (formalX W) ^ Fintype.card K +
        HahnSeries.C W.a₃) : LaurentSeries K).orderTop := by
    rw [HahnSeries.orderTop_neg]
    exact orderTop_C_a₁_mul_formalX_pow_plus_C_a₃_ge W
  have h_lt : (-((formalY W) ^ Fintype.card K) : LaurentSeries K).orderTop <
      (-(HahnSeries.C W.a₁ * (formalX W) ^ Fintype.card K +
        HahnSeries.C W.a₃) : LaurentSeries K).orderTop := by
    rw [h_neg_y_pow]
    refine lt_of_lt_of_le ?_ h_rest_ge
    have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    refine WithTop.coe_lt_coe.mpr ?_
    nlinarith
  rw [HahnSeries.orderTop_add_eq_left h_lt, h_neg_y_pow]

/-- **Sub-helper 34**: `(C(a₃) · formalY).orderTop ≥ -3` for q ≥ 1. -/
theorem orderTop_C_a₃_mul_formalY_ge :
    (((-3 : ℤ)) : WithTop ℤ) ≤
      (HahnSeries.C W.a₃ * formalY W : LaurentSeries K).orderTop := by
  rw [HahnSeries.orderTop_mul, formalY_orderTop]
  by_cases ha₃ : W.a₃ = 0
  · rw [ha₃, map_zero, HahnSeries.orderTop_zero, top_add]
    exact le_top
  · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₃,
        show ((0 : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) from rfl, zero_add]

/-- **Sub-helper 35**: `(C(a₁) · (formalY · formalX^q)).orderTop ≥ -2-3q`
for q ≥ 1. -/
theorem orderTop_C_a₁_mul_formalY_mul_formalX_pow_ge (hq : 1 ≤ Fintype.card K) :
    (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C W.a₁ * (formalY W * (formalX W) ^ Fintype.card K)
        : LaurentSeries K).orderTop := by
  rw [HahnSeries.orderTop_mul, HahnSeries.orderTop_mul,
    formalY_orderTop, formalX_pow_orderTop]
  by_cases ha₁ : W.a₁ = 0
  · rw [ha₁, map_zero, HahnSeries.orderTop_zero, top_add]
    exact le_top
  · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₁]
    rw [show ((0 : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) from rfl, zero_add]
    rw [show ((-3 : ℤ) : WithTop ℤ) +
          ((-2 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) =
          (((-3 + -2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ)
        from (WithTop.coe_add _ _).symm]
    refine WithTop.coe_le_coe.mpr ?_
    have h_q : (1 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    omega

/-- **Sub-helper 36**: `localExpand(y · negFrob.π·y) = -formalY · formalY^q -
C(a₁) · (formalY · formalX^q) - C(a₃) · formalY`. -/
theorem localExpand_y_gen_mul_negFrobeniusIsog_pullback_y_gen :
    localExpand W (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) =
      -(formalY W * (formalY W) ^ Fintype.card K) -
        HahnSeries.C W.a₁ * (formalY W * (formalX W) ^ Fintype.card K) -
        HahnSeries.C W.a₃ * formalY W := by
  rw [map_mul, localExpand_negFrobeniusIsog_pullback_y_gen, localExpand_y_gen]
  ring

/-- **Sub-helper 37**: `(localExpand(y · negFrob.π·y)).orderTop ≥ -3-3q` for q ≥ 2.
Each of the three terms has orderTop ≥ -3-3q:
* `-formalY · formalY^q`: = -3-3q (sub-helper 12).
* `-C(a₁) · (formalY · formalX^q)`: ≥ -2-3q ≥ -3-3q (sub-helper 35).
* `-C(a₃) · formalY`: ≥ -3 ≥ -3-3q for q ≥ 0 (sub-helper 34). -/
theorem orderTop_localExpand_y_gen_mul_negFrobeniusIsog_pullback_y_gen_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (y_gen W *
        (negFrobeniusIsog W).pullback (y_gen W))).orderTop := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  rw [localExpand_y_gen_mul_negFrobeniusIsog_pullback_y_gen]
  rw [show -(formalY W * (formalY W) ^ Fintype.card K) -
        HahnSeries.C W.a₁ * (formalY W * (formalX W) ^ Fintype.card K) -
        HahnSeries.C W.a₃ * formalY W =
      -(formalY W * (formalY W) ^ Fintype.card K) +
        (-(HahnSeries.C W.a₁ *
          (formalY W * (formalX W) ^ Fintype.card K)) +
        -(HahnSeries.C W.a₃ * formalY W))
      from by ring]
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · rw [HahnSeries.orderTop_neg, orderTop_formalY_mul_formalY_pow]
  · refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
    refine le_min ?_ ?_
    · rw [HahnSeries.orderTop_neg]
      refine le_trans ?_ (orderTop_C_a₁_mul_formalY_mul_formalX_pow_ge W
        (by linarith : 1 ≤ Fintype.card K))
      refine WithTop.coe_le_coe.mpr ?_
      linarith
    · rw [HahnSeries.orderTop_neg]
      refine le_trans ?_ (orderTop_C_a₃_mul_formalY_ge W)
      refine WithTop.coe_le_coe.mpr ?_
      have h_q_nn : (0 : ℤ) ≤ (Fintype.card K : ℤ) := by positivity
      linarith

/-- **Sub-helper 38**: `(localExpand(y_gen + (negFrob).pullback y_gen)).orderTop = -3q`
for q ≥ 2. The `(negFrob).pullback y_gen` part dominates strictly (orderTop -3q
< -3 for q ≥ 2). -/
theorem orderTop_localExpand_y_gen_add_negFrobeniusIsog_pullback_y_gen
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (y_gen W +
        (negFrobeniusIsog W).pullback (y_gen W))).orderTop =
      (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [map_add, localExpand_y_gen]
  -- formalY + localExpand((negFrob).π·y), with -3q < -3 for q ≥ 2.
  have h_negFrob_y :
      (localExpand W ((negFrobeniusIsog W).pullback (y_gen W))).orderTop =
        (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) :=
    orderTop_localExpand_negFrobeniusIsog_pullback_y_gen W hq
  have h_lt : (localExpand W ((negFrobeniusIsog W).pullback (y_gen W))).orderTop <
      (formalY W).orderTop := by
    rw [h_negFrob_y, formalY_orderTop]
    have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    refine WithTop.coe_lt_coe.mpr ?_
    nlinarith
  rw [HahnSeries.orderTop_add_eq_right h_lt, h_negFrob_y]

/-- **Sub-helper 39**: `(localExpand(a₃ · (y_gen + (negFrob).pullback y_gen))).orderTop ≥ -3q`. -/
theorem orderTop_localExpand_a₃_mul_y_gen_add_negFrobeniusIsog_pullback_y_gen_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (algebraMap K W.toAffine.FunctionField W.a₃ *
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)))).orderTop := by
  refine le_trans ?_ (orderTop_localExpand_algebraMap_mul_ge W W.a₃ _)
  rw [orderTop_localExpand_y_gen_add_negFrobeniusIsog_pullback_y_gen W hq]

/-- **Sub-helper 40**: `(localExpand(x_gen + (negFrob).pullback x_gen)).orderTop ≥ -2q`
for q ≥ 2. Uses the fact that `(negFrob).pullback x_gen = (frob).pullback x_gen`. -/
theorem orderTop_localExpand_x_gen_add_negFrobeniusIsog_pullback_x_gen_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (x_gen W +
        (negFrobeniusIsog W).pullback (x_gen W))).orderTop := by
  rw [negFrobeniusIsog_pullback_x_gen, localExpand_x_gen_add_frob_pullback_x_gen]
  exact orderTop_formalX_add_formalX_pow_ge_neg_two_q W hq

/-- **Sub-helper 41**: `(localExpand(a₄ · (x_gen + (negFrob).pullback x_gen))).orderTop ≥ -2q`. -/
theorem orderTop_localExpand_a₄_mul_x_gen_add_negFrobeniusIsog_pullback_x_gen_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (algebraMap K W.toAffine.FunctionField W.a₄ *
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)))).orderTop := by
  refine le_trans ?_ (orderTop_localExpand_algebraMap_mul_ge W W.a₄ _)
  exact orderTop_localExpand_x_gen_add_negFrobeniusIsog_pullback_x_gen_ge W hq

/-- **Sub-helper 42**: `(localExpand(2·a₆)).orderTop ≥ 0`. -/
theorem orderTop_localExpand_two_mul_a₆_ge :
    (0 : WithTop ℤ) ≤
      (localExpand W ((2 : W.toAffine.FunctionField) *
        algebraMap K W.toAffine.FunctionField W.a₆)).orderTop := by
  refine le_trans ?_ (orderTop_localExpand_two_mul_ge W _)
  rw [localExpand_algebraMap_eq_C]
  exact orderTop_HahnSeries_C_ge_zero W.a₆

/-- **Sub-helper 43**: `(localExpand(2 · y_gen · (negFrob).π·y)).orderTop ≥ -3-3q`. -/
theorem orderTop_localExpand_two_mul_y_gen_mul_negFrob_π_y_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W ((2 : W.toAffine.FunctionField) * y_gen W *
        (negFrobeniusIsog W).pullback (y_gen W))).orderTop := by
  rw [show ((2 : W.toAffine.FunctionField) * y_gen W *
        (negFrobeniusIsog W).pullback (y_gen W)) =
      (2 : W.toAffine.FunctionField) *
        (y_gen W * (negFrobeniusIsog W).pullback (y_gen W)) from by ring]
  refine le_trans ?_ (orderTop_localExpand_two_mul_ge W _)
  exact orderTop_localExpand_y_gen_mul_negFrobeniusIsog_pullback_y_gen_ge W hq

/-- **Sub-helper 44**: `(localExpand(x_gen² · (negFrob).π·x)).orderTop = -4 - 2q`. -/
theorem orderTop_localExpand_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen :
    (localExpand W (x_gen W ^ 2 *
        (negFrobeniusIsog W).pullback (x_gen W))).orderTop =
      (((-4 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen, localExpand_x_gen_sq_mul_frob_pullback_x_gen]
  exact orderTop_formalX_pow_q_plus_two W

/-- **Sub-helper 45**: `(localExpand(x_gen · ((negFrob).π·x)²)).orderTop = -2 - 4q`.
The DOMINANT term of `addPullbackNumerator_reduced_negFrobenius`. -/
theorem orderTop_localExpand_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq :
    (localExpand W (x_gen W *
        ((negFrobeniusIsog W).pullback (x_gen W)) ^ 2)).orderTop =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact orderTop_localExpand_x_gen_mul_frob_pullback_x_gen_sq W

/-- **Sub-helper 46**: `(localExpand(2 · a₂ · x_gen · (negFrob).π·x)).orderTop ≥ -2 - 2q`. -/
theorem orderTop_localExpand_two_mul_a₂_mul_x_gen_mul_negFrob_π_x_ge :
    (((-2 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W ((2 : W.toAffine.FunctionField) *
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
        (negFrobeniusIsog W).pullback (x_gen W))).orderTop := by
  rw [show ((2 : W.toAffine.FunctionField) *
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
        (negFrobeniusIsog W).pullback (x_gen W)) =
      (2 : W.toAffine.FunctionField) *
        (algebraMap K W.toAffine.FunctionField W.a₂ *
          (x_gen W * (negFrobeniusIsog W).pullback (x_gen W))) from by ring]
  refine le_trans ?_ (orderTop_localExpand_two_mul_ge W _)
  refine le_trans ?_ (orderTop_localExpand_algebraMap_mul_ge W W.a₂ _)
  rw [negFrobeniusIsog_pullback_x_gen,
    localExpand_x_gen_mul_frob_pullback_x_gen]
  exact (orderTop_formalX_pow_q_plus_one W).symm.le

/-- **Sub-helper 47**: `(localExpand(x · (negFrob).π·y)).orderTop = -2 - 3q` for q ≥ 2. -/
theorem orderTop_localExpand_x_gen_mul_negFrob_pullback_y_gen
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (x_gen W * (negFrobeniusIsog W).pullback (y_gen W))).orderTop =
      (((-2 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [map_mul, localExpand_x_gen, HahnSeries.orderTop_mul, formalX_orderTop,
    orderTop_localExpand_negFrobeniusIsog_pullback_y_gen W hq, ← WithTop.coe_add,
    show ((-2 : ℤ) + (-3 : ℤ) * (Fintype.card K : ℤ)) =
        -2 - 3 * (Fintype.card K : ℤ) from by ring]

/-- **Sub-helper 48**: `(localExpand((negFrob).π·x · y)).orderTop = -3 - 2q`. -/
theorem orderTop_localExpand_negFrob_pullback_x_gen_mul_y_gen :
    (localExpand W ((negFrobeniusIsog W).pullback (x_gen W) * y_gen W)).orderTop =
      (((-3 - 2 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen, localExpand_frob_pullback_x_gen_mul_y_gen]
  exact orderTop_formalX_pow_mul_formalY W

/-- **Sub-helper 49** (Term 5 inner): `(localExpand(x · negFrob.π·y +
negFrob.π·x · y)).orderTop ≥ -3-3q` for q ≥ 2. The `min_orderTop_le_orderTop_add`
extracts both summands. Sub-helper 47 = -2-3q ≥ -3-3q, sub-helper 48 = -3-2q ≥ -3-3q. -/
theorem orderTop_localExpand_x_gen_mul_negFrob_π_y_plus_negFrob_π_x_mul_y_gen_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
        (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)).orderTop := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  rw [map_add]
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · rw [orderTop_localExpand_x_gen_mul_negFrob_pullback_y_gen W hq]
    refine WithTop.coe_le_coe.mpr ?_
    linarith
  · rw [orderTop_localExpand_negFrob_pullback_x_gen_mul_y_gen]
    refine WithTop.coe_le_coe.mpr ?_
    linarith

/-- **Sub-helper 50** (Term 5 outer): `(localExpand(a₁ · (x · negFrob.π·y +
negFrob.π·x · y))).orderTop ≥ -3-3q` for q ≥ 2. Composition of sub-helpers 28 + 49. -/
theorem orderTop_localExpand_a₁_mul_x_negFrob_π_y_plus_negFrob_π_x_y_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (algebraMap K W.toAffine.FunctionField W.a₁ *
        (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
          (negFrobeniusIsog W).pullback (x_gen W) * y_gen W))).orderTop := by
  refine le_trans ?_ (orderTop_localExpand_algebraMap_mul_ge W W.a₁ _)
  exact orderTop_localExpand_x_gen_mul_negFrob_π_y_plus_negFrob_π_x_mul_y_gen_ge W hq

/-- **Sub-helper 51** (Term 1 promoted): `(localExpand(a₄ · (x_gen +
negFrob.π·x))).orderTop ≥ -3-3q` for q ≥ 1. From sub-helper 41 (≥ -2q). -/
theorem orderTop_localExpand_a₄_mul_x_gen_add_negFrob_π_x_promoted
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (algebraMap K W.toAffine.FunctionField W.a₄ *
        (x_gen W + (negFrobeniusIsog W).pullback (x_gen W)))).orderTop := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  refine le_trans ?_ (orderTop_localExpand_a₄_mul_x_gen_add_negFrobeniusIsog_pullback_x_gen_ge W hq)
  refine WithTop.coe_le_coe.mpr ?_
  linarith

/-- **Sub-helper 52** (Term 2 promoted): `(localExpand(2·a₆)).orderTop ≥ -3-3q`. -/
theorem orderTop_localExpand_two_mul_a₆_promoted
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W ((2 : W.toAffine.FunctionField) *
        algebraMap K W.toAffine.FunctionField W.a₆)).orderTop := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  refine le_trans ?_ (orderTop_localExpand_two_mul_a₆_ge W)
  refine WithTop.coe_le_coe.mpr ?_
  linarith

/-- **Sub-helper 53** (Term 3 promoted): `(localExpand(a₃ · (y_gen +
negFrob.π·y))).orderTop ≥ -3-3q`. From sub-helper 39 (≥ -3q). -/
theorem orderTop_localExpand_a₃_mul_y_gen_add_negFrob_π_y_promoted
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (algebraMap K W.toAffine.FunctionField W.a₃ *
        (y_gen W + (negFrobeniusIsog W).pullback (y_gen W)))).orderTop := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  refine le_trans ?_ (orderTop_localExpand_a₃_mul_y_gen_add_negFrobeniusIsog_pullback_y_gen_ge W hq)
  refine WithTop.coe_le_coe.mpr ?_
  linarith

/-- **Sub-helper 54** (Term 6 promoted): `(localExpand(x² · negFrob.π·x)).orderTop ≥ -3-3q`.
From sub-helper 44 (= -4-2q). -/
theorem orderTop_localExpand_x_gen_sq_mul_negFrob_π_x_promoted
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (x_gen W ^ 2 *
        (negFrobeniusIsog W).pullback (x_gen W))).orderTop := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  rw [orderTop_localExpand_x_gen_sq_mul_negFrobeniusIsog_pullback_x_gen W]
  refine WithTop.coe_le_coe.mpr ?_
  linarith

/-- **Sub-helper 55** (Term 8 promoted): `(localExpand(2·a₂·x·negFrob.π·x)).orderTop ≥ -3-3q`.
From sub-helper 46 (≥ -2-2q). -/
theorem orderTop_localExpand_two_a₂_x_negFrob_π_x_promoted
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W ((2 : W.toAffine.FunctionField) *
        algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
        (negFrobeniusIsog W).pullback (x_gen W))).orderTop := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  refine le_trans ?_ (orderTop_localExpand_two_mul_a₂_mul_x_gen_mul_negFrob_π_x_ge W)
  refine WithTop.coe_le_coe.mpr ?_
  linarith

/-- **Sub-helper 56**: `add_ge_of_both_ge` — addition preserves orderTop bounds. -/
theorem orderTop_add_ge_of_both_ge {a b : LaurentSeries K} {n : WithTop ℤ}
    (ha : n ≤ a.orderTop) (hb : n ≤ b.orderTop) :
    n ≤ (a + b).orderTop :=
  le_trans (le_min ha hb) HahnSeries.min_orderTop_le_orderTop_add

/-- **Sub-helper 57**: `sub_ge_of_both_ge` — subtraction preserves orderTop bounds.
Uses `HahnSeries.orderTop_neg` to convert `b` ↔ `-b`. -/
theorem orderTop_sub_ge_of_both_ge {a b : LaurentSeries K} {n : WithTop ℤ}
    (ha : n ≤ a.orderTop) (hb : n ≤ b.orderTop) :
    n ≤ (a - b).orderTop := by
  rw [sub_eq_add_neg]
  refine orderTop_add_ge_of_both_ge ha ?_
  rw [HahnSeries.orderTop_neg]
  exact hb

/-- **Sub-helper 58** (Cumulative sum): `(localExpand(rest)).orderTop ≥ -3-3q`,
where `rest` is `addPullbackNumerator_reduced_negFrobenius` minus the dominant
term `x · (negFrob.π·x)²`. Sequential `add/sub_ge_of_both_ge` chain over
the 7 sub-dominant term bounds. -/
theorem orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge
    (hq : 2 ≤ Fintype.card K) :
    (((-3 - 3 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) ≤
      (localExpand W (
        algebraMap K W.toAffine.FunctionField W.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₆
          - algebraMap K W.toAffine.FunctionField W.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : W.toAffine.FunctionField) * y_gen W *
              (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K W.toAffine.FunctionField W.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
              (negFrobeniusIsog W).pullback (x_gen W))).orderTop := by
  have h_t1 := orderTop_localExpand_a₄_mul_x_gen_add_negFrob_π_x_promoted W hq
  have h_t2 := orderTop_localExpand_two_mul_a₆_promoted W hq
  have h_t3 := orderTop_localExpand_a₃_mul_y_gen_add_negFrob_π_y_promoted W hq
  have h_t4 := orderTop_localExpand_two_mul_y_gen_mul_negFrob_π_y_ge W hq
  have h_t5 := orderTop_localExpand_a₁_mul_x_negFrob_π_y_plus_negFrob_π_x_y_ge W hq
  have h_t6 := orderTop_localExpand_x_gen_sq_mul_negFrob_π_x_promoted W hq
  have h_t7 := orderTop_localExpand_two_a₂_x_negFrob_π_x_promoted W hq
  -- Distribute localExpand across the addition/subtraction.
  simp only [map_add, map_sub]
  -- Goal: -3-3q ≤ (((((((T1) + T2) - T3) - T4) - T5) + T6) + T7).orderTop
  refine orderTop_add_ge_of_both_ge ?_ h_t7
  refine orderTop_add_ge_of_both_ge ?_ h_t6
  refine orderTop_sub_ge_of_both_ge ?_ h_t5
  refine orderTop_sub_ge_of_both_ge ?_ h_t4
  refine orderTop_sub_ge_of_both_ge ?_ h_t3
  exact orderTop_add_ge_of_both_ge h_t1 h_t2

/-- **MAIN THEOREM** (LaurentSeries-side mirror of
`ordAtInfty_addPullbackNumerator_reduced_negFrobenius_eq`):
`(localExpand(addPullbackNumerator_reduced_negFrobenius)).orderTop = -2-4q`
for q ≥ 2.

Algebraic decomposition: the full expression is `rest + dominant`, where
* `dominant = x_gen · (negFrob.π·x)²` has orderTop = -2-4q (sub-helper 45)
* `rest` (the other 7 terms) has orderTop ≥ -3-3q (sub-helper 58)

For q ≥ 2: -2-4q < -3-3q, so `orderTop_add_eq_right` extracts the dominant
orderTop. -/
theorem orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullbackNumerator_reduced_negFrobenius W)).orderTop =
      (((-2 - 4 * (Fintype.card K : ℤ)) : ℤ) : WithTop ℤ) := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  -- Algebraic decomposition: full = rest + dominant.
  have h_eq : addPullbackNumerator_reduced_negFrobenius W =
      (algebraMap K W.toAffine.FunctionField W.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₆
          - algebraMap K W.toAffine.FunctionField W.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : W.toAffine.FunctionField) * y_gen W *
              (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K W.toAffine.FunctionField W.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
              (negFrobeniusIsog W).pullback (x_gen W)) +
      (x_gen W * ((negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    unfold addPullbackNumerator_reduced_negFrobenius
    ring
  rw [h_eq, map_add]
  -- Goal: orderTop(localExpand(rest) + localExpand(dominant)) = -2-4q
  have h_rest := orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge W hq
  have h_dom := orderTop_localExpand_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq W
  -- Strict non-arch: dominant strictly less than rest, so add_eq_right applies.
  have h_lt : (localExpand W (x_gen W *
      ((negFrobeniusIsog W).pullback (x_gen W)) ^ 2)).orderTop <
      (localExpand W (
        algebraMap K W.toAffine.FunctionField W.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₆
          - algebraMap K W.toAffine.FunctionField W.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : W.toAffine.FunctionField) * y_gen W *
              (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K W.toAffine.FunctionField W.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
              (negFrobeniusIsog W).pullback (x_gen W))).orderTop := by
    rw [h_dom]
    refine lt_of_lt_of_le ?_ h_rest
    refine WithTop.coe_lt_coe.mpr ?_
    linarith
  rw [HahnSeries.orderTop_add_eq_right h_lt, h_dom]

/-- **Leading coefficient companion**:
`(localExpand(addPullbackNumerator_reduced_negFrobenius)).leadingCoeff = 1`
for q ≥ 2. The leading coefficient of the dominant term `x_gen · (negFrob.π·x)²`
is 1 (sub-helper 9 / `leadingCoeff_localExpand_x_gen_mul_frob_pullback_x_gen_sq`),
which propagates through the strict-non-arch via `leadingCoeff_add_eq_right`. -/
theorem leadingCoeff_localExpand_addPullbackNumerator_reduced_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullbackNumerator_reduced_negFrobenius W)).leadingCoeff = 1 := by
  have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
  have h_eq : addPullbackNumerator_reduced_negFrobenius W =
      (algebraMap K W.toAffine.FunctionField W.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₆
          - algebraMap K W.toAffine.FunctionField W.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : W.toAffine.FunctionField) * y_gen W *
              (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K W.toAffine.FunctionField W.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
              (negFrobeniusIsog W).pullback (x_gen W)) +
      (x_gen W * ((negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    unfold addPullbackNumerator_reduced_negFrobenius
    ring
  rw [h_eq, map_add]
  have h_rest := orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_rest_ge W hq
  have h_dom := orderTop_localExpand_x_gen_mul_negFrobeniusIsog_pullback_x_gen_sq W
  have h_lt : (localExpand W (x_gen W *
      ((negFrobeniusIsog W).pullback (x_gen W)) ^ 2)).orderTop <
      (localExpand W (
        algebraMap K W.toAffine.FunctionField W.a₄ *
            (x_gen W + (negFrobeniusIsog W).pullback (x_gen W))
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₆
          - algebraMap K W.toAffine.FunctionField W.a₃ *
              (y_gen W + (negFrobeniusIsog W).pullback (y_gen W))
          - (2 : W.toAffine.FunctionField) * y_gen W *
              (negFrobeniusIsog W).pullback (y_gen W)
          - algebraMap K W.toAffine.FunctionField W.a₁ *
              (x_gen W * (negFrobeniusIsog W).pullback (y_gen W) +
               (negFrobeniusIsog W).pullback (x_gen W) * y_gen W)
          + x_gen W ^ 2 * (negFrobeniusIsog W).pullback (x_gen W)
          + (2 : W.toAffine.FunctionField) *
              algebraMap K W.toAffine.FunctionField W.a₂ * x_gen W *
              (negFrobeniusIsog W).pullback (x_gen W))).orderTop := by
    rw [h_dom]
    refine lt_of_lt_of_le ?_ h_rest
    refine WithTop.coe_lt_coe.mpr ?_
    linarith
  rw [HahnSeries.leadingCoeff_add_eq_right h_lt]
  -- Now: leadingCoeff(localExpand(dominant)) = 1.
  rw [show (x_gen W * ((negFrobeniusIsog W).pullback (x_gen W)) ^ 2) =
      x_gen W * ((negFrobeniusIsog W).pullback (x_gen W)) ^ 2 from rfl,
    negFrobeniusIsog_pullback_x_gen]
  exact leadingCoeff_localExpand_x_gen_mul_frob_pullback_x_gen_sq W

/-- **Sub-helper 61**: `(formalX - formalX^q).leadingCoeff = -1` for q ≥ 2.
The dominant term `-formalX^q` (orderTop -2q < -2) determines the leading
coefficient via `leadingCoeff_add_eq_right`. -/
theorem leadingCoeff_formalX_sub_formalX_pow (hq : 2 ≤ Fintype.card K) :
    (formalX W - (formalX W) ^ Fintype.card K : LaurentSeries K).leadingCoeff = -1 := by
  rw [sub_eq_add_neg]
  have h_lt : (-((formalX W) ^ Fintype.card K) : LaurentSeries K).orderTop <
      (formalX W).orderTop := by
    rw [HahnSeries.orderTop_neg, formalX_pow_orderTop, formalX_orderTop]
    have h_q : (2 : ℤ) ≤ (Fintype.card K : ℤ) := by exact_mod_cast hq
    refine WithTop.coe_lt_coe.mpr ?_
    nlinarith
  rw [HahnSeries.leadingCoeff_add_eq_right h_lt, HahnSeries.leadingCoeff_neg,
    formalX_pow_leadingCoeff]

/-- **Sub-helper 62**: `((formalX - formalX^q)²).leadingCoeff = 1` for q ≥ 2.
Direct from `HahnSeries.leadingCoeff_mul` (squared) and sub-helper 61
(`(-1)² = 1`). -/
theorem leadingCoeff_formalX_sub_formalX_pow_sq (hq : 2 ≤ Fintype.card K) :
    ((formalX W - (formalX W) ^ Fintype.card K) ^ 2 : LaurentSeries K).leadingCoeff = 1 := by
  rw [sq, HahnSeries.leadingCoeff_mul, leadingCoeff_formalX_sub_formalX_pow W hq]
  ring

/-- **Sub-helper 63**: `(localExpand((x_gen - negFrob.π·x)²)).orderTop = -4q` for q ≥ 2.
Bridges via `negFrobeniusIsog_pullback_x_gen` to the frobenius-side sub-helper 4. -/
theorem orderTop_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W ((x_gen W -
      (negFrobeniusIsog W).pullback (x_gen W)) ^ 2)).orderTop =
      ((-4 * (Fintype.card K : ℤ) : ℤ) : WithTop ℤ) := by
  rw [negFrobeniusIsog_pullback_x_gen, localExpand_x_gen_sub_frob_pullback_x_gen_sq]
  exact orderTop_formalX_sub_formalX_pow_sq W hq

/-- **Sub-helper 64**: `(localExpand((x_gen - negFrob.π·x)²)).leadingCoeff = 1` for q ≥ 2. -/
theorem leadingCoeff_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W ((x_gen W -
      (negFrobeniusIsog W).pullback (x_gen W)) ^ 2)).leadingCoeff = 1 := by
  rw [negFrobeniusIsog_pullback_x_gen, localExpand_x_gen_sub_frob_pullback_x_gen_sq]
  exact leadingCoeff_formalX_sub_formalX_pow_sq W hq

/-- **Sub-helper 65**: `(localExpand((x_gen - negFrob.π·x)²)) ≠ 0` for q ≥ 2.
Direct from orderTop being a finite value. -/
theorem localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_ne_zero
    (hq : 2 ≤ Fintype.card K) :
    localExpand W ((x_gen W -
      (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) ≠ 0 := by
  intro h
  have h_top : (localExpand W ((x_gen W -
      (negFrobeniusIsog W).pullback (x_gen W)) ^ 2)).orderTop = ⊤ := by
    rw [h]; exact HahnSeries.orderTop_zero
  rw [orderTop_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq W hq] at h_top
  exact WithTop.coe_ne_top h_top

/-- **Sub-helper 65b**: `(x_gen - negFrob.π·x) ≠ 0` in K(E). Derived from the
LaurentSeries-side fact `(formalX - formalX^q).orderTop = -2q ≠ ⊤`. -/
private theorem x_gen_sub_negFrob_pullback_x_gen_ne_zero_local
    (hq : 2 ≤ Fintype.card K) :
    (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ≠ 0 := by
  intro h
  have h_zero : localExpand W
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) = 0 := by
    rw [h]; exact map_zero _
  rw [negFrobeniusIsog_pullback_x_gen,
    localExpand_x_gen_sub_frobenius_pullback_x_gen] at h_zero
  have h_top : (formalX W - (formalX W) ^ Fintype.card K
      : LaurentSeries K).orderTop = ⊤ := by
    rw [h_zero]; exact HahnSeries.orderTop_zero
  rw [orderTop_formalX_sub_formalX_pow W hq] at h_top
  exact WithTop.coe_ne_top h_top

/-- **MAIN COMPANION**: `(localExpand(addPullback_x_negFrobenius)).orderTop = -2`
for q ≥ 2. The LaurentSeries-side mirror of `ord_addPullback_x_negFrobenius`. -/
theorem orderTop_localExpand_addPullback_x_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullback_x W (negFrobeniusIsog W))).orderTop =
      ((-2 : ℤ) : WithTop ℤ) := by
  have h_pix_ne : x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_negFrob_pullback_x_gen_ne_zero_local W hq
  have h_pix_sq_ne : (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 h_pix_ne
  have h_div_eq : addPullback_x W (negFrobeniusIsog W) =
      addPullbackNumerator_negFrobenius W /
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    rw [addPullbackNumerator_negFrobenius_eq W, mul_div_cancel_left₀ _ h_pix_sq_ne]
  rw [h_div_eq, map_div₀]
  rw [HahnSeries.orderTop_div
    (localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_ne_zero W hq)]
  rw [addPullbackNumerator_negFrobenius_eq_reduced W,
    orderTop_localExpand_addPullbackNumerator_reduced_negFrobenius_eq W hq,
    orderTop_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq W hq]
  norm_cast
  omega

/-- **MAIN COMPANION**: `(localExpand(addPullback_x_negFrobenius)).leadingCoeff = 1`
for q ≥ 2. -/
theorem leadingCoeff_localExpand_addPullback_x_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullback_x W (negFrobeniusIsog W))).leadingCoeff = 1 := by
  have h_pix_ne : x_gen W - (negFrobeniusIsog W).pullback (x_gen W) ≠ 0 :=
    x_gen_sub_negFrob_pullback_x_gen_ne_zero_local W hq
  have h_pix_sq_ne : (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 h_pix_ne
  have h_div_eq : addPullback_x W (negFrobeniusIsog W) =
      addPullbackNumerator_negFrobenius W /
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) := by
    rw [addPullbackNumerator_negFrobenius_eq W, mul_div_cancel_left₀ _ h_pix_sq_ne]
  rw [h_div_eq, map_div₀]
  rw [HahnSeries.leadingCoeff_div
    (localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq_ne_zero W hq)]
  rw [addPullbackNumerator_negFrobenius_eq_reduced W,
    leadingCoeff_localExpand_addPullbackNumerator_reduced_negFrobenius_eq W hq,
    leadingCoeff_localExpand_x_gen_sub_negFrobeniusIsog_pullback_x_gen_sq W hq]
  ring

/-- **Sub-helper 66**: `localExpand(addPullback_x_negFrobenius) ≠ 0` for q ≥ 2.
Direct from orderTop being a finite value. -/
theorem localExpand_addPullback_x_negFrobenius_ne_zero
    (hq : 2 ≤ Fintype.card K) :
    localExpand W (addPullback_x W (negFrobeniusIsog W)) ≠ 0 := by
  intro h
  have h_top : (localExpand W (addPullback_x W (negFrobeniusIsog W))).orderTop = ⊤ := by
    rw [h]; exact HahnSeries.orderTop_zero
  rw [orderTop_localExpand_addPullback_x_negFrobenius_eq W hq] at h_top
  exact WithTop.coe_ne_top h_top

/-- **Sub-helper 67**: `(localExpand(addPullback_x_negFrobenius)).coeff (-2) = 1` for q ≥ 2.
Direct extraction of the leading coefficient at the leading exponent
via `HahnSeries.coeff_untop_eq_leadingCoeff` (when orderTop = -2 finite).

This is the ACTUAL coefficient value at the most-negative exponent, the
LaurentSeries-side input for the IV.1.4 step 2 leading-coefficient
computation. -/
theorem coeff_neg_two_localExpand_addPullback_x_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullback_x W (negFrobeniusIsog W))).coeff (-2 : ℤ) = 1 := by
  have h_orderTop := orderTop_localExpand_addPullback_x_negFrobenius_eq W hq
  have h_leadingCoeff := leadingCoeff_localExpand_addPullback_x_negFrobenius_eq W hq
  have h_ne_top : (localExpand W (addPullback_x W (negFrobeniusIsog W))).orderTop ≠ ⊤ := by
    rw [h_orderTop]; exact WithTop.coe_ne_top
  have h_untop : (localExpand W (addPullback_x W (negFrobeniusIsog W))).orderTop.untop h_ne_top
      = (-2 : ℤ) := by
    apply WithTop.coe_inj.mp
    rw [WithTop.coe_untop]
    exact h_orderTop
  rw [← h_untop, HahnSeries.coeff_untop_eq_leadingCoeff]
  exact h_leadingCoeff

/-- **Sub-helper 68**: `((localExpand addPullback_x)^2).orderTop = -4`. -/
theorem orderTop_localExpand_addPullback_x_negFrobenius_sq
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_x W (negFrobeniusIsog W))) ^ 2 :
        LaurentSeries K).orderTop =
      ((-4 : ℤ) : WithTop ℤ) := by
  rw [sq, HahnSeries.orderTop_mul,
    orderTop_localExpand_addPullback_x_negFrobenius_eq W hq, ← WithTop.coe_add]
  congr 1

/-- **Sub-helper 69**: `((localExpand addPullback_x)^3).orderTop = -6`. -/
theorem orderTop_localExpand_addPullback_x_negFrobenius_cube
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_x W (negFrobeniusIsog W))) ^ 3 :
        LaurentSeries K).orderTop =
      ((-6 : ℤ) : WithTop ℤ) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, HahnSeries.orderTop_mul,
    orderTop_localExpand_addPullback_x_negFrobenius_sq W hq,
    orderTop_localExpand_addPullback_x_negFrobenius_eq W hq, ← WithTop.coe_add]
  congr 1

/-- **Sub-helper 70**: `localExpand(addPullback_y)` is nonzero for q ≥ 2.
Direct from `localExpand` being a ring hom to a field + addPullback_y ≠ 0
(via `ord_addPullback_y_negFrobenius`). -/
theorem localExpand_addPullback_y_negFrobenius_ne_zero
    (hq : 2 ≤ Fintype.card K) :
    localExpand W (addPullback_y W (negFrobeniusIsog W)) ≠ 0 := by
  intro h
  have h_inj : Function.Injective (localExpand W) := (localExpand W).injective
  have h_y_eq_zero : addPullback_y W (negFrobeniusIsog W) = 0 := by
    have := h_inj (h.trans (map_zero _).symm)
    exact this
  have h_y_ord := ord_addPullback_y_negFrobenius W hq
  rw [h_y_eq_zero] at h_y_ord
  exact WithTop.top_ne_coe ((W_smooth W).ordAtInfty_zero.symm.trans h_y_ord)

/-- **Sub-helper 71**: localExpand of the curve equation
`Y² + a₁·X·Y + a₃·Y = X³ + a₂·X² + a₄·X + a₆` applied to the addPullback
coordinates. Direct from `addPullback_equation` + `localExpand` ring hom.

Note: `localExpand W ((W_KE W).toAffine.a_i)` is just `HahnSeries.C` of `a_i`,
expanding via `localExpand_algebraMap_eq_C`. -/
theorem localExpand_addPullback_curve_equation :
    (localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W))) +
      HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W))) =
      (localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 +
      HahnSeries.C W.a₂ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₄ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
      HahnSeries.C W.a₆ := by
  have h := addPullback_equation (negFrobeniusIsog_addNonInverse W)
  rw [WeierstrassCurve.Affine.equation_iff] at h
  have h_le := congrArg (localExpand W) h
  simp only [map_add, map_mul, map_pow] at h_le
  -- Replace `localExpand (algebraMap K KE a_i) = HahnSeries.C a_i`
  have ha₁ : localExpand W ((W_KE W).toAffine.a₁) = HahnSeries.C W.a₁ :=
    localExpand_algebraMap_eq_C W W.a₁
  have ha₂ : localExpand W ((W_KE W).toAffine.a₂) = HahnSeries.C W.a₂ :=
    localExpand_algebraMap_eq_C W W.a₂
  have ha₃ : localExpand W ((W_KE W).toAffine.a₃) = HahnSeries.C W.a₃ :=
    localExpand_algebraMap_eq_C W W.a₃
  have ha₄ : localExpand W ((W_KE W).toAffine.a₄) = HahnSeries.C W.a₄ :=
    localExpand_algebraMap_eq_C W W.a₄
  have ha₆ : localExpand W ((W_KE W).toAffine.a₆) = HahnSeries.C W.a₆ :=
    localExpand_algebraMap_eq_C W W.a₆
  rw [ha₁, ha₂, ha₃, ha₄, ha₆] at h_le
  exact h_le

/-- **Sub-helper 72**: `(localExpand(a₂·X² + a₄·X + a₆)).orderTop ≥ -4` for q ≥ 2.
The non-cubic RHS terms have orderTop bounded by -4 (since `a₂·X²` has
orderTop ≥ -4 = orderTop X² when a₂ ≠ 0, and `a₄·X` has orderTop ≥ -2 ≥ -4,
and `a₆` has orderTop ≥ 0 ≥ -4). -/
theorem orderTop_localExpand_RHS_lower_terms_ge
    (hq : 2 ≤ Fintype.card K) :
    ((-4 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C W.a₂ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
       HahnSeries.C W.a₄ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
       HahnSeries.C W.a₆ : LaurentSeries K).orderTop := by
  refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
  refine le_min ?_ ?_
  · refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
    refine le_min ?_ ?_
    · -- a₂ · X² has orderTop ≥ -4
      rw [HahnSeries.orderTop_mul,
        orderTop_localExpand_addPullback_x_negFrobenius_sq W hq]
      by_cases ha₂ : W.a₂ = 0
      · rw [ha₂, map_zero, HahnSeries.orderTop_zero, top_add]; exact le_top
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₂]
        push_cast
        rw [zero_add]
    · -- a₄ · X has orderTop ≥ -4
      rw [HahnSeries.orderTop_mul,
        orderTop_localExpand_addPullback_x_negFrobenius_eq W hq]
      by_cases ha₄ : W.a₄ = 0
      · rw [ha₄, map_zero, HahnSeries.orderTop_zero, top_add]; exact le_top
      · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₄]
        push_cast
        rw [zero_add]
        refine WithTop.coe_le_coe.mpr ?_
        norm_num
  · -- a₆ has orderTop ≥ -4 (≥ 0 actually)
    refine le_trans ?_ (orderTop_HahnSeries_C_ge_zero W.a₆)
    exact_mod_cast (by norm_num : (-4 : ℤ) ≤ 0)

/-- **Sub-helper 73**: `(localExpand(X³ + a₂·X² + a₄·X + a₆)).orderTop = -6`
for q ≥ 2. Strict non-arch with `X³` dominating (orderTop -6) and the other
terms bounded ≥ -4. -/
theorem orderTop_localExpand_addPullback_RHS_eq
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 +
      HahnSeries.C W.a₂ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₄ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
      HahnSeries.C W.a₆ : LaurentSeries K).orderTop =
      ((-6 : ℤ) : WithTop ℤ) := by
  rw [show ((localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 +
        HahnSeries.C W.a₂ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
        HahnSeries.C W.a₄ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
        HahnSeries.C W.a₆ : LaurentSeries K) =
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 +
        (HahnSeries.C W.a₂ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
        HahnSeries.C W.a₄ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
        HahnSeries.C W.a₆) from by ring]
  have h_lt :
      ((localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 :
          LaurentSeries K).orderTop <
      (HahnSeries.C W.a₂ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
       HahnSeries.C W.a₄ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
       HahnSeries.C W.a₆ : LaurentSeries K).orderTop := by
    refine lt_of_lt_of_le ?_ (orderTop_localExpand_RHS_lower_terms_ge W hq)
    rw [orderTop_localExpand_addPullback_x_negFrobenius_cube W hq]
    exact_mod_cast (by norm_num : (-6 : ℤ) < -4)
  exact (HahnSeries.orderTop_add_eq_left h_lt).trans
    (orderTop_localExpand_addPullback_x_negFrobenius_cube W hq)

/-- **Sub-helper 74** (Y-side LHS orderTop = -6): direct from sub-helper 73 +
the curve equation (sub-helper 71). -/
theorem orderTop_localExpand_addPullback_LHS_eq
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W))) +
      HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
        : LaurentSeries K).orderTop =
      ((-6 : ℤ) : WithTop ℤ) := by
  rw [localExpand_addPullback_curve_equation W]
  exact orderTop_localExpand_addPullback_RHS_eq W hq

/-- **Sub-helper 75** (extract m): `localExpand(addPullback_y).orderTop = (m : ℤ)`
for some integer `m`. Uses sub-helper 70 (≠ 0). -/
theorem exists_m_orderTop_localExpand_addPullback_y_negFrobenius
    (hq : 2 ≤ Fintype.card K) :
    ∃ m : ℤ, (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      ((m : ℤ) : WithTop ℤ) := by
  have h_ne : localExpand W (addPullback_y W (negFrobeniusIsog W)) ≠ 0 :=
    localExpand_addPullback_y_negFrobenius_ne_zero W hq
  have h_ne_top : (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop ≠ ⊤ :=
    HahnSeries.orderTop_ne_top.mpr h_ne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h_ne_top
  exact ⟨m, hm.symm⟩

/-- **Sub-helper 76** (Y² orderTop = 2m): with `m = orderTop(Y)`, `Y²` has orderTop `2m`. -/
theorem orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m
    (hq : 2 ≤ Fintype.card K) (m : ℤ)
    (hm : (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      ((m : ℤ) : WithTop ℤ)) :
    ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 :
        LaurentSeries K).orderTop =
      ((2 * m : ℤ) : WithTop ℤ) := by
  rw [sq, HahnSeries.orderTop_mul, hm, ← WithTop.coe_add]
  congr 1; ring

/-- **Sub-helper 77** (X·Y orderTop = -2 + m): -/
theorem orderTop_localExpand_addPullback_x_mul_y_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) (m : ℤ)
    (hm : (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      ((m : ℤ) : WithTop ℤ)) :
    (localExpand W (addPullback_x W (negFrobeniusIsog W)) *
        localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      (((-2 + m) : ℤ) : WithTop ℤ) := by
  rw [HahnSeries.orderTop_mul,
    orderTop_localExpand_addPullback_x_negFrobenius_eq W hq, hm,
    ← WithTop.coe_add]

/-- **Sub-helper 78** (rule out m ≥ -2): if `m ≥ -2`, then LHS orderTop ≥ -4,
contradicting LHS orderTop = -6. -/
theorem m_le_neg_three_orderTop_localExpand_addPullback_y_negFrobenius
    (hq : 2 ≤ Fintype.card K) (m : ℤ)
    (hm : (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      ((m : ℤ) : WithTop ℤ)) :
    m ≤ -3 := by
  by_contra! h_not_le
  have h_m_ge : -2 ≤ m := by omega
  -- Y² has orderTop = 2m ≥ -4
  have h_y_sq_ge : ((-4 : ℤ) : WithTop ℤ) ≤
      ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 :
          LaurentSeries K).orderTop := by
    rw [orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m W hq m hm]
    refine WithTop.coe_le_coe.mpr ?_
    linarith
  -- a₁·X·Y has orderTop ≥ -4
  have h_a1xy_ge : ((-4 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop := by
    rw [show (HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))) =
      HahnSeries.C W.a₁ *
        ((localExpand W (addPullback_x W (negFrobeniusIsog W))) *
          (localExpand W (addPullback_y W (negFrobeniusIsog W))))
        from by ring]
    rw [HahnSeries.orderTop_mul]
    have h_xy := orderTop_localExpand_addPullback_x_mul_y_negFrobenius_eq W hq m hm
    rw [h_xy]
    by_cases ha₁ : W.a₁ = 0
    · rw [ha₁, map_zero, HahnSeries.orderTop_zero, top_add]; exact le_top
    · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₁]
      push_cast
      rw [zero_add]
      refine WithTop.coe_le_coe.mpr ?_; linarith
  -- a₃·Y has orderTop ≥ -4
  have h_a3y_ge : ((-4 : ℤ) : WithTop ℤ) ≤
      (HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop := by
    rw [HahnSeries.orderTop_mul, hm]
    by_cases ha₃ : W.a₃ = 0
    · rw [ha₃, map_zero, HahnSeries.orderTop_zero, top_add]; exact le_top
    · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₃]
      push_cast
      rw [zero_add]
      refine WithTop.coe_le_coe.mpr ?_; linarith
  -- LHS orderTop ≥ -4 (sum of three terms each ≥ -4)
  have h_lhs_ge : ((-4 : ℤ) : WithTop ℤ) ≤
      ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
        HahnSeries.C W.a₁ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
          (localExpand W (addPullback_y W (negFrobeniusIsog W))) +
        HahnSeries.C W.a₃ *
          (localExpand W (addPullback_y W (negFrobeniusIsog W)))
            : LaurentSeries K).orderTop :=
    orderTop_add_ge_of_both_ge
      (orderTop_add_ge_of_both_ge h_y_sq_ge h_a1xy_ge) h_a3y_ge
  rw [orderTop_localExpand_addPullback_LHS_eq W hq] at h_lhs_ge
  have h46 : (-4 : ℤ) ≤ -6 := by exact_mod_cast h_lhs_ge
  omega

/-- **Sub-helper 79** (Y² strictly dominates a₁·X·Y, given m ≤ -3): for `m ≤ -3`,
`Y²` has orderTop = `2m ≤ -6 < -2 + m = orderTop(a₁·X·Y)`. -/
theorem orderTop_y_sq_lt_a1xy_negFrobenius
    (hq : 2 ≤ Fintype.card K) (m : ℤ) (h_m_le : m ≤ -3)
    (hm : (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      ((m : ℤ) : WithTop ℤ)) :
    ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 :
        LaurentSeries K).orderTop <
      (HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop := by
  rw [orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m W hq m hm]
  rw [show (HahnSeries.C W.a₁ *
      (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
      (localExpand W (addPullback_y W (negFrobeniusIsog W)))) =
      HahnSeries.C W.a₁ *
      ((localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W))))
      from by ring]
  rw [HahnSeries.orderTop_mul,
    orderTop_localExpand_addPullback_x_mul_y_negFrobenius_eq W hq m hm]
  by_cases ha₁ : W.a₁ = 0
  · rw [ha₁, map_zero, HahnSeries.orderTop_zero, top_add]
    exact WithTop.coe_lt_top _
  · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₁]
    push_cast
    rw [zero_add]
    refine WithTop.coe_lt_coe.mpr ?_
    linarith

/-- **Sub-helper 80** (Y² strictly dominates a₃·Y, given m ≤ -3): for `m ≤ -3`,
`Y²` has orderTop = `2m ≤ -6 < m = orderTop(a₃·Y)` (since `2m < m` for `m ≤ -3`). -/
theorem orderTop_y_sq_lt_a3y_negFrobenius
    (hq : 2 ≤ Fintype.card K) (m : ℤ) (h_m_le : m ≤ -3)
    (hm : (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      ((m : ℤ) : WithTop ℤ)) :
    ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 :
        LaurentSeries K).orderTop <
      (HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop := by
  rw [orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m W hq m hm,
    HahnSeries.orderTop_mul, hm]
  by_cases ha₃ : W.a₃ = 0
  · rw [ha₃, map_zero, HahnSeries.orderTop_zero, top_add]
    exact WithTop.coe_lt_top _
  · rw [HahnSeries.C_apply, HahnSeries.orderTop_single ha₃]
    push_cast
    rw [zero_add]
    refine WithTop.coe_lt_coe.mpr ?_
    linarith

/-- **MAIN Y-SIDE THEOREM**: `(localExpand(addPullback_y_negFrobenius)).orderTop = -3`
for q ≥ 2. Mirror of K(E)-side `ord_addPullback_y_negFrobenius`. The case
analysis from the curve equation forces `m = -3`. -/
theorem orderTop_localExpand_addPullback_y_negFrobenius_eq
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
      ((-3 : ℤ) : WithTop ℤ) := by
  obtain ⟨m, hm⟩ := exists_m_orderTop_localExpand_addPullback_y_negFrobenius W hq
  have h_m_le : m ≤ -3 := m_le_neg_three_orderTop_localExpand_addPullback_y_negFrobenius W hq m hm
  -- From m ≤ -3, Y² strictly dominates the other LHS terms.
  have h_lt_a1xy := orderTop_y_sq_lt_a1xy_negFrobenius W hq m h_m_le hm
  have h_lt_a3y := orderTop_y_sq_lt_a3y_negFrobenius W hq m h_m_le hm
  -- ord(Y² + a₁XY) = ord(Y²) (since Y² strictly less than a₁XY).
  have h_inner_eq : ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop =
      ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 :
          LaurentSeries K).orderTop :=
    HahnSeries.orderTop_add_eq_left h_lt_a1xy
  -- ord((Y² + a₁XY) + a₃Y) = ord(Y²) (since same is true for the outer addition).
  have h_lt_outer : ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop <
      (HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop := h_inner_eq ▸ h_lt_a3y
  have h_outer_eq := HahnSeries.orderTop_add_eq_left h_lt_outer
  -- Combine with LHS = -6 to get 2m = -6, m = -3.
  have h_lhs_ord : ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W))) +
      HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop =
      ((-6 : ℤ) : WithTop ℤ) := orderTop_localExpand_addPullback_LHS_eq W hq
  rw [h_outer_eq, h_inner_eq,
    orderTop_localExpand_addPullback_y_negFrobenius_sq_eq_two_m W hq m hm] at h_lhs_ord
  have h_2m : (2 * m : ℤ) = -6 := by exact_mod_cast h_lhs_ord
  rw [hm]
  congr 1
  omega

/-- **Sub-helper 84**: leadingCoeff of `(localExpand X)^3 = 1`, derived from
sub-helper main companion (`leadingCoeff(localExpand X) = 1`) + leadingCoeff_mul. -/
theorem leadingCoeff_localExpand_addPullback_x_negFrobenius_cube_eq
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_x W (negFrobeniusIsog W))) ^ 3 :
        LaurentSeries K).leadingCoeff = 1 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one,
    HahnSeries.leadingCoeff_mul, sq, HahnSeries.leadingCoeff_mul,
    leadingCoeff_localExpand_addPullback_x_negFrobenius_eq W hq]
  ring

/-- **Sub-helper 85**: leadingCoeff of RHS = 1.

Strict-dominance of `X³` on RHS (orderTop -6 < -4 of other terms) gives
`leadingCoeff(RHS) = leadingCoeff(X³) = 1` via `leadingCoeff_add_eq_left`. -/
theorem leadingCoeff_localExpand_addPullback_RHS_eq
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 +
      HahnSeries.C W.a₂ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₄ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
      HahnSeries.C W.a₆ : LaurentSeries K).leadingCoeff = 1 := by
  rw [show ((localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 +
        HahnSeries.C W.a₂ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
        HahnSeries.C W.a₄ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
        HahnSeries.C W.a₆ : LaurentSeries K) =
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 +
        (HahnSeries.C W.a₂ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
        HahnSeries.C W.a₄ *
          (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
        HahnSeries.C W.a₆) from by ring]
  have h_lt :
      ((localExpand W (addPullback_x W (negFrobeniusIsog W)))^3 :
          LaurentSeries K).orderTop <
      (HahnSeries.C W.a₂ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W)))^2 +
       HahnSeries.C W.a₄ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) +
       HahnSeries.C W.a₆ : LaurentSeries K).orderTop := by
    refine lt_of_lt_of_le ?_ (orderTop_localExpand_RHS_lower_terms_ge W hq)
    rw [orderTop_localExpand_addPullback_x_negFrobenius_cube W hq]
    exact_mod_cast (by norm_num : (-6 : ℤ) < -4)
  rw [HahnSeries.leadingCoeff_add_eq_left h_lt]
  exact leadingCoeff_localExpand_addPullback_x_negFrobenius_cube_eq W hq

/-- **Sub-helper 86**: leadingCoeff of LHS = 1.

LHS = RHS (curve equation), so leadingCoeff equal. -/
theorem leadingCoeff_localExpand_addPullback_LHS_eq
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W))) +
      HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
        : LaurentSeries K).leadingCoeff = 1 := by
  rw [localExpand_addPullback_curve_equation W]
  exact leadingCoeff_localExpand_addPullback_RHS_eq W hq

/-- **Sub-helper 87**: leadingCoeff of `Y²` extracted from LHS via strict-dominance.

For the actual y-orderTop = -3, `Y²` (orderTop = -6) strictly dominates `a₁·X·Y`
(orderTop = -5) and `a₃·Y` (orderTop = -3). So `leadingCoeff(LHS) = leadingCoeff(Y²)`. -/
theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_sq_eq_one
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 :
        LaurentSeries K).leadingCoeff = 1 := by
  have h_y_ord_3 :
      (localExpand W (addPullback_y W (negFrobeniusIsog W))).orderTop =
        (((-3 : ℤ)) : WithTop ℤ) :=
    orderTop_localExpand_addPullback_y_negFrobenius_eq W hq
  have h_lt_a1xy := orderTop_y_sq_lt_a1xy_negFrobenius W hq (-3)
    (by norm_num) h_y_ord_3
  have h_lt_a3y := orderTop_y_sq_lt_a3y_negFrobenius W hq (-3)
    (by norm_num) h_y_ord_3
  have h_inner_lc : ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).leadingCoeff =
      ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 :
          LaurentSeries K).leadingCoeff :=
    HahnSeries.leadingCoeff_add_eq_left h_lt_a1xy
  have h_inner_ord := HahnSeries.orderTop_add_eq_left h_lt_a1xy
  have h_lt_outer : ((localExpand W (addPullback_y W (negFrobeniusIsog W)))^2 +
      HahnSeries.C W.a₁ *
        (localExpand W (addPullback_x W (negFrobeniusIsog W))) *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop <
      (HahnSeries.C W.a₃ *
        (localExpand W (addPullback_y W (negFrobeniusIsog W)))
          : LaurentSeries K).orderTop := h_inner_ord ▸ h_lt_a3y
  have h_outer_lc := HahnSeries.leadingCoeff_add_eq_left h_lt_outer
  -- LHS_lc = inner_lc (= Y²_lc) via h_outer_lc + h_inner_lc.
  have h_lhs_lc := leadingCoeff_localExpand_addPullback_LHS_eq W hq
  rw [h_outer_lc, h_inner_lc] at h_lhs_lc
  exact h_lhs_lc

/-- **MAIN Y-SIDE LEADING-COEFFICIENT**: `(leadingCoeff(localExpand addPullback_y))² = 1`
for q ≥ 2. From `leadingCoeff(Y²) = 1` (sub-helper 87) + `leadingCoeff_mul`. -/
theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_sq
    (hq : 2 ≤ Fintype.card K) :
    ((localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff)^2 = 1 := by
  have h := leadingCoeff_localExpand_addPullback_y_negFrobenius_sq_eq_one W hq
  rw [sq, HahnSeries.leadingCoeff_mul] at h
  rw [sq]
  exact h

/-- **Sub-helper 89**: `leadingCoeff(localExpand addPullback_y) ≠ 0` for q ≥ 2.
Direct from the squared identity = 1 (so leadingCoeff = ±1). -/
theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_ne_zero
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff ≠ 0 := by
  intro h
  have h_sq := leadingCoeff_localExpand_addPullback_y_negFrobenius_sq W hq
  rw [h, sq, mul_zero] at h_sq
  exact zero_ne_one h_sq

/-- **Sub-helper 89b**: `addPullbackAlgHom_negFrobenius (x_gen) = addPullback_x`. -/
theorem addPullbackAlgHom_negFrobenius_x_gen_eq
    (hq : 2 ≤ Fintype.card K) :
    addPullbackAlgHom_negFrobenius W hq (x_gen W) =
      addPullback_x W (negFrobeniusIsog W) := by
  unfold addPullbackAlgHom_negFrobenius addPullbackAlgHom_negFrobenius_of_inj addPullbackAlgHom
  rw [IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (algebraMap _ _ _) = _
  rw [IsFractionRing.lift_algebraMap]
  change (addCoordAlgHom (negFrobeniusIsog_addNonInverse W)).toRingHom
    (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X) =
    addPullback_x W (negFrobeniusIsog W)
  change addCoordRingHom (negFrobeniusIsog_addNonInverse W) _ = _
  unfold addCoordRingHom
  rw [show algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X =
      Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X) from rfl]
  rw [AdjoinRoot.lift_mk]
  simp [addBaseHom, Polynomial.eval₂_C]

/-- **Sub-helper 89c**: `addPullbackAlgHom_negFrobenius (y_gen) = addPullback_y`. -/
theorem addPullbackAlgHom_negFrobenius_y_gen_eq
    (hq : 2 ≤ Fintype.card K) :
    addPullbackAlgHom_negFrobenius W hq (y_gen W) =
      addPullback_y W (negFrobeniusIsog W) := by
  unfold addPullbackAlgHom_negFrobenius addPullbackAlgHom_negFrobenius_of_inj addPullbackAlgHom
  rw [IsFractionRing.liftAlgHom_apply]
  change IsFractionRing.lift _ (y_gen W) = _
  rw [show y_gen W = algebraMap _ _ (AdjoinRoot.root W.toAffine.polynomial)
        from rfl]
  rw [IsFractionRing.lift_algebraMap]
  change (addCoordAlgHom (negFrobeniusIsog_addNonInverse W)).toRingHom
    (AdjoinRoot.root W.toAffine.polynomial) = addPullback_y W (negFrobeniusIsog W)
  change addCoordRingHom (negFrobeniusIsog_addNonInverse W)
    (AdjoinRoot.root W.toAffine.polynomial) = _
  unfold addCoordRingHom
  rw [show AdjoinRoot.root W.toAffine.polynomial =
      AdjoinRoot.mk W.toAffine.polynomial Polynomial.X from AdjoinRoot.mk_X.symm]
  rw [AdjoinRoot.lift_mk]
  simp [addBaseHom, Polynomial.eval₂_X]

/-- **Sub-helper 90**:
`localExpand(γ.pullback localParam) = -localExpand(addPullback_x) / localExpand(addPullback_y)`
for γ = isogOneSub_negFrobenius. Direct ring-hom + AlgHom.commutes_div + map_div₀. -/
theorem localExpand_isogOneSub_negFrobenius_pullback_localParam
    (hq : 2 ≤ Fintype.card K) :
    localExpand W ((isogOneSub_negFrobenius W hq).pullback (localParam W)) =
      -(localExpand W (addPullback_x W (negFrobeniusIsog W))) /
        localExpand W (addPullback_y W (negFrobeniusIsog W)) := by
  rw [isogOneSub_negFrobenius_pullback]
  unfold localParam
  rw [map_div₀, map_neg, map_div₀, map_neg,
    addPullbackAlgHom_negFrobenius_x_gen_eq W hq,
    addPullbackAlgHom_negFrobenius_y_gen_eq W hq]

/-- **Sub-helper 91**: `(localExpand(γ.pullback localParam)).orderTop = 1` for
γ = isogOneSub_negFrobenius. Via `orderTop_div`: `-2 - (-3) = 1`. -/
theorem orderTop_localExpand_isogOneSub_negFrobenius_pullback_localParam
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W ((isogOneSub_negFrobenius W hq).pullback (localParam W))).orderTop =
      ((1 : ℤ) : WithTop ℤ) := by
  rw [localExpand_isogOneSub_negFrobenius_pullback_localParam W hq]
  rw [HahnSeries.orderTop_div
    (localExpand_addPullback_y_negFrobenius_ne_zero W hq)]
  rw [HahnSeries.orderTop_neg,
    orderTop_localExpand_addPullback_x_negFrobenius_eq W hq,
    orderTop_localExpand_addPullback_y_negFrobenius_eq W hq]
  rfl

/-- **Sub-helper 92**: `(localExpand(γ.pullback localParam)).leadingCoeff = -1 / leadingCoeff(Y)`
for γ = isogOneSub_negFrobenius. Via `leadingCoeff_div` + `leadingCoeff_neg`. -/
theorem leadingCoeff_localExpand_isogOneSub_negFrobenius_pullback_localParam
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W ((isogOneSub_negFrobenius W hq).pullback (localParam W))).leadingCoeff =
      -1 / (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff := by
  rw [localExpand_isogOneSub_negFrobenius_pullback_localParam W hq]
  rw [HahnSeries.leadingCoeff_div
    (localExpand_addPullback_y_negFrobenius_ne_zero W hq)]
  rw [HahnSeries.leadingCoeff_neg,
    leadingCoeff_localExpand_addPullback_x_negFrobenius_eq W hq]

/-- **Sub-helper 93**: `coeff 1 (formal γ) = -1 / leadingCoeff(Y)` for γ = isogOneSub_negFrobenius.

Via `formalIsogenySeries_coeff` + `coeff_untop_eq_leadingCoeff` at orderTop = 1.
This is the LaurentSeries-side computation of `coeff 1 (formal γ)` modulo
the sign of `leadingCoeff(Y) ∈ {1, -1}`. -/
theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_neg_one_div_leadingCoeff
    (hq : 2 ≤ Fintype.card K) :
    PowerSeries.coeff 1 (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      -1 / (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff := by
  rw [formalIsogenySeries_coeff]
  -- Goal: (localExpand (γ.pullback localParam)).coeff (1 : ℤ) = ...
  set Z := localExpand W ((isogOneSub_negFrobenius W hq).pullback (localParam W))
  have h_Z_ord : Z.orderTop = ((1 : ℤ) : WithTop ℤ) :=
    orderTop_localExpand_isogOneSub_negFrobenius_pullback_localParam W hq
  have h_Z_lc := leadingCoeff_localExpand_isogOneSub_negFrobenius_pullback_localParam W hq
  -- coeff (1 : ℤ) = leadingCoeff Z (since orderTop = 1)
  have h_Z_ne : Z ≠ 0 := by
    intro h
    rw [h, HahnSeries.orderTop_zero] at h_Z_ord
    exact WithTop.top_ne_coe h_Z_ord
  have h_ne_top : Z.orderTop ≠ ⊤ := by rw [h_Z_ord]; exact WithTop.coe_ne_top
  have h_untop : Z.orderTop.untop h_ne_top = (1 : ℤ) := by
    apply WithTop.coe_inj.mp
    rwa [WithTop.coe_untop]
  rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from rfl, ← h_untop,
    HahnSeries.coeff_untop_eq_leadingCoeff]
  exact h_Z_lc

/-- **Sub-helper 94** (witness-parametric coeff 1 = 1): with `leadingCoeff(Y) = -1`
witness, `coeff 1 (formalIsogenySeries γ) = 1` axiom-clean. -/
theorem coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_one_of_y_lc
    (hq : 2 ≤ Fintype.card K)
    (h_y_lc : (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff = -1) :
    PowerSeries.coeff 1 (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) = 1 := by
  rw [coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_neg_one_div_leadingCoeff
    W hq, h_y_lc]
  -- Goal: -1 / -1 = 1
  norm_num

/-- **Sub-helper 95** (Witness #1 closer via leadingCoeff(Y) witness + BRIDGE-001 γ):
takes `leadingCoeff(Y) = -1` as the LaurentSeries-side witness and BRIDGE-001
for γ as the K(E)-side witness, fires Witness #1 unconditional. -/
theorem isogOneSub_negFrobenius_isSeparable_via_y_lc_and_bridge_001
    (hq : 2 ≤ Fintype.card K)
    (h_y_lc : (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff = -1)
    (h_bridge_001_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)))) :
    (isogOneSub_negFrobenius W hq).IsSeparable := by
  have h_coeff_γ := coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_one_of_y_lc
    W hq h_y_lc
  have h_leading_add : PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) := by
    rw [h_coeff_γ, coeff_one_formalIsogenySeries_id W,
      coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero W hq, add_zero]
  exact isogOneSub_negFrobenius_isSeparable_of_bridge_and_leading W hq
    h_bridge_001_γ h_leading_add

/-- **Sub-helper 96** (omegaPullbackCoeff = 1 via leadingCoeff(Y) + BRIDGE-001 γ):
companion to 95 producing `omegaPullbackCoeff(γ) = 1`. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_y_lc_and_bridge_001
    (hq : 2 ≤ Fintype.card K)
    (h_y_lc : (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff = -1)
    (h_bridge_001_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)))) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 := by
  have h_coeff_γ := coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_one_of_y_lc
    W hq h_y_lc
  have h_leading_add : PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)) =
      PowerSeries.coeff 1 (formalIsogenySeries W (Isogeny.id W.toAffine)) +
        PowerSeries.coeff 1 (formalIsogenySeries W (negFrobeniusIsog W)) := by
    rw [h_coeff_γ, coeff_one_formalIsogenySeries_id W,
      coeff_one_formalIsogenySeries_negFrobeniusIsog_eq_zero W hq, add_zero]
  exact omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_of_bridge_and_leading W hq
    h_bridge_001_γ h_leading_add

/-- **Sub-helper 96b** (sign determination — char 2 case axiom-clean):
in characteristic 2, `(localExpand addPullback_y).leadingCoeff = -1`
because `c_y² = 1` (sub-helper 88) and `1 = -1` in char 2 (via `CharTwo.neg_eq`).

This pins the sign for characteristic 2 axiom-clean, closing the
sign-determination work for q = 2^k case. -/
theorem leadingCoeff_localExpand_addPullback_y_negFrobenius_eq_neg_one_char_two
    [CharP K 2]
    (hq : 2 ≤ Fintype.card K) :
    (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff = -1 := by
  have h_sq := leadingCoeff_localExpand_addPullback_y_negFrobenius_sq W hq
  set c := (localExpand W (addPullback_y W (negFrobeniusIsog W))).leadingCoeff
  -- In char 2: -1 = 1 in K (via CharTwo.neg_eq).
  have h_neg_one : (-1 : K) = 1 := CharTwo.neg_eq 1
  -- c² = 1 in char 2 ⇒ (c + 1)² = 0 (since 2c = 0 and 1 + 1 = 0).
  have h_two : (2 : K) = 0 := by
    have h := CharP.cast_eq_zero K 2
    exact_mod_cast h
  have h11 : (1 : K) + 1 = 0 := by
    have h_eq : (1 : K) + 1 = (2 : K) := by norm_num
    rwa [h_eq]
  have h2_c : (2 : K) * c = 0 := by
    rw [h_two, zero_mul]
  have h_c_plus_one_sq : (c + 1)^2 = 0 := by
    have step : (c + 1)^2 = c^2 + (2 : K) * c + 1 := by ring
    rw [step, h_sq, h2_c]
    -- Goal: 1 + 0 + 1 = 0
    rw [add_zero]
    exact h11
  have h_c_plus_one : c + 1 = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num : 2 ≠ 0) |>.mp h_c_plus_one_sq
  exact eq_neg_of_add_eq_zero_left h_c_plus_one

/-- **Sub-helper 98** (Witness #1 char 2): in characteristic 2, the y-side
sign pin is automatic via 96b. Witness #1 fires with only BRIDGE-001 for γ. -/
theorem isogOneSub_negFrobenius_isSeparable_char_two
    [CharP K 2]
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_001_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)))) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  isogOneSub_negFrobenius_isSeparable_via_y_lc_and_bridge_001 W hq
    (leadingCoeff_localExpand_addPullback_y_negFrobenius_eq_neg_one_char_two W hq)
    h_bridge_001_γ

/-- **Sub-helper 99** (omegaPullbackCoeff(γ) = 1 char 2). -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_char_two
    [CharP K 2]
    (hq : 2 ≤ Fintype.card K)
    (h_bridge_001_γ : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq)))) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 :=
  omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_y_lc_and_bridge_001 W hq
    (leadingCoeff_localExpand_addPullback_y_negFrobenius_eq_neg_one_char_two W hq)
    h_bridge_001_γ

/-- **Sub-helper 101** (BRIDGE-001 for γ char-2 from omega witness): takes
`omegaPullbackCoeff(γ) = 1` directly and discharges BRIDGE-001 for γ
axiom-clean. The LaurentSeries side gives `coeff 1 (formal γ) = 1` via
y-lc (sub-helper 96b) + ratio chain. -/
theorem bridge_001_γ_isogOneSub_negFrobenius_char_two
    [CharP K 2]
    (hq : 2 ≤ Fintype.card K)
    (h_omega : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) =
      algebraMap K W.toAffine.FunctionField (PowerSeries.coeff 1
        (formalIsogenySeries W (isogOneSub_negFrobenius W hq))) := by
  rw [h_omega]
  rw [coeff_one_formalIsogenySeries_isogOneSub_negFrobenius_eq_one_of_y_lc W hq
    (leadingCoeff_localExpand_addPullback_y_negFrobenius_eq_neg_one_char_two W hq)]
  exact (map_one _).symm

/-- **Sub-helper 104** (Frobenius D vanishing): for finite K with characteristic
p (and `q = #K` a power of p), the Kähler differential of `x_gen^q` vanishes.

Proof: `D(x^q) = q · x^(q-1) · D(x)` (Leibniz pow), and `(q : K) = 0` since
`p ∣ q`. -/
theorem kaehler_D_x_gen_pow_card_eq_zero
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W ^ Fintype.card K) = 0 := by
  rw [Derivation.leibniz_pow]
  have h_card_zero : (Fintype.card K : K) = 0 := Nat.cast_card_eq_zero K
  change (Fintype.card K : ℕ) • (x_gen W ^ (Fintype.card K - 1) •
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W)) = 0
  rw [show (Fintype.card K : ℕ) • (x_gen W ^ (Fintype.card K - 1) •
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W)) =
    ((Fintype.card K : K) • x_gen W ^ (Fintype.card K - 1)) •
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) from by
    rw [Nat.cast_smul_eq_nsmul, smul_assoc]]
  rw [h_card_zero, zero_smul, zero_smul]

/-- **Sub-helper 105** (Frobenius D pullback vanishing): the Kähler differential
of `(frobeniusIsog).pullback x_gen` vanishes. Direct from sub-helper 104 +
`frobeniusIsog_pullback_apply` (= `x_gen^q`). -/
theorem kaehler_D_frobeniusIsog_pullback_x_gen
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    KaehlerDifferential.D K W.toAffine.FunctionField
        ((frobeniusIsog W).pullback (x_gen W)) = 0 := by
  rw [frobeniusIsog_pullback_apply]
  exact kaehler_D_x_gen_pow_card_eq_zero W p

/-- **Sub-helper 106** (Frobenius D pullback y vanishing): the Kähler differential
of `(frobeniusIsog).pullback y_gen` vanishes. Same proof shape as 105. -/
theorem kaehler_D_frobeniusIsog_pullback_y_gen
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    KaehlerDifferential.D K W.toAffine.FunctionField
        ((frobeniusIsog W).pullback (y_gen W)) = 0 := by
  rw [frobeniusIsog_pullback_apply, Derivation.leibniz_pow]
  have h_card_zero : (Fintype.card K : K) = 0 := Nat.cast_card_eq_zero K
  change (Fintype.card K : ℕ) • (y_gen W ^ (Fintype.card K - 1) •
      KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W)) = 0
  rw [show (Fintype.card K : ℕ) • (y_gen W ^ (Fintype.card K - 1) •
      KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W)) =
    ((Fintype.card K : K) • y_gen W ^ (Fintype.card K - 1)) •
      KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) from by
    rw [Nat.cast_smul_eq_nsmul, smul_assoc]]
  rw [h_card_zero, zero_smul, zero_smul]

/-- **Sub-helper 107** (negFrobenius D pullback x vanishing): the Kähler differential
of `(negFrobeniusIsog).pullback x_gen` vanishes.

`negFrobeniusIsog = mulByInt(-1) ∘ frobeniusIsog`, so
`(negFrob).pullback x_gen = frobenius.pullback ((mulByInt(-1)).pullback x_gen) =
frobenius.pullback x_gen = x_gen^q` (since `[-1]` fixes `x_gen`).
Then by sub-helper 104, `D(x_gen^q) = 0`. -/
theorem kaehler_D_negFrobeniusIsog_pullback_x_gen
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    KaehlerDifferential.D K W.toAffine.FunctionField
        ((negFrobeniusIsog W).pullback (x_gen W)) = 0 := by
  rw [negFrobeniusIsog_pullback_x_gen]
  exact kaehler_D_frobeniusIsog_pullback_x_gen W p

/-- **Sub-helper 108** (negFrobenius D pullback y vanishing): the Kähler differential
of `(negFrobeniusIsog).pullback y_gen` vanishes.

`(negFrob).pullback y_gen = -π·y_gen - a₁·π·x_gen - a₃` (where π·· =
frobeniusIsog.pullback). The differential operator `D` is a K-derivation,
so `D(constant) = 0` for `a₃ ∈ K`, and `D(a₁ · f) = a₁ · D(f)` for `a₁ ∈ K`,
and `D(-f) = -D(f)`. Combined with sub-helpers 105-106, all three terms
vanish. -/
theorem kaehler_D_negFrobeniusIsog_pullback_y_gen
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    KaehlerDifferential.D K W.toAffine.FunctionField
        ((negFrobeniusIsog W).pullback (y_gen W)) = 0 := by
  rw [negFrobeniusIsog_pullback_y_gen]
  -- D is a K-derivation: D(-x - a₁ * y - a₃) = -D(x) - (a₁•D(y)) - 0 since a₁,a₃ ∈ K.
  rw [map_sub, map_sub, map_neg, kaehler_D_frobeniusIsog_pullback_y_gen W p]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).leibniz
      (algebraMap K KE W.a₁) ((frobeniusIsog W).pullback (x_gen W))]
  rw [kaehler_D_frobeniusIsog_pullback_x_gen W p,
      (KaehlerDifferential.D K W.toAffine.FunctionField).map_algebraMap W.a₁,
      (KaehlerDifferential.D K W.toAffine.FunctionField).map_algebraMap W.a₃]
  simp

/-- **Sub-helper 109** (D(addPullback_x) formula via slope).

For any α : Isogeny W W with `D((α).pullback x_gen) = 0` (i.e., α has its
x-pullback Kähler-flat, true for Frobenius / negFrobenius in characteristic
p), the Kähler differential of `addPullback_x` reduces to a slope-only term
minus the Kähler differential of x_gen:
  `D(addPullback_x) = (2·ℓ + a₁) • D(ℓ) - D(x_gen)`
where `ℓ = addSlope W α`. The W_KE coefficients (a₁, a₂) are images under
`algebraMap K KE`, so D vanishes on them as K-elements. -/
theorem kaehler_D_addPullback_x_via_slope_witness
    (α : Isogeny W.toAffine W.toAffine)
    (h_α_x : KaehlerDifferential.D K W.toAffine.FunctionField
        (α.pullback (x_gen W)) = 0) :
    KaehlerDifferential.D K W.toAffine.FunctionField (addPullback_x W α) =
      (2 * addSlope W α + algebraMap K KE W.a₁) •
        KaehlerDifferential.D K W.toAffine.FunctionField (addSlope W α) -
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
  unfold addPullback_x W_KE
  set D := KaehlerDifferential.D K W.toAffine.FunctionField
  set ℓ := addSlope W α
  change D ((ℓ) ^ 2 + (algebraMap K KE) W.a₁ * ℓ
          - (algebraMap K KE) W.a₂ - x_gen W - α.pullback (x_gen W)) = _
  rw [map_sub, map_sub, map_sub, map_add, D.leibniz ((algebraMap K KE) W.a₁) ℓ,
    D.leibniz_pow ℓ 2, D.map_algebraMap W.a₁, D.map_algebraMap W.a₂, h_α_x]
  simp only [smul_zero, add_zero, sub_zero]
  change (2 : ℕ) • ℓ ^ (2 - 1) • D ℓ + (algebraMap K KE) W.a₁ • D ℓ - D (x_gen W) =
      (2 * ℓ + (algebraMap K KE) W.a₁) • D ℓ - D (x_gen W)
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, add_smul]
  congr 1; congr 1
  rw [show (2 : ℕ) • (ℓ • D ℓ) = ((2 : KE)) • (ℓ • D ℓ) from
        (Nat.cast_smul_eq_nsmul (R := KE) 2 _).symm]
  rw [smul_smul]

/-- **Sub-helper 110** (D(addPullback_x) for negFrobenius — specialized).

Direct from sub-helper 109 + sub-helper 107: for the addition-pullback
under negFrobenius, `D(addPullback_x) = (2·ℓ + a₁) • D(ℓ) - D(x_gen)`
where ℓ = addSlope W (negFrobeniusIsog W).

This is the key formula — D(addPullback_x) is determined entirely by
the slope's Kähler differential (and D(x_gen)), with no contribution
from D applied to the negFrob-pullback (which vanishes in characteristic p). -/
theorem kaehler_D_addPullback_x_negFrobenius
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    KaehlerDifferential.D K W.toAffine.FunctionField
        (addPullback_x W (negFrobeniusIsog W)) =
      (2 * addSlope W (negFrobeniusIsog W) + algebraMap K KE W.a₁) •
        KaehlerDifferential.D K W.toAffine.FunctionField
          (addSlope W (negFrobeniusIsog W)) -
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) :=
  kaehler_D_addPullback_x_via_slope_witness W (negFrobeniusIsog W)
    (kaehler_D_negFrobeniusIsog_pullback_x_gen W p)

/-- **Route B core (III.5.2), general slope-differential formula** (no `D(α*x)=0`
hypothesis): for any `α`, the Kähler differential of the `id + α` addition-pullback
x-coordinate is the slope term minus `D(x_gen)` minus `D(α*x)`. Generalizes
`kaehler_D_addPullback_x_via_slope_witness` (which drops the last term under the
char-`p` Frobenius flatness). This is the differential side of Silverman III.5.2:
`D(addPullback_x) = (2ℓ+a₁)·D(ℓ) − D(x) − D(α*x)`. -/
theorem kaehler_D_addPullback_x_general
    (α : Isogeny W.toAffine W.toAffine) :
    KaehlerDifferential.D K W.toAffine.FunctionField (addPullback_x W α) =
      (2 * addSlope W α + algebraMap K KE W.a₁) •
        KaehlerDifferential.D K W.toAffine.FunctionField (addSlope W α) -
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) -
      KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (x_gen W)) := by
  unfold addPullback_x W_KE
  set D := KaehlerDifferential.D K W.toAffine.FunctionField
  set ℓ := addSlope W α
  change D ((ℓ) ^ 2 + (algebraMap K KE) W.a₁ * ℓ
          - (algebraMap K KE) W.a₂ - x_gen W - α.pullback (x_gen W)) = _
  rw [map_sub, map_sub, map_sub, map_add, D.leibniz ((algebraMap K KE) W.a₁) ℓ,
    D.leibniz_pow ℓ 2, D.map_algebraMap W.a₁, D.map_algebraMap W.a₂]
  simp only [smul_zero, add_zero, sub_zero]
  change (2 : ℕ) • ℓ ^ (2 - 1) • D ℓ + (algebraMap K KE) W.a₁ • D ℓ
      - D (x_gen W) - D (α.pullback (x_gen W)) =
      (2 * ℓ + (algebraMap K KE) W.a₁) • D ℓ - D (x_gen W) - D (α.pullback (x_gen W))
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, add_smul]
  congr 2
  rw [show (2 : ℕ) • (ℓ • D ℓ) = ((2 : KE)) • (ℓ • D ℓ) from
        (Nat.cast_smul_eq_nsmul (R := KE) 2 _).symm, smul_smul]

/-- **Sub-helper 111** (ω(γ) = 1 via Kähler witness).

Closing-arc witness consumer: given that
  `(α*(u))⁻¹ • D(addPullback_x) = invariantDifferential`
(equivalently, `α*(u) • ω = D(addPullback_x)` for ω = invariantDifferential),
conclude `omegaPullbackCoeff(γ) = 1`. Direct from
`omegaPullbackCoeff_spec` + `omegaPullbackCoeff_unique`.

The hypothesis is the SUBSTANTIVE Kähler identity in K(E) that III.5.2 / IV.1.4
carries out: relating the slope's differential to the addition-pullback's
differential. Once this identity is closed (via, e.g., the curve equation
matching at orderTop -6 and the slope-of-formal-identity lemma), `ω(γ) = 1`
follows axiom-clean and the Hasse-Weil bound discharges via sub-helper 103. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_kaehler_witness
    (hq : 2 ≤ Fintype.card K)
    (h_kaehler :
      (alpha_star_u W (isogOneSub_negFrobenius W hq))⁻¹ •
        KaehlerDifferential.D K W.toAffine.FunctionField
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      invariantDifferential W.toAffine) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 := by
  apply omegaPullbackCoeff_unique
  rw [omegaPullbackCoeff_spec, one_smul]
  unfold x_gen at h_kaehler
  exact h_kaehler

/-- **Sub-helper 113** (Kähler ω(γ) = 1 via pullbackKaehler witness — closing-arc).

The cleaner reformulation of sub-helper 111 using `pullbackKaehler` directly:
given `γ.pullbackKaehler ω = ω`, conclude `omegaPullbackCoeff(γ) = 1`.

Direct from `pullbackKaehler_invariantDifferential` + `omegaPullbackCoeff_unique`. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_pullbackKaehler_witness
    (hq : 2 ≤ Fintype.card K)
    (h_pK : (isogOneSub_negFrobenius W hq).pullbackKaehler
        (invariantDifferential W.toAffine) = invariantDifferential W.toAffine) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 := by
  apply omegaPullbackCoeff_unique
  rw [one_smul, ← Isogeny.pullbackKaehler_invariantDifferential]
  exact h_pK

/-- **Sub-helper 114** (id.pullbackKaehler ω = ω, axiom-clean).

The identity isogeny acts trivially on the invariant differential. Direct
from `pullbackKaehler_invariantDifferential (Isogeny.id W.toAffine)` +
`omegaPullbackCoeff_id = 1`. -/
theorem pullbackKaehler_invariantDifferential_id :
    (Isogeny.id W.toAffine).pullbackKaehler (invariantDifferential W.toAffine) =
      invariantDifferential W.toAffine := by
  rw [Isogeny.pullbackKaehler_invariantDifferential, omegaPullbackCoeff_id, one_smul]

/-- **Sub-helper 115** ((-π).pullbackKaehler ω = 0, axiom-clean).

The negation-of-Frobenius isogeny annihilates the invariant differential
(at the cotangent level). Direct from `pullbackKaehler_invariantDifferential
(negFrobeniusIsog W)` + `omegaPullbackCoeff_negFrobeniusIsog = 0`
(Differential.lean line 430, axiom-clean). -/
theorem pullbackKaehler_invariantDifferential_negFrobeniusIsog :
    (negFrobeniusIsog W).pullbackKaehler (invariantDifferential W.toAffine) = 0 := by
  rw [Isogeny.pullbackKaehler_invariantDifferential,
      omegaPullbackCoeff_negFrobeniusIsog, zero_smul]

/-- **Sub-helper 116** (γ.pullbackKaehler ω = ω via III.5.2 additivity witness — axiom-clean).

Given the III.5.2 additivity at the differential level for our specific
decomposition `γ = id + (-π)`:
  `γ.pullbackKaehler ω = id.pullbackKaehler ω + (-π).pullbackKaehler ω`,
combine with sub-helpers 114-115 (axiom-clean: `id.pullbackKaehler ω = ω` and
`(-π).pullbackKaehler ω = 0`) to conclude `γ.pullbackKaehler ω = ω + 0 = ω`.

This is the closing-arc commit: the only remaining substantive input is the
III.5.2 differential additivity for our specific case, which is the III.5.2
content for elliptic curve isogenies. -/
theorem pullbackKaehler_invariantDifferential_isogOneSub_negFrobenius_via_additivity_witness
    (hq : 2 ≤ Fintype.card K)
    (h_add : (isogOneSub_negFrobenius W hq).pullbackKaehler
        (invariantDifferential W.toAffine) =
      (Isogeny.id W.toAffine).pullbackKaehler (invariantDifferential W.toAffine) +
      (negFrobeniusIsog W).pullbackKaehler (invariantDifferential W.toAffine)) :
    (isogOneSub_negFrobenius W hq).pullbackKaehler
        (invariantDifferential W.toAffine) = invariantDifferential W.toAffine := by
  rw [h_add, pullbackKaehler_invariantDifferential_id W,
      pullbackKaehler_invariantDifferential_negFrobeniusIsog W, add_zero]

/-- **Sub-helper 117** (ω(γ) = 1 via III.5.2 additivity witness — closing-arc).

Composes sub-helper 113 (Kähler witness → ω(γ) = 1) with sub-helper 116
(III.5.2 additivity → γ.pullbackKaehler ω = ω). The single substantive
input is the III.5.2 differential additivity for our specific decomposition. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_additivity_witness
    (hq : 2 ≤ Fintype.card K)
    (h_add : (isogOneSub_negFrobenius W hq).pullbackKaehler
        (invariantDifferential W.toAffine) =
      (Isogeny.id W.toAffine).pullbackKaehler (invariantDifferential W.toAffine) +
      (negFrobeniusIsog W).pullbackKaehler (invariantDifferential W.toAffine)) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 :=
  omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_pullbackKaehler_witness W hq
    (pullbackKaehler_invariantDifferential_isogOneSub_negFrobenius_via_additivity_witness
      W hq h_add)

/-- **Sub-helper 119** (Kähler witness via slope-derivative witness — closing-arc).

Given `D(addSlope W (negFrobeniusIsog W)) = c • D(x_gen)` for some `c : K(E)`
(derived from differentiating the slope formula `(y_gen - π·y) / (x_gen - π·x)`
with the Frobenius differential vanishing — sub-helpers 107, 108) and the
algebraic identity in K(E):
  `(2ℓ + a₁) · c - 1 = (alpha_star_u γ) · u_gen⁻¹`
(equivalently, after clearing denominators: the K(E) identity that the III.5.2
content carries out), conclude the Kähler witness needed by sub-helper 111.

This factors the III.5.2 differential additivity through an explicit K(E)
identity. The slope-derivative witness is the Kähler-differential form of
the curve-tangent calculation; the K(E) identity is the substantive arithmetic
content of III.5.2 for our `id + (-π)` decomposition. -/
theorem kaehler_witness_via_slope_deriv_witness
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 2 ≤ Fintype.card K)
    (c : KE)
    (h_slope_deriv :
      KaehlerDifferential.D K W.toAffine.FunctionField
          (addSlope W (negFrobeniusIsog W)) =
        c • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W))
    (h_KE_identity :
      ((2 * addSlope W (negFrobeniusIsog W) +
            algebraMap K KE W.a₁) * c - 1) * (u_gen W) =
        alpha_star_u W (isogOneSub_negFrobenius W hq)) :
    (alpha_star_u W (isogOneSub_negFrobenius W hq))⁻¹ •
        KaehlerDifferential.D K W.toAffine.FunctionField
          ((isogOneSub_negFrobenius W hq).pullback (x_gen W)) =
      invariantDifferential W.toAffine := by
  -- (γ).pullback x_gen = addPullback_x W (negFrobeniusIsog W)
  rw [show (isogOneSub_negFrobenius W hq).pullback (x_gen W) =
      addPullback_x W (negFrobeniusIsog W) from
      addPullbackAlgHom_negFrobenius_x_gen_eq W hq]
  rw [kaehler_D_addPullback_x_negFrobenius W p, h_slope_deriv, smul_smul]
  rw [show ((2 * addSlope W (negFrobeniusIsog W) +
            algebraMap K KE W.a₁) * c) •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) -
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) =
    (((2 * addSlope W (negFrobeniusIsog W) +
            algebraMap K KE W.a₁) * c) - 1) •
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) from by
    rw [sub_smul, one_smul]]
  rw [smul_smul]
  rw [show invariantDifferential W.toAffine =
      (u_gen W)⁻¹ • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) from
        rfl]
  congr 1
  have h_alphau_ne : alpha_star_u W (isogOneSub_negFrobenius W hq) ≠ 0 := by
    rw [alpha_star_u_eq]
    -- α.pullback is an algebra hom KE →ₐ KE; KE is a field, so the pullback is injective.
    intro h
    have h_inj : Function.Injective (isogOneSub_negFrobenius W hq).pullback :=
      (isogOneSub_negFrobenius W hq).pullback.toRingHom.injective
    have h_eq : (isogOneSub_negFrobenius W hq).pullback (u_gen W) =
        (isogOneSub_negFrobenius W hq).pullback 0 := by
      rwa [map_zero]
    exact u_gen_ne_zero W (h_inj h_eq)
  field_simp [h_alphau_ne, u_gen_ne_zero W]
  linear_combination h_KE_identity

/-- **Sub-helper 120** (Weierstrass equation in K(E), axiom-clean):
`y_gen² + a₁·x_gen·y_gen + a₃·y_gen = x_gen³ + a₂·x_gen² + a₄·x_gen + a₆`
in K(E). Direct from the affine equation `Affine.Equation` for the generic
point on `W_KE`, with W_KE coefficients lifted to algebraMap form.

This is the foundational K(E) identity that the curve-equation Kähler
differential identity (sub-helper 121) builds upon. No derivation involved
yet — purely the equation in K(E). -/
theorem weierstrass_equation_in_KE :
    y_gen W ^ 2 + algebraMap K KE W.a₁ * x_gen W * y_gen W +
        algebraMap K KE W.a₃ * y_gen W =
      x_gen W ^ 3 + algebraMap K KE W.a₂ * x_gen W ^ 2 +
        algebraMap K KE W.a₄ * x_gen W +
        algebraMap K KE W.a₆ := by
  have h_gen := generic_equation W
  rw [(W_KE W).toAffine.equation_iff] at h_gen
  exact h_gen

/-- **Sub-helper 121** (Kähler form of curve equation, axiom-clean foundation):
literal D-application of the Weierstrass equation in K(E):
`D(y² + a₁xy + a₃y) = D(x³ + a₂x² + a₄x + a₆)` in `Ω[K(E)/K]`.

Direct from `congrArg D` applied to `weierstrass_equation_in_KE` (sub-helper
120). The substantive Kähler identity `(a₃ + 2y + a₁x)·Dy = (3x² + 2a₂x +
a₄ - a₁y)·Dx` follows by Leibniz expansion; the explicit ℕ-smul ↔ KE-smul
conversion in that expansion is technical and deferred. -/
theorem kaehler_D_weierstrass_equation_K_E :
    KaehlerDifferential.D K W.toAffine.FunctionField
        (y_gen W ^ 2 +
          algebraMap K KE W.a₁ * x_gen W * y_gen W +
          algebraMap K KE W.a₃ * y_gen W) =
      KaehlerDifferential.D K W.toAffine.FunctionField
        (x_gen W ^ 3 +
          algebraMap K KE W.a₂ * x_gen W ^ 2 +
          algebraMap K KE W.a₄ * x_gen W +
          algebraMap K KE W.a₆) :=
  congrArg (KaehlerDifferential.D K W.toAffine.FunctionField)
    (weierstrass_equation_in_KE W)

/-- **Sub-helper 122** (D(y²) via pow_two — axiom-clean KE-smul-only):
`D(y_gen²) = y_gen • D(y_gen) + y_gen • D(y_gen)`. Wall-break: avoids
`Derivation.leibniz_pow`'s ℕ-smul. -/
theorem kaehler_D_y_gen_sq :
    KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W ^ 2) =
      y_gen W • KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) +
      y_gen W • KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) := by
  rw [pow_two,
    (KaehlerDifferential.D K W.toAffine.FunctionField).leibniz (y_gen W) (y_gen W)]

/-- **Sub-helper 123** (D(x²) via pow_two — axiom-clean):
`D(x_gen²) = x_gen • D(x_gen) + x_gen • D(x_gen)`. -/
theorem kaehler_D_x_gen_sq :
    KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W ^ 2) =
      x_gen W • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) +
      x_gen W • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
  rw [pow_two,
    (KaehlerDifferential.D K W.toAffine.FunctionField).leibniz (x_gen W) (x_gen W)]

/-- **Sub-helper 124** (D(x³) via pow expansion + leibniz — axiom-clean):
`D(x_gen³) = x_gen² • D(x_gen) + x_gen • D(x_gen²)`. -/
theorem kaehler_D_x_gen_cube :
    KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W ^ 3) =
      x_gen W ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) +
      x_gen W •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W ^ 2) := by
  rw [show (x_gen W) ^ 3 = (x_gen W) ^ 2 * x_gen W from by ring,
    (KaehlerDifferential.D K W.toAffine.FunctionField).leibniz (x_gen W ^ 2) (x_gen W)]

/-- **Sub-helper 125** (D-distribution of Weierstrass equation LHS, axiom-clean):
fully Leibniz-expanded LHS in KE-smul-only form. Uses sub-helper 122 (D(y²)
bypass) + Derivation.leibniz + D.map_algebraMap. -/
theorem kaehler_D_weierstrass_LHS_expanded :
    KaehlerDifferential.D K W.toAffine.FunctionField
        (y_gen W ^ 2 +
          algebraMap K KE W.a₁ * x_gen W * y_gen W +
          algebraMap K KE W.a₃ * y_gen W) =
      (y_gen W •
          KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) +
        y_gen W •
          KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W)) +
      ((algebraMap K KE W.a₁ * x_gen W) •
          KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) +
        y_gen W •
          (algebraMap K KE W.a₁ •
            KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W))) +
      algebraMap K KE W.a₃ •
        KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) := by
  rw [map_add, map_add, kaehler_D_y_gen_sq W]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).leibniz
      (algebraMap K KE W.a₁ * x_gen W) (y_gen W)]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).leibniz
      (algebraMap K KE W.a₁) (x_gen W)]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).leibniz
      (algebraMap K KE W.a₃) (y_gen W)]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).map_algebraMap W.a₁,
      (KaehlerDifferential.D K W.toAffine.FunctionField).map_algebraMap W.a₃]
  simp only [smul_zero, add_zero]

/-- **Sub-helper 126** (D-distribution of Weierstrass equation RHS, axiom-clean):
fully Leibniz-expanded RHS. Uses sub-helpers 123, 124. -/
theorem kaehler_D_weierstrass_RHS_expanded :
    KaehlerDifferential.D K W.toAffine.FunctionField
        (x_gen W ^ 3 +
          algebraMap K KE W.a₂ * x_gen W ^ 2 +
          algebraMap K KE W.a₄ * x_gen W +
          algebraMap K KE W.a₆) =
      ((x_gen W ^ 2 •
            KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) +
          x_gen W •
            (x_gen W •
              KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) +
              x_gen W •
                KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W))) +
        algebraMap K KE W.a₂ •
          (x_gen W •
            KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) +
            x_gen W •
              KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W))) +
      algebraMap K KE W.a₄ •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
  rw [map_add, map_add, map_add, kaehler_D_x_gen_cube W, kaehler_D_x_gen_sq W]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).leibniz
      (algebraMap K KE W.a₂) (x_gen W ^ 2)]
  rw [kaehler_D_x_gen_sq W]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).leibniz
      (algebraMap K KE W.a₄) (x_gen W)]
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).map_algebraMap W.a₂,
      (KaehlerDifferential.D K W.toAffine.FunctionField).map_algebraMap W.a₄,
      (KaehlerDifferential.D K W.toAffine.FunctionField).map_algebraMap W.a₆]
  simp only [smul_zero, add_zero]

/-- **Sub-helper 127** (curve-equation Kähler identity, axiom-clean):

`(a₃ + 2y + a₁x) • D(y) = (3x² + 2a₂x + a₄ - a₁y) • D(x)` in `Ω[K(E)/K]`.

Combines sub-helper 121 (D(LHS) = D(RHS) via congrArg) + 125 (LHS expansion)
+ 126 (RHS expansion) + `linear_combination`. All KE-smul throughout —
ℕ-smul wall bypassed via sub-helpers 122-124.

This is the SUBSTANTIVE K(E) Kähler identity. NO witnesses. Foundational
for sub-helper 128 (D(slope)) and the III.5.2 invariant-differential
additivity. -/
theorem kaehler_curve_equation_K_E :
    (algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
        algebraMap K KE W.a₁ * x_gen W) •
        KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) =
      ((3 : KE) * x_gen W ^ 2 +
        (2 : KE) * algebraMap K KE W.a₂ * x_gen W +
        algebraMap K KE W.a₄ -
        algebraMap K KE W.a₁ * y_gen W) •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
  -- Sixth wall-break attempt: pre-rewrite goal `(2 : KE) * y_gen` to
  -- `y_gen + y_gen` using ring identities BEFORE expansion, eliminating the
  -- (2 : KE) literal at the source. Then both sides use only +-additive
  -- composition + KE-smul, no `(2 : ℕ)` casts anywhere.
  set Dx := KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) with hDx
  set Dy := KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) with hDy
  -- Substitute literals with explicit sums in K(E).
  have h2y : (2 : KE) * y_gen W = y_gen W + y_gen W := by ring
  have h3x2 : (3 : KE) * x_gen W ^ 2 = x_gen W ^ 2 + x_gen W ^ 2 + x_gen W ^ 2 := by ring
  have h2a2x : (2 : KE) * algebraMap K KE W.a₂ * x_gen W =
    algebraMap K KE W.a₂ * x_gen W +
      algebraMap K KE W.a₂ * x_gen W := by ring
  rw [h2y, h3x2, h2a2x]
  -- Distribute • on both sides into individual c • Dx / c • Dy terms.
  simp only [add_smul, sub_smul]
  have h_eq := kaehler_D_weierstrass_equation_K_E W
  rw [kaehler_D_weierstrass_LHS_expanded W,
      kaehler_D_weierstrass_RHS_expanded W] at h_eq
  -- Flatten nested smul (x • x • Dx → (x*x) • Dx) and distribute over +.
  simp only [smul_add, ← mul_smul] at h_eq ⊢
  -- Convert (x * x) → x^2 via pow_two for matching with goal's x^2 form.
  rw [show x_gen W * x_gen W = x_gen W ^ 2 from (sq (x_gen W)).symm] at h_eq
  -- Reduce y * a₁ in h_eq to a₁ * y to match goal.
  rw [show y_gen W * algebraMap K KE W.a₁ =
        algebraMap K KE W.a₁ * y_gen W from by ring] at h_eq
  -- Now both sides are sums of (KE-coefficient) • (Dx or Dy). Match via abel.
  linear_combination (norm := abel) h_eq

/-- **Sub-helper 128** (D(addSlope) for negFrobenius — substantive K(E) identity, axiom-clean):

The Kähler derivative of `addSlope W (negFrobeniusIsog W) =
(y_gen - π·y) / (x_gen - π·x)` satisfies the closed-form identity:

```
(x_gen - π·x)² • D(addSlope) = (x_gen - π·x) • D(y_gen) - (y_gen - π·y) • D(x_gen)
```

where π·x = (negFrob).pullback x_gen, π·y = (negFrob).pullback y_gen.

Proof: apply `Derivation.leibniz_div` to `addSlope_negFrobeniusIsog_eq`,
simplify via `D(π·x) = 0` (sub-helper 107), `D(π·y) = 0` (sub-helper 108),
cancel Den² · Den⁻² = 1.

This is the SUBSTANTIVE K(E) Kähler identity for the addition slope —
NO witnesses, NO hypotheses beyond Mathlib's quotient rule and the
existing Frobenius-differential vanishing (axiom-clean). -/
theorem kaehler_D_addSlope_negFrobenius
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField
          (addSlope W (negFrobeniusIsog W)) =
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) •
        KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) -
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
  set N := y_gen W - (negFrobeniusIsog W).pullback (y_gen W)
  set Den := x_gen W - (negFrobeniusIsog W).pullback (x_gen W)
  have hDen_ne : Den ≠ 0 := x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  rw [addSlope_negFrobeniusIsog_eq W]
  change Den ^ 2 • KaehlerDifferential.D K W.toAffine.FunctionField (N / Den) =
      Den • KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) -
      N • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W)
  rw [(KaehlerDifferential.D K W.toAffine.FunctionField).leibniz_div N Den]
  have h_DN : KaehlerDifferential.D K W.toAffine.FunctionField N =
      KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) := by
    change KaehlerDifferential.D K W.toAffine.FunctionField
        (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) = _
    rw [map_sub, kaehler_D_negFrobeniusIsog_pullback_y_gen W p, sub_zero]
  have h_DDen : KaehlerDifferential.D K W.toAffine.FunctionField Den =
      KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
    change KaehlerDifferential.D K W.toAffine.FunctionField
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) = _
    rw [map_sub, kaehler_D_negFrobeniusIsog_pullback_x_gen W p, sub_zero]
  rw [h_DN, h_DDen, smul_smul]
  rw [show Den ^ 2 * Den⁻¹ ^ 2 = 1 from by
    rw [← mul_pow, mul_inv_cancel₀ hDen_ne, one_pow]]
  rw [one_smul]

/-- **Route B core (III.5.2), general slope differential** (no Frobenius flatness): for any `α`
with `x_gen ≠ α*x_gen` (non-doubling), the Kähler derivative of `addSlope = (y−α*y)/(x−α*x)`
satisfies `Den²·D(addSlope) = Den·(D(y)−D(α*y)) − N·(D(x)−D(α*x))` where `N = y−α*y`,
`Den = x−α*x`. Generalizes `kaehler_D_addSlope_negFrobenius` (which used `D(π*x)=D(π*y)=0`). -/
theorem kaehler_D_addSlope_general
    (α : Isogeny W.toAffine W.toAffine)
    (h_ne : x_gen W ≠ α.pullback (x_gen W)) :
    (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField (addSlope W α) =
      (x_gen W - α.pullback (x_gen W)) •
        (KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) -
         KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (y_gen W))) -
      (y_gen W - α.pullback (y_gen W)) •
        (KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) -
         KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (x_gen W))) := by
  set D := KaehlerDifferential.D K W.toAffine.FunctionField
  set N := y_gen W - α.pullback (y_gen W) with hN
  set Den := x_gen W - α.pullback (x_gen W) with hDen
  have hDen_ne : Den ≠ 0 := sub_ne_zero.mpr h_ne
  have h_slope : addSlope W α = N / Den := by
    rw [addSlope, hN, hDen]
    exact (W_KE W).toAffine.slope_of_X_ne h_ne
  rw [h_slope, D.leibniz_div N Den]
  have h_DN : D N = D (y_gen W) - D (α.pullback (y_gen W)) := by rw [hN, map_sub]
  have h_DDen : D Den = D (x_gen W) - D (α.pullback (x_gen W)) := by rw [hDen, map_sub]
  rw [h_DN, h_DDen, smul_smul,
    show Den ^ 2 * Den⁻¹ ^ 2 = 1 from by rw [← mul_pow, mul_inv_cancel₀ hDen_ne, one_pow],
    one_smul]

/-- **Sub-helper 129** (D(γ.pullback x_gen) cleared form, axiom-clean):

Combines sub-helper 110 (`D(addPullback_x) = (2ℓ + a₁) • D(ℓ) - D(x_gen)`)
with sub-helper 128 (`Den² • D(addSlope) = Den • D(y_gen) - N • D(x_gen)`)
to give a single closed-form identity for D(γ.pullback x_gen) involving
D(y_gen) and D(x_gen) (with Den² as the multiplier).

Specifically:
```
Den² • D(γ.pullback x_gen) = (2ℓ + a₁) • Den • D(y_gen)
                            - (2ℓ + a₁) • N • D(x_gen)
                            - Den² • D(x_gen)
```

where ℓ = addSlope, Den = x_gen - π·x, N = y_gen - π·y.

This is the substantive D(γ.pullback x_gen) reduction in K(E), expressed
purely in terms of the curve generators' Kähler differentials and Den, N
without any inverses. Foundational for the III.5.2 cascade closure. -/
theorem kaehler_D_addPullback_x_negFrobenius_cleared
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField
          (addPullback_x W (negFrobeniusIsog W)) =
      (2 * addSlope W (negFrobeniusIsog W) + algebraMap K KE W.a₁) •
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) •
          KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W)) -
      (2 * addSlope W (negFrobeniusIsog W) + algebraMap K KE W.a₁) •
        ((y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) •
          KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W)) -
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
  -- Multiply sub-helper 110 by Den² and use sub-helper 128.
  rw [kaehler_D_addPullback_x_negFrobenius W p, smul_sub, smul_smul]
  rw [mul_comm ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2)
      (2 * addSlope W (negFrobeniusIsog W) + algebraMap K KE W.a₁)]
  rw [← smul_smul, kaehler_D_addSlope_negFrobenius W p, smul_sub]

/-- **Route B core (III.5.2), general cleared form**: combines `kaehler_D_addPullback_x_general`
with `kaehler_D_addSlope_general` to clear the `Den²` denominator from `D(addPullback_x)` for
arbitrary `α` (non-doubling). Generalizes `kaehler_D_addPullback_x_negFrobenius_cleared`. -/
theorem kaehler_D_addPullback_x_general_cleared
    (α : Isogeny W.toAffine W.toAffine)
    (h_ne : x_gen W ≠ α.pullback (x_gen W)) :
    (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField (addPullback_x W α) =
      (2 * addSlope W α + algebraMap K KE W.a₁) •
        ((x_gen W - α.pullback (x_gen W)) •
          (KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) -
           KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (y_gen W)))) -
      (2 * addSlope W α + algebraMap K KE W.a₁) •
        ((y_gen W - α.pullback (y_gen W)) •
          (KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) -
           KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (x_gen W)))) -
      (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) -
      (x_gen W - α.pullback (x_gen W)) ^ 2 •
        KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (x_gen W)) := by
  rw [kaehler_D_addPullback_x_general W α, smul_sub, smul_sub, smul_smul,
    mul_comm ((x_gen W - α.pullback (x_gen W)) ^ 2)
      (2 * addSlope W α + algebraMap K KE W.a₁),
    ← smul_smul, kaehler_D_addSlope_general W α h_ne, smul_sub]

/-- **RB-ω1**: `D(x_gen) = u_gen • ω` (immediate from `ω = u_gen⁻¹ • D(x_gen)`). -/
theorem kaehler_D_x_gen_eq_u_smul_omega :
    KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) =
      u_gen W • invariantDifferential W.toAffine := by
  rw [show invariantDifferential W.toAffine =
        (u_gen W)⁻¹ • KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) from rfl,
    smul_smul, mul_inv_cancel₀ (u_gen_ne_zero W), one_smul]

/-- **RB-ω2 leaf**: `D(y_gen) = (3x²+2a₂x+a₄−a₁y) • ω`. From the curve-equation differential
`u_gen·D(y) = (3x²+2a₂x+a₄−a₁y)·D(x)` (Sub-helper 121 chain) and `D(x) = u_gen·ω` (RB-ω1),
dividing through by `u_gen ≠ 0`. Silverman III.5: the relation `(2y+a₁x+a₃)dy =
(3x²+2a₂x+a₄−a₁y)dx` from differentiating the Weierstrass equation. -/
theorem kaehler_D_y_gen_eq_num_smul_omega :
    KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) =
      (3 * x_gen W ^ 2 + 2 * algebraMap K KE W.a₂ * x_gen W +
        algebraMap K KE W.a₄ - algebraMap K KE W.a₁ * y_gen W) •
        invariantDifferential W.toAffine := by
  have h127 := kaehler_curve_equation_K_E W
  have hu : algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
      algebraMap K KE W.a₁ * x_gen W = u_gen W := by
    change algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
        algebraMap K KE W.a₁ * x_gen W =
      2 * y_gen W + algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃
    ring
  rw [hu] at h127
  have h2 : u_gen W • KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W) =
      u_gen W • ((3 * x_gen W ^ 2 + 2 * algebraMap K KE W.a₂ * x_gen W +
        algebraMap K KE W.a₄ - algebraMap K KE W.a₁ * y_gen W) •
        invariantDifferential W.toAffine) := by
    rw [h127, kaehler_D_x_gen_eq_u_smul_omega, smul_comm]
  exact smul_right_injective _ (u_gen_ne_zero W) h2

/-- **RB-ω3 leaf** (α-image differentials): for the omega coefficient
`a_α = omegaPullbackCoeff W α`, `D(α*x) = (α*u)·a_α·ω` and `D(α*y) = (α*num)·a_α·ω`. From
`omegaPullbackCoeff_spec` (`a_α•ω = (α*u)⁻¹•D(α*x)`) and the α-image curve-equation differential
(Sub-helper 121 at the pulled-back point `(α*x, α*y)`, also on the curve by `pullback_equation`). -/
theorem kaehler_D_alpha_pullback_x_eq_smul_omega
    (α : Isogeny W.toAffine W.toAffine) :
    KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (x_gen W)) =
      (alpha_star_u W α * omegaPullbackCoeff W α) • invariantDifferential W.toAffine := by
  have h_au_ne : alpha_star_u W α ≠ 0 := by
    rw [alpha_star_u_eq]
    exact fun h ↦ u_gen_ne_zero W (α.pullback_injective (by rw [h, map_zero]))
  have hspec := omegaPullbackCoeff_spec W α
  rw [show (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) = x_gen W from rfl]
    at hspec
  have key : alpha_star_u W α • (omegaPullbackCoeff W α • invariantDifferential W.toAffine) =
      KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (x_gen W)) := by
    rw [hspec, smul_smul, mul_inv_cancel₀ h_au_ne, one_smul]
  rw [← key, smul_smul]

/-- **RB-ω3b leaf** (α-image `D(y)`): `D(α*y) = (α*num)·a_α·ω`. From the α-image curve-equation
differential (apply `Isogeny.pullbackKaehler` to `kaehler_curve_equation_K_E` — `pullbackKaehler` is
α-semilinear and sends `D g ↦ D(α*g)`) + `kaehler_D_alpha_pullback_x_eq_smul_omega` (RB-ω3a), cancel
`α*u ≠ 0`. -/
theorem kaehler_D_alpha_pullback_y_eq_smul_omega
    (α : Isogeny W.toAffine W.toAffine) :
    KaehlerDifferential.D K W.toAffine.FunctionField (α.pullback (y_gen W)) =
      ((3 * (α.pullback (x_gen W)) ^ 2 +
          2 * algebraMap K KE W.a₂ * (α.pullback (x_gen W)) +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * (α.pullback (y_gen W))) *
        omegaPullbackCoeff W α) • invariantDifferential W.toAffine := by
  have h_au_ne : alpha_star_u W α ≠ 0 := by
    rw [alpha_star_u_eq]
    exact fun h ↦ u_gen_ne_zero W (α.pullback_injective (by rw [h, map_zero]))
  have hx := kaehler_D_alpha_pullback_x_eq_smul_omega W α
  -- α-image curve-equation differential via pullbackKaehler of `kaehler_curve_equation_K_E`.
  have himg := congrArg (Isogeny.pullbackKaehler α) (kaehler_curve_equation_K_E W)
  rw [Isogeny.pullbackKaehler_smul_KE, Isogeny.pullbackKaehler_smul_KE,
    Isogeny.pullbackKaehler_D, Isogeny.pullbackKaehler_D] at himg
  -- Reconcile the pulled-back coefficients with `alpha_star_u` and the goal's `α*num`.
  have hC : α.pullback (algebraMap K KE W.a₃ + 2 * y_gen W +
      algebraMap K KE W.a₁ * x_gen W) = alpha_star_u W α := by
    rw [alpha_star_u_eq, u_gen]
    simp only [map_add, map_mul, map_ofNat, AlgHom.commutes,
      show α.pullback (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (AdjoinRoot.root W.toAffine.polynomial)) = α.pullback (y_gen W) from rfl,
      show α.pullback (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (algebraMap (Polynomial K) W.toAffine.CoordinateRing Polynomial.X)) =
          α.pullback (x_gen W) from rfl]
    ring
  have hN : α.pullback ((3 : KE) * x_gen W ^ 2 +
      2 * algebraMap K KE W.a₂ * x_gen W + algebraMap K KE W.a₄ -
      algebraMap K KE W.a₁ * y_gen W) =
      3 * (α.pullback (x_gen W)) ^ 2 +
        2 * algebraMap K KE W.a₂ * (α.pullback (x_gen W)) +
        algebraMap K KE W.a₄ - algebraMap K KE W.a₁ * (α.pullback (y_gen W)) := by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, AlgHom.commutes]
  rw [hC, hN, hx, smul_smul] at himg
  -- himg : alpha_star_u • D(α*y) = (α*num * (α*u * a_α)) • ω
  refine smul_right_injective _ h_au_ne (?_ : alpha_star_u W α • _ = alpha_star_u W α • _)
  rw [himg, smul_smul]
  congr 1
  ring

/-- **RB-ω4 leaf (the III.5.2 ring collapse)**: for genuine α (x≠α*x), the differential of the
addition-pullback x-coordinate equals `addPullback_u • (1 + a_α) • ω`, where
`addPullback_u = 2·addPullback_y + a₁·addPullback_x + a₃` is the u-coordinate at the sum point.
Obtained by substituting RB-ω1/ω2/ω3 into `kaehler_D_addPullback_x_general_cleared` (clearing
`Den²`), reducing to a single ring identity in `K(E)` (the addition-formula `addX`/`addSlope`
definitions + the Weierstrass relations at both points). This is the entire substantive content
of Silverman III.5.2, now a self-contained ring-identity leaf. -/
theorem kaehler_D_addPullback_x_eq_one_add_smul_omega
    (α : Isogeny W.toAffine W.toAffine)
    (h_ne : x_gen W ≠ α.pullback (x_gen W)) :
    KaehlerDifferential.D K W.toAffine.FunctionField (addPullback_x W α) =
      (2 * addPullback_y W α + algebraMap K KE W.a₁ * addPullback_x W α +
        algebraMap K KE W.a₃) •
        ((1 + omegaPullbackCoeff W α) • invariantDifferential W.toAffine) := by
  have hDen2_ne : (x_gen W - α.pullback (x_gen W)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (sub_ne_zero.mpr h_ne)
  have hcleared := kaehler_D_addPullback_x_general_cleared W α h_ne
  rw [kaehler_D_x_gen_eq_u_smul_omega W, kaehler_D_y_gen_eq_num_smul_omega W,
    kaehler_D_alpha_pullback_x_eq_smul_omega W α,
    kaehler_D_alpha_pullback_y_eq_smul_omega W α] at hcleared
  refine smul_right_injective _ hDen2_ne (?_ :
    (x_gen W - α.pullback (x_gen W)) ^ 2 • _ =
      (x_gen W - α.pullback (x_gen W)) ^ 2 • _)
  rw [hcleared]
  simp only [smul_smul, ← sub_smul]
  congr 1
  -- The scalar identity in `K(E)` holds ONLY MODULO the Weierstrass relation at BOTH
  -- P = (x_gen, y_gen) and α(P) = (α*x, α*y): the denominator-cleared bracket differs from
  -- `Den²·u₃·(1 + a_α)` by exactly `(2N + a₁·Den)·(1 - a_α)·(g_{α(P)} - g_P)` (with `N = y - α*y`,
  -- `Den = x - α*x`, `g` the Weierstrass polynomial, zero on the curve). So it is a
  -- `linear_combination` of the two curve equations, not bare `ring`.
  rw [addPullback_y, addPullback_x]
  rw [show addSlope W α =
      (y_gen W - α.pullback (y_gen W)) / (x_gen W - α.pullback (x_gen W)) from by
        rw [addSlope]; exact (W_KE W).toAffine.slope_of_X_ne h_ne]
  rw [show u_gen W = 2 * y_gen W + algebraMap K KE W.a₁ * x_gen W + algebraMap K KE W.a₃ from rfl,
    show alpha_star_u W α = 2 * α.pullback (y_gen W) +
      algebraMap K KE W.a₁ * α.pullback (x_gen W) + algebraMap K KE W.a₃ from rfl]
  have hP := generic_equation W
  rw [WeierstrassCurve.Affine.equation_iff] at hP
  have hαP := pullback_equation W α
  rw [WeierstrassCurve.Affine.equation_iff] at hαP
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    W_KE, WeierstrassCurve.toAffine, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hP hαP ⊢
  field_simp [sub_ne_zero.mpr h_ne]
  set X := x_gen W with hX
  set Y := y_gen W with hY
  set PX := α.pullback X with hPX
  set PY := α.pullback Y with hPY
  set c1 := algebraMap K KE W.a₁ with hc1
  -- `bracket − Den²·u₃·(1 + a_α) = (2N + a₁·Den)(1 − a_α)(g_{α(P)} − g_P)`, hence the coefficients:
  linear_combination
    (-(2 * (Y - PY) + c1 * (X - PX)) * (1 - omegaPullbackCoeff W α)) * hP +
      ((2 * (Y - PY) + c1 * (X - PX)) * (1 - omegaPullbackCoeff W α)) * hαP

/-- **Sub-helper 130** (D(addSlope) reduced to D(x_gen) via curve equation, axiom-clean):

Combines sub-helper 127 (curve equation Kähler identity) with sub-helper 128
(D(slope) identity) to express D(addSlope) entirely in terms of D(x_gen):

```
(u_gen · Den²) • D(addSlope) = (Den · num - u_gen · N) • D(x_gen)
```

where:
- u_gen = a₃ + 2y + a₁x
- Den = x - π·x
- N = y - π·y
- num = 3x² + 2a₂x + a₄ - a₁y

Substantive K(E) Kähler identity — combines axiom-clean Path A sub-helpers
127 + 128. Foundational for ω(γ) = 1 via the Kähler-witness route. -/
theorem kaehler_D_addSlope_via_curve_equation_negFrobenius
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ((algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
        algebraMap K KE W.a₁ * x_gen W) *
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) •
        KaehlerDifferential.D K W.toAffine.FunctionField
          (addSlope W (negFrobeniusIsog W)) =
      ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) *
        ((3 : KE) * x_gen W ^ 2 +
          (2 : KE) * algebraMap K KE W.a₂ * x_gen W +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * y_gen W) -
        (algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
          algebraMap K KE W.a₁ * x_gen W) *
          (y_gen W - (negFrobeniusIsog W).pullback (y_gen W))) •
        KaehlerDifferential.D K W.toAffine.FunctionField (x_gen W) := by
  -- Multiply sub-helper 128 by u_gen' on the left, then substitute via 127.
  have h_slope := kaehler_D_addSlope_negFrobenius W p
  have h_curve := kaehler_curve_equation_K_E W
  -- Step 1: multiply h_slope by u_gen' (smul-distribute).
  -- Step 2: substitute h_curve to convert u_gen' • D(y) → num • D(x).
  rw [mul_smul, h_slope, smul_sub]
  rw [show (algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
        algebraMap K KE W.a₁ * x_gen W) •
      ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) •
        KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W)) =
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) •
      ((algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
        algebraMap K KE W.a₁ * x_gen W) •
        KaehlerDifferential.D K W.toAffine.FunctionField (y_gen W)) from
      smul_comm _ _ _]
  rw [h_curve]
  -- Now collect smul forms.
  rw [smul_smul, smul_smul, ← sub_smul]

/-- **Sub-helper 131** (`alpha_star_u` computed explicitly for γ, axiom-clean):
the explicit form of `alpha_star_u (isogOneSub_negFrobenius W hq)` in K(E):
`α*(u) = 2·addPullback_y + a₁·addPullback_x + a₃`.

Direct from `alpha_star_u_eq` + sub-helpers 89b, 89c (axiom-clean
`γ.pullback x_gen = addPullback_x` and `γ.pullback y_gen = addPullback_y`)
+ `u_gen` definition. -/
theorem alpha_star_u_isogOneSub_negFrobenius
    (hq : 2 ≤ Fintype.card K) :
    alpha_star_u W (isogOneSub_negFrobenius W hq) =
      2 * addPullback_y W (negFrobeniusIsog W) +
        algebraMap K KE W.a₁ * addPullback_x W (negFrobeniusIsog W) +
        algebraMap K KE W.a₃ := by
  rw [alpha_star_u_eq]
  show (isogOneSub_negFrobenius W hq).pullback (u_gen W) = _
  unfold u_gen
  rw [map_add, map_add, map_mul, map_mul, map_ofNat]
  rw [show (isogOneSub_negFrobenius W hq).pullback
        (algebraMap (Affine.CoordinateRing W.toAffine) KE
          (algebraMap (Polynomial K) (Affine.CoordinateRing W.toAffine) Polynomial.X)) =
      addPullback_x W (negFrobeniusIsog W) from
      addPullbackAlgHom_negFrobenius_x_gen_eq W hq]
  rw [show (isogOneSub_negFrobenius W hq).pullback
        (algebraMap (Affine.CoordinateRing W.toAffine) KE
          (AdjoinRoot.root W.toAffine.polynomial)) =
      addPullback_y W (negFrobeniusIsog W) from
      addPullbackAlgHom_negFrobenius_y_gen_eq W hq]
  rw [(isogOneSub_negFrobenius W hq).pullback.commutes W.a₁,
      (isogOneSub_negFrobenius W hq).pullback.commutes W.a₃]

/-- **Sub-helper 132** (α*(u) + u_gen identity in K(E), axiom-clean):

`α*(u) + u_gen = -(2ℓ + a₁) · (addPullback_x - x_gen)` in K(E)

where ℓ = addSlope W (negFrobeniusIsog W).

Proof: substitute α*(u) = 2·addPullback_y + a₁·addPullback_x + a₃ (sub-helper 131)
and addPullback_y via Affine.addY/negY/negAddY definitional unfoldings,
then verify by ring algebra in K(E).

This is the substantive K(E) identity that simplifies the RHS of the
target Kähler-witness identity to:
`(α*(u) + u_gen) · Den² = -(2ℓ + a₁) · (addPullback_x - x_gen) · Den²`.

Combined with sub-helper 130 (LHS reduction), the target K(E) identity
becomes a sub-divisible polynomial identity. -/
theorem alpha_star_u_plus_u_gen_negFrobenius
    (hq : 2 ≤ Fintype.card K) :
    alpha_star_u W (isogOneSub_negFrobenius W hq) + u_gen W =
      -((2 * addSlope W (negFrobeniusIsog W) +
          algebraMap K KE W.a₁) *
        (addPullback_x W (negFrobeniusIsog W) - x_gen W)) := by
  rw [alpha_star_u_isogOneSub_negFrobenius W hq]
  unfold u_gen addPullback_y addPullback_x x_gen y_gen
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]
  -- Unfold W_KE coefficients to algebraMap-images of W coefficients.
  have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.a₁ := rfl
  have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.a₂ := rfl
  have h_a3 : (W_KE W).toAffine.a₃ = algebraMap K KE W.a₃ := rfl
  rw [h_a1, h_a2, h_a3]
  ring

/-- **Sub-helper 133** (curve equation for π·(x_gen, y_gen) in K(E), axiom-clean):

The π-shifted Weierstrass equation in K(E):
`(π·y)² + a₁(π·x)(π·y) + a₃(π·y) = (π·x)³ + a₂(π·x)² + a₄(π·x) + a₆`

where π·x = (negFrob).pullback x_gen, π·y = (negFrob).pullback y_gen.

Proof: apply `(negFrobeniusIsog W).pullback` (a K-algebra hom) to
`weierstrass_equation_in_KE` (sub-helper 120). The hom respects + and *
and fixes algebraMap-images of K, so the equation transforms term-by-term. -/
theorem weierstrass_equation_pi_negFrobenius :
    (negFrobeniusIsog W).pullback (y_gen W) ^ 2 +
        algebraMap K KE W.a₁ *
          (negFrobeniusIsog W).pullback (x_gen W) *
          (negFrobeniusIsog W).pullback (y_gen W) +
        algebraMap K KE W.a₃ *
          (negFrobeniusIsog W).pullback (y_gen W) =
      (negFrobeniusIsog W).pullback (x_gen W) ^ 3 +
        algebraMap K KE W.a₂ *
          (negFrobeniusIsog W).pullback (x_gen W) ^ 2 +
        algebraMap K KE W.a₄ *
          (negFrobeniusIsog W).pullback (x_gen W) +
        algebraMap K KE W.a₆ := by
  have h := weierstrass_equation_in_KE W
  -- Apply (negFrob).pullback to both sides; it's a ring hom.
  have h_pi := congrArg (negFrobeniusIsog W).pullback h
  simp only [map_add, map_mul, map_pow,
    AlgHom.commutes (negFrobeniusIsog W).pullback] at h_pi
  exact h_pi

/-- **Sub-helper 134** (substantive K(E) polynomial identity for III.5.2, axiom-clean):

The K(E) ring identity that closes the Kähler-witness route to ω(γ) = 1:

```
(x - π·x) · num - u_gen · (y - π·y) +
  (addPullback_x - x_gen) · (x - π·x)² = 0
```

where:
- x, y, π·x, π·y are x_gen, y_gen, (negFrob).pullback x_gen,
  (negFrob).pullback y_gen.
- num = 3x² + 2a₂x + a₄ - a₁y.
- u_gen = 2y + a₁x + a₃.
- addPullback_x = ℓ² + a₁ℓ - a₂ - x - π·x where ℓ = (y - π·y) / (x - π·x).
- (addPullback_x - x_gen) · (x - π·x)² = (y - π·y)² + a₁·(y - π·y)·(x - π·x)
  - a₂·(x - π·x)² - (2x + π·x)·(x - π·x)² (substituting ℓ via N/Den).

Proof: substitute the slope formula `ℓ = (y - π·y)/(x - π·x)` (squared and
multiplied by Den² gives the polynomial form), then close via
`linear_combination` with the two curve equations (sub-helpers 120 + 133)
as multipliers. The identity holds because γ = id - π is a curve isogeny,
which respects the curve equation.

This is the substantive III.5.2 K(E) polynomial content. -/
theorem kaehler_witness_polynomial_identity_negFrobenius :
    (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) *
        ((3 : KE) * x_gen W ^ 2 +
          (2 : KE) * algebraMap K KE W.a₂ * x_gen W +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * y_gen W) -
      (algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
        algebraMap K KE W.a₁ * x_gen W) *
        (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) +
      ((y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) ^ 2 +
        algebraMap K KE W.a₁ *
          (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) *
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) -
        algebraMap K KE W.a₂ *
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 -
        ((2 : KE) * x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) *
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2) = 0 := by
  have h_curve := weierstrass_equation_in_KE W
  have h_curve_pi := weierstrass_equation_pi_negFrobenius W
  linear_combination -h_curve + h_curve_pi

/-- **Sub-helper 135** ((addPullback_x - x_gen) · Den² polynomial form, axiom-clean):

```
(addPullback_x - x_gen) · Den² =
  (y - π·y)² + a₁·(y - π·y)·(x - π·x)
  - a₂·(x - π·x)² - (2x + π·x)·(x - π·x)²
```

Direct from `addPullback_x = ℓ² + a₁ℓ - a₂ - x - π·x` (Affine.addX) and
slope formula `ℓ = (y - π·y) / (x - π·x)` giving `ℓ · (x - π·x) = (y - π·y)`,
hence `ℓ² · (x - π·x)² = (y - π·y)²` and `ℓ · (x - π·x)² = (y - π·y) · (x - π·x)`.

Substantive polynomial-form bridge between the slope-divisor identity
and the curve-equation polynomial identity (sub-helper 134). -/
theorem addPullback_x_sub_x_gen_mul_Den_sq_negFrobenius :
    (addPullback_x W (negFrobeniusIsog W) - x_gen W) *
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 =
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) ^ 2 +
        algebraMap K KE W.a₁ *
          (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) *
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) -
        algebraMap K KE W.a₂ *
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 -
        ((2 : KE) * x_gen W + (negFrobeniusIsog W).pullback (x_gen W)) *
          (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 := by
  unfold addPullback_x
  simp only [WeierstrassCurve.Affine.addX]
  have h_a1 : (W_KE W).toAffine.a₁ = algebraMap K KE W.a₁ := rfl
  have h_a2 : (W_KE W).toAffine.a₂ = algebraMap K KE W.a₂ := rfl
  rw [h_a1, h_a2]
  -- Substitute ℓ via slope formula: ℓ · (x - π·x) = (y - π·y).
  have h_slope_lin : addSlope W (negFrobeniusIsog W) *
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) =
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) := by
    rw [addSlope_negFrobeniusIsog_eq W, div_mul_cancel₀]
    exact x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  -- Goal is (ℓ² + a₁ℓ - a₂ - x - π·x - x) · Den² = N² + a₁·N·Den - a₂·Den² - (2x+π·x)·Den².
  -- Where ℓ·Den = N (h_slope_lin), so ℓ²·Den² = N², ℓ·Den² = N·Den.
  have h_slope_sq : (addSlope W (negFrobeniusIsog W) *
      (x_gen W - (negFrobeniusIsog W).pullback (x_gen W))) ^ 2 =
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) ^ 2 := by
    rw [h_slope_lin]
  -- LHS - RHS = (ℓ·Den - N) · (ℓ·Den + N + a₁·Den)
  -- and h_slope_lin says ℓ·Den - N = 0 (after rearranging ℓ·Den = N).
  -- Linear combination multiplier: (ℓ·Den + N + a₁·Den).
  linear_combination
    (addSlope W (negFrobeniusIsog W) *
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) +
      (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) +
      algebraMap K KE W.a₁ *
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W))) * h_slope_lin

/-- **Sub-helper 136** (curve-equation form of K(E) Kähler-witness identity, axiom-clean):

```
Den · num - u_gen · N + (addPullback_x - x_gen) · Den² = 0
```

Combines sub-helper 134 (polynomial form identity) with sub-helper 135
(`(addPullback_x - x_gen) · Den² = polynomial form`) to give the K(E)
identity in the form needed by the Kähler-witness consumer.

This is THE identity that closes ω(γ) = 1 / Witness #1 / III.5.2 via
the Kähler witness route. -/
theorem kaehler_witness_curve_form_negFrobenius :
    (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) *
        ((3 : KE) * x_gen W ^ 2 +
          (2 : KE) * algebraMap K KE W.a₂ * x_gen W +
          algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * y_gen W) -
      (algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
        algebraMap K KE W.a₁ * x_gen W) *
        (y_gen W - (negFrobeniusIsog W).pullback (y_gen W)) +
      (addPullback_x W (negFrobeniusIsog W) - x_gen W) *
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 = 0 := by
  rw [addPullback_x_sub_x_gen_mul_Den_sq_negFrobenius W]
  exact kaehler_witness_polynomial_identity_negFrobenius W

/-- **Sub-helper 137** (K(E) coefficient identity for Kähler witness, axiom-clean):
the K(E) coefficient identity that closes the Kähler-witness chain:

```
(2ℓ + a₁) · (Den · num - u_gen · N) = (α*(u) + u_gen) · Den²
```

Combines sub-helpers 132 + 136 axiom-clean. -/
theorem kaehler_witness_coefficient_identity_negFrobenius
    (hq : 2 ≤ Fintype.card K) :
    ((2 : KE) * addSlope W (negFrobeniusIsog W) +
        algebraMap K KE W.a₁) *
        ((x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) *
          ((3 : KE) * x_gen W ^ 2 +
            (2 : KE) * algebraMap K KE W.a₂ * x_gen W +
            algebraMap K KE W.a₄ -
            algebraMap K KE W.a₁ * y_gen W) -
          (algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
            algebraMap K KE W.a₁ * x_gen W) *
            (y_gen W - (negFrobeniusIsog W).pullback (y_gen W))) =
      (alpha_star_u W (isogOneSub_negFrobenius W hq) + u_gen W) *
        (x_gen W - (negFrobeniusIsog W).pullback (x_gen W)) ^ 2 := by
  rw [alpha_star_u_plus_u_gen_negFrobenius W hq]
  -- Use sub-helper 136 (curve-form K(E) identity, axiom-clean):
  -- Den·num - u_gen·N + (addPullback_x - x_gen)·Den² = 0.
  -- Multiply by (2ℓ+a₁) to get: (2ℓ+a₁)·(Den·num - u_gen·N + (addPullback_x - x_gen)·Den²) = 0.
  -- Rearrange to: (2ℓ+a₁)·(Den·num - u_gen·N) = -(2ℓ+a₁)·(addPullback_x - x_gen)·Den².
  have h_136 := kaehler_witness_curve_form_negFrobenius W
  linear_combination
    (2 * addSlope W (negFrobeniusIsog W) + algebraMap K KE W.a₁) * h_136

/-- **Sub-helper 138** (ω(γ) = 1 axiom-clean — Witness #1 omega-coefficient).

Instantiates `kaehler_witness_via_slope_deriv_witness` with the explicit
witness `c := (Den · num - u · N) / (u · Den²)`, where `u = a₃ + 2y + a₁x`,
`Den = x - π·x`, `N = y - π·y`, `num = 3x² + 2a₂x + a₄ - a₁y`.

The slope-deriv witness `D(addSlope) = c • D(x_gen)` follows from sub-helper
130 by smul-cancelling `u · Den²`. The K(E) coefficient identity
`((2ℓ + a₁) · c - 1) · u_gen = α*(u)` follows from sub-helper 137 by
field-simplification + linear_combination. -/
theorem omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 2 ≤ Fintype.card K) :
    omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1 := by
  apply omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one_via_kaehler_witness W hq
  set Den : KE := x_gen W - (negFrobeniusIsog W).pullback (x_gen W) with hDen
  set N : KE := y_gen W - (negFrobeniusIsog W).pullback (y_gen W) with hN
  set num : KE := (3 : KE) * x_gen W ^ 2 +
      (2 : KE) * algebraMap K KE W.a₂ * x_gen W +
      algebraMap K KE W.a₄ -
      algebraMap K KE W.a₁ * y_gen W with hnum
  set u : KE := algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
      algebraMap K KE W.a₁ * x_gen W with hu
  have hDen_ne : Den ≠ 0 := x_gen_sub_negFrobeniusIsog_pullback_x_gen_ne_zero W
  have hDen_sq_ne : Den ^ 2 ≠ 0 := pow_ne_zero _ hDen_ne
  have hu_eq : u = u_gen W := by
    change algebraMap K KE W.a₃ + (2 : KE) * y_gen W +
         algebraMap K KE W.a₁ * x_gen W = u_gen W
    unfold u_gen y_gen x_gen
    ring
  have hu_ne : u ≠ 0 := hu_eq ▸ u_gen_ne_zero W
  have huDen_ne : u * Den ^ 2 ≠ 0 := mul_ne_zero hu_ne hDen_sq_ne
  refine kaehler_witness_via_slope_deriv_witness W p hq
    ((Den * num - u * N) / (u * Den ^ 2)) ?_ ?_
  · -- h_slope_deriv: D(addSlope) = c • D(x_gen).
    have h_130 := kaehler_D_addSlope_via_curve_equation_negFrobenius W p
    rw [div_eq_inv_mul, ← smul_smul, ← h_130, smul_smul,
      inv_mul_cancel₀ huDen_ne, one_smul]
  · -- h_KE_identity: ((2ℓ + a₁) * c - 1) * u_gen W = α*(u).
    have h_137 := kaehler_witness_coefficient_identity_negFrobenius W hq
    rw [← hu_eq] at h_137 ⊢
    rw [mul_div_assoc', sub_mul, one_mul, div_mul_eq_mul_div,
        sub_eq_iff_eq_add, div_eq_iff huDen_ne]
    linear_combination u * h_137

/-- **Sub-helper 139** (Witness #1 axiom-clean — IsSeparable γ).

Composes sub-helper 138 (ω(γ) = 1 axiom-clean) with
`isogOneSub_negFrobenius_isSeparable_of_h_coeff_only` (T-II-4-004 absorbed,
axiom-clean) to produce the unconditional Witness #1 of the Hasse-Weil bound. -/
theorem isogOneSub_negFrobenius_isSeparable
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hq : 2 ≤ Fintype.card K) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  isogOneSub_negFrobenius_isSeparable_of_h_coeff_only W hq
    (omegaPullbackCoeff_isogOneSub_negFrobenius_eq_one W p hq)

/-- Pure-algebra core of `kaehler_D_addPullback_x_pair_eq_smul_omega`: the denominator-cleared
scalar identity, abstracted over a commutative ring with the two pullback Weierstrass equations
`hα₁ hα₂` as hypotheses. Extracting it as a free-variable `linear_combination` keeps the parent
theorem's `field_simp` step and this `ring` step in separate declarations, each under the default
heartbeat budget. -/
theorem kaehler_D_addPullback_x_pair_ring_identity {R : Type*} [CommRing R]
    (X₁ X₂ Y₁ Y₂ c1 a₁ a₂ A₂ A₃ A₄ A₆ : R)
    (hα₁ : Y₁ ^ 2 + c1 * X₁ * Y₁ + A₃ * Y₁ = X₁ ^ 3 + A₂ * X₁ ^ 2 + A₄ * X₁ + A₆)
    (hα₂ : Y₂ ^ 2 + c1 * X₂ * Y₂ + A₃ * Y₂ = X₂ ^ 3 + A₂ * X₂ ^ 2 + A₄ * X₂ + A₆) :
    (2 * (Y₁ - Y₂) + (X₁ - X₂) * c1) *
            ((X₁ - X₂) *
                ((X₁ * (X₁ * 3 + 2 * A₂) + A₄ - Y₁ * c1) * a₁ -
                  (X₂ * (X₂ * 3 + 2 * A₂) + A₄ - Y₂ * c1) * a₂) -
              (Y₁ - Y₂) * (a₁ * (2 * Y₁ + X₁ * c1 + A₃) - a₂ * (2 * Y₂ + X₂ * c1 + A₃))) -
          (X₁ - X₂) ^ 3 * a₁ * (2 * Y₁ + X₁ * c1 + A₃) -
        (X₁ - X₂) ^ 3 * a₂ * (2 * Y₂ + X₂ * c1 + A₃) =
      (2 *
              (-((Y₁ - Y₂) *
                        ((Y₁ - Y₂) * (Y₁ - Y₂ + (X₁ - X₂) * c1) - (X₁ - X₂) ^ 2 * A₂ -
                              (X₁ - X₂) ^ 2 * X₁ - (X₁ - X₂) ^ 2 * X₂ - (X₁ - X₂) ^ 2 * X₁) +
                      (X₁ - X₂) ^ 3 * Y₁) -
                  (X₁ - X₂) * c1 *
                    ((Y₁ - Y₂) * (Y₁ - Y₂ + (X₁ - X₂) * c1) - (X₁ - X₂) ^ 2 * A₂ -
                        (X₁ - X₂) ^ 2 * X₁ - (X₁ - X₂) ^ 2 * X₂) -
                (X₁ - X₂) ^ 3 * A₃) +
            (X₁ - X₂) * c1 *
              ((Y₁ - Y₂) * (Y₁ - Y₂ + (X₁ - X₂) * c1) - (X₁ - X₂) ^ 2 * A₂ -
                  (X₁ - X₂) ^ 2 * X₁ - (X₁ - X₂) ^ 2 * X₂) +
          (X₁ - X₂) ^ 3 * A₃) *
        (a₁ + a₂) := by
  linear_combination
    (-(2 * (Y₁ - Y₂) + c1 * (X₁ - X₂)) * (a₁ - a₂)) * hα₁ +
      ((2 * (Y₁ - Y₂) + c1 * (X₁ - X₂)) * (a₁ - a₂)) * hα₂

/-- **General-pair III.5.2 differential collapse**: for genuine pairs (`α₁*x ≠ α₂*x`), the
differential of the pair addition `x`-coordinate is
`u₃ • ((a_{α₁} + a_{α₂}) • ω)`, where `u₃ = 2·addPullback_y_pair + a₁·addPullback_x_pair + a₃`
is the `u`-coordinate at the sum point. The general-pair analogue of
`kaehler_D_addPullback_x_eq_one_add_smul_omega`; both points now use the general image-differential
leaves `kaehler_D_alpha_pullback_x/y_eq_smul_omega`, and the final scalar identity is a
`linear_combination` of the two pullback Weierstrass equations (`pullback_equation α₁/α₂`). -/
theorem kaehler_D_addPullback_x_pair_eq_smul_omega
    (α₁ α₂ : Isogeny W.toAffine W.toAffine)
    (h_ne : α₁.pullback (x_gen W) ≠ α₂.pullback (x_gen W)) :
    KaehlerDifferential.D K W.toAffine.FunctionField (addPullback_x_pair α₁ α₂) =
      (2 * addPullback_y_pair α₁ α₂ + algebraMap K KE W.a₁ * addPullback_x_pair α₁ α₂ +
        algebraMap K KE W.a₃) •
        ((omegaPullbackCoeff W α₁ + omegaPullbackCoeff W α₂) •
          invariantDifferential W.toAffine) := by
  set D := KaehlerDifferential.D K W.toAffine.FunctionField with hD_def
  set X₁ := α₁.pullback (x_gen W) with hX₁
  set X₂ := α₂.pullback (x_gen W) with hX₂
  set Y₁ := α₁.pullback (y_gen W) with hY₁
  set Y₂ := α₂.pullback (y_gen W) with hY₂
  have hDen_ne : X₁ - X₂ ≠ 0 := sub_ne_zero.mpr h_ne
  have hDen2_ne : (X₁ - X₂) ^ 2 ≠ 0 := pow_ne_zero 2 hDen_ne
  -- Slope = (Y₁ - Y₂)/(X₁ - X₂).
  have h_slope : addSlopePair α₁ α₂ = (Y₁ - Y₂) / (X₁ - X₂) :=
    addSlopePair_eq_of_x_ne h_ne
  -- STEP 1: D(addPullback_x_pair) cleared of Den² (mirror `kaehler_D_addPullback_x_general` +
  -- `kaehler_D_addSlope_general`, with X₁/Y₁ in place of x_gen/y_gen).
  -- D(slope): Den² • D(slope) = Den • (D Y₁ - D Y₂) - (Y₁ - Y₂) • (D X₁ - D X₂).
  have h_Dslope : (X₁ - X₂) ^ 2 • D (addSlopePair α₁ α₂) =
      (X₁ - X₂) • (D Y₁ - D Y₂) - (Y₁ - Y₂) • (D X₁ - D X₂) := by
    rw [h_slope, D.leibniz_div (Y₁ - Y₂) (X₁ - X₂), map_sub, map_sub, smul_smul,
      show (X₁ - X₂) ^ 2 * (X₁ - X₂)⁻¹ ^ 2 = 1 from by
        rw [← mul_pow, mul_inv_cancel₀ hDen_ne, one_pow], one_smul]
  -- D(addPullback_x_pair) = (2·slope + a₁)•D(slope) - D X₁ - D X₂  (Leibniz on addX).
  have h_Dx : D (addPullback_x_pair α₁ α₂) =
      (2 * addSlopePair α₁ α₂ + algebraMap K KE W.a₁) • D (addSlopePair α₁ α₂) - D X₁ - D X₂ := by
    unfold addPullback_x_pair WeierstrassCurve.Affine.addX
    set ℓ := addSlopePair α₁ α₂ with hℓ
    change D ((ℓ) ^ 2 + (W_KE W).toAffine.a₁ * ℓ
            - (W_KE W).toAffine.a₂ - X₁ - X₂) = _
    rw [show (W_KE W).toAffine.a₁ = algebraMap K KE W.a₁ from rfl,
      show (W_KE W).toAffine.a₂ = algebraMap K KE W.a₂ from rfl]
    rw [map_sub, map_sub, map_sub, map_add, D.leibniz (algebraMap K KE W.a₁) ℓ,
      D.leibniz_pow ℓ 2, D.map_algebraMap W.a₁, D.map_algebraMap W.a₂]
    simp only [smul_zero, add_zero, sub_zero]
    change (2 : ℕ) • ℓ ^ (2 - 1) • D ℓ + (algebraMap K KE) W.a₁ • D ℓ - D X₁ - D X₂ =
      (2 * ℓ + (algebraMap K KE) W.a₁) • D ℓ - D X₁ - D X₂
    rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, add_smul,
      show (2 : ℕ) • (ℓ • D ℓ) = ((2 : KE)) • (ℓ • D ℓ) from
        (Nat.cast_smul_eq_nsmul (R := KE) 2 _).symm, smul_smul]
  -- Cleared form: Den² • D(addPullback_x_pair).
  have hcleared : (X₁ - X₂) ^ 2 • D (addPullback_x_pair α₁ α₂) =
      (2 * addSlopePair α₁ α₂ + algebraMap K KE W.a₁) •
        ((X₁ - X₂) • (D Y₁ - D Y₂)) -
      (2 * addSlopePair α₁ α₂ + algebraMap K KE W.a₁) •
        ((Y₁ - Y₂) • (D X₁ - D X₂)) -
      (X₁ - X₂) ^ 2 • D X₁ - (X₁ - X₂) ^ 2 • D X₂ := by
    rw [h_Dx, smul_sub, smul_sub, smul_smul,
      mul_comm ((X₁ - X₂) ^ 2) (2 * addSlopePair α₁ α₂ + algebraMap K KE W.a₁),
      ← smul_smul, h_Dslope, smul_sub]
  rw [show D X₁ = (alpha_star_u W α₁ * omegaPullbackCoeff W α₁) •
        invariantDifferential W.toAffine from kaehler_D_alpha_pullback_x_eq_smul_omega W α₁,
      show D Y₁ = ((3 * X₁ ^ 2 + 2 * algebraMap K KE W.a₂ * X₁ + algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * Y₁) * omegaPullbackCoeff W α₁) •
            invariantDifferential W.toAffine from kaehler_D_alpha_pullback_y_eq_smul_omega W α₁,
      show D X₂ = (alpha_star_u W α₂ * omegaPullbackCoeff W α₂) •
        invariantDifferential W.toAffine from kaehler_D_alpha_pullback_x_eq_smul_omega W α₂,
      show D Y₂ = ((3 * X₂ ^ 2 + 2 * algebraMap K KE W.a₂ * X₂ + algebraMap K KE W.a₄ -
          algebraMap K KE W.a₁ * Y₂) * omegaPullbackCoeff W α₂) •
            invariantDifferential W.toAffine from kaehler_D_alpha_pullback_y_eq_smul_omega W α₂]
    at hcleared
  refine smul_right_injective _ hDen2_ne (?_ :
    (X₁ - X₂) ^ 2 • _ = (X₁ - X₂) ^ 2 • _)
  rw [hcleared]
  simp only [smul_smul, ← sub_smul]
  congr 1
  rw [addPullback_y_pair, addPullback_x_pair, h_slope]
  rw [show alpha_star_u W α₁ = 2 * Y₁ + algebraMap K KE W.a₁ * X₁ + algebraMap K KE W.a₃ from rfl,
    show alpha_star_u W α₂ = 2 * Y₂ + algebraMap K KE W.a₁ * X₂ + algebraMap K KE W.a₃ from rfl]
  have hα₁ := pullback_equation W α₁
  rw [WeierstrassCurve.Affine.equation_iff] at hα₁
  have hα₂ := pullback_equation W α₂
  rw [WeierstrassCurve.Affine.equation_iff] at hα₂
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY,
    W_KE, WeierstrassCurve.toAffine, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hα₁ hα₂ ⊢
  field_simp [hDen_ne]
  -- The cleared scalar identity is the `(α₁,α₂)`-combination of the two pullback Weierstrass
  -- equations (the `id ⊞ α` collapse); discharged by the free-variable algebra core.
  exact kaehler_D_addPullback_x_pair_ring_identity X₁ X₂ Y₁ Y₂ (algebraMap K KE W.a₁)
    (omegaPullbackCoeff W α₁) (omegaPullbackCoeff W α₂) (algebraMap K KE W.a₂)
    (algebraMap K KE W.a₃) (algebraMap K KE W.a₄) (algebraMap K KE W.a₆) hα₁ hα₂

end HasseWeil
