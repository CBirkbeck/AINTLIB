/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.OrdAtInftyBaseChange
import HasseWeil.WeilPairing.OneSubAffineResidues
import HasseWeil.WeilPairing.ProjOrdTransportLocal
import HasseWeil.WeilPairing.WallAGeometricRealization

/-!
# The infinity residues of the concrete `(1 − π)_{K̄}` (CoordHom-free)

This file builds the **two non-affine fields** of `ComapPointValuationWitness W (1 − π)`
(`ProjOrdTransportLocal.lean`) for the genuine base-changed `1 − π` over `K̄`:

* `infinity` = `InftyOrdTransport (1 − π)`: `ord_∞((1 − π)^* h) = ord_∞ h` for all `h` (as
  `(1 − π)(O) = O`), and
* `affineToInfty`: for an affine smooth point `P` with `(1 − π)(P) = O` (a kernel point),
  `(pointValuation P).comap (1 − π)^* = ordAtInftyValuation`.

Both rest on the **same** two infinity-order values
```
  ord_∞((1 − π)^* x_gen) = -2,    ord_∞((1 − π)^* y_gen) = -3,
```
exactly as the proven `[ℓ]` infinity case (`DivisorPullback.lean`,
`inftyOrdTransport_mulByInt` / `comap_pointValuation_mulByInt_eq_infty`) rests on
`ord_∞(mulByInt_x ℓ) = -2`, `ord_∞(mulByInt_y ℓ) = -3`.

## The shared infinity-order linchpin and its reduction

Over `K̄` the pullback of `(1 − π)` on the generators is the **function-field base change** of the
explicit `K`-level addition-formula pullback (Wall A, `oneSubFrobeniusPullback_L_x_gen` /
`_y_gen`):
```
  (1 − π)^* x_gen^{K̄} = functionFieldMap ((1 − π)^K^* x_gen^K),
  (1 − π)^* y_gen^{K̄} = functionFieldMap ((1 − π)^K^* y_gen^K).
```
The `K`-level orders `ord_∞^K((1 − π)^K^* x_gen) = -2`, `ord_∞^K((1 − π)^K^* y_gen) = -3` are
*proved* (`AdditionPullback/SilvermanIV14.lean` + `AdditionPullback/Frobenius.lean`:
`addPullbackAlgHom_negFrobenius_?_gen_eq` ∘ `ord_addPullback_?_negFrobenius`).  Hence the two `K̄`
orders reduce to the single **base-change order-transport at the place at infinity**
```
  ord_∞^{K̄}(functionFieldMap z) = ord_∞^K z      (`OrdAtInftyBaseChange`)
```
— the statement that the rational point `O` stays rational with ramification index `e = 1` under
`K → K̄`.  This is the infinity twin of the affine `pointValuation` base-change.  It is now
**DISCHARGED** (`ordAtInftyBaseChange_holds`) via the general curve transport
`HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_functionFieldMap` (`Curves/OrdAtInftyBaseChange.lean`):
`ord_∞(f) = -intDegree (N(f))`, the algebra norm transports under base change by the explicit
coordinate-ring norm formula `norm_smul_basis` (a polynomial identity commuting with `K[X] → L[X]`)
and `natDegree`-preservation under the injective `K → L`.  Every declaration of this file is then
axiom-clean `[propext, Classical.choice, Quot.sound]`, with **no carried `OrdAtInftyBaseChange`**.

## What this file proves (modulo the one carried `Prop`)

* `ordAtInfty_oneSub_pullback_x_gen` / `_y_gen` — the two `K̄` infinity orders `-2`, `-3`, from the
  Wall A base-change realisation + the `K`-level orders + the carried order-transport `Prop`.
* `inftyOrdTransport_of_ordAtInfty_x_y` — **field-general**: `InftyOrdTransport φ` from the two
  infinity orders `ord_∞(φ^* x_gen) = -2`, `ord_∞(φ^* y_gen) = -3` (the verbatim generalisation of
  `inftyOrdTransport_mulByInt`'s pinning via `eq_ordAtInftyValuation_of_x_y`).
* `inftyOrdTransport_oneSub` — the **`infinity` field** for `(1 − π)_{K̄}`.
* `oneSub_hcov_kernel` — the kernel-translation invariance `τ_k((1 − π)^* z) = (1 − π)^* z`
  (`k ∈ ker(1 − π)`), from the Wall A generic-point covariance
  `mapTranslateGenericPoint_oneSub_canonical` via `hcov_of_mapTranslateGenericPoint_canonical`.
* `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant` — **field-general**: the
  infinity comap identity from the two infinity orders + kernel-invariance (the verbatim
  generalisation of `comap_pointValuation_mulByInt_eq_infty`'s translation-invariance trick).
* `comap_pointValuation_oneSub_eq_infty` — the **`affineToInfty` field** for `(1 − π)_{K̄}`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, I.2 (base change), III.4 (Frobenius),
III.4.10c, IV.1 (`ord_∞(x) = -2`, `ord_∞(y) = -3`).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

open HasseWeil IsogenyBaseChangeConcrete

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
variable (p r : ℕ) [Fact p.Prime] [CharP K p] [Fact (Fintype.card K = p ^ r)]

noncomputable local instance instDecEqACOSIR : DecidableEq (AlgebraicClosure K) := Classical.decEq _

variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]

/-- **`ord_∞^K((1 − π)^K^* x_gen) = -2`** (the `K`-level pole at `O`, Silverman IV.1).  Composition of
`isogOneSub_negFrobenius_pullback`, `addPullbackAlgHom_negFrobenius_x_gen_eq`
(`(1 − π)^K^* x_gen = addPullback_x (−π)`), and `ord_addPullback_x_negFrobenius`. -/
theorem ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty ((HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.x_gen W)) =
      ((-2 : ℤ) : WithTop ℤ) := by
  rw [HasseWeil.isogOneSub_negFrobenius_pullback, HasseWeil.addPullbackAlgHom_negFrobenius_x_gen_eq W hq]
  exact HasseWeil.ord_addPullback_x_negFrobenius W hq

/-- **`ord_∞^K((1 − π)^K^* y_gen) = -3`** (the `K`-level pole at `O`, Silverman IV.1).  The
`y`-analogue of `ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K`, via
`ord_addPullback_y_negFrobenius`. -/
theorem ordAtInfty_isogOneSub_negFrobenius_pullback_y_gen_K (hq : 2 ≤ Fintype.card K) :
    (W_smooth W).ordAtInfty ((HasseWeil.isogOneSub_negFrobenius W hq).pullback (HasseWeil.y_gen W)) =
      ((-3 : ℤ) : WithTop ℤ) := by
  rw [HasseWeil.isogOneSub_negFrobenius_pullback, HasseWeil.addPullbackAlgHom_negFrobenius_y_gen_eq W hq]
  exact HasseWeil.ord_addPullback_y_negFrobenius W hq

/-- **Base-change order-transport at infinity, as a `Prop`** (Silverman I.2 + IV.1): for nonzero
`z ∈ K(E)`, `ord_∞^{K̄}(functionFieldMap z) = ord_∞^K z` (the order at the `K`-rational, unramified
`e = 1` point `O` is unchanged under `K → L`).  DISCHARGED by `ordAtInftyBaseChange_holds`; the
infinity analogue of the affine `pointValuation`
base-change naturality the affine third carries. -/
def OrdAtInftyBaseChange (L : Type*) [Field L] [Algebra K L]
    [(W.baseChange L).toAffine.IsElliptic] : Prop :=
  ∀ z : W.toAffine.FunctionField, z ≠ 0 →
    (W_smooth (W.baseChange L)).ordAtInfty
        ((⟨W.toAffine⟩ : SmoothPlaneCurve K).functionFieldMap L z) =
      (W_smooth W).ordAtInfty z

/-- **`OrdAtInftyBaseChange` is DISCHARGED** (no longer carried).  The order at infinity transports
under the function-field base change because `ord_∞(f) = -intDegree (N(f))` and the norm/degree
base-change is the explicit coordinate-ring norm formula (`norm_smul_basis`, a polynomial identity
commuting with `K[X] → L[X]`) plus `natDegree`-preservation under the injective `K → L`
(`HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_functionFieldMap`).  `W_smooth C = ⟨C.toAffine⟩`, so
this is the named leaf at the general curve transport. -/
theorem ordAtInftyBaseChange_holds (L : Type*) [Field L] [Algebra K L]
    [(W.baseChange L).toAffine.IsElliptic] : OrdAtInftyBaseChange W L :=
  fun z hz => HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_functionFieldMap
    (⟨W.toAffine⟩ : SmoothPlaneCurve K) L z hz

/-- **`ord_∞^{K̄}((1 − π)_{K̄}^* x_gen) = -2`** — the pole of order `2` at `O` over `K̄`.  Chains the
Wall A base-change realisation `oneSubFrobeniusPullback_L_x_gen`
(`(1 − π)_{K̄}^* x_gen = functionFieldMap((1 − π)^K^* x_gen)`), the *discharged* order-transport
`ordAtInftyBaseChange_holds`, and the `K`-level order
`ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K`. -/
theorem ordAtInfty_oneSub_pullback_x_gen (hq : 2 ≤ Fintype.card K) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.x_gen (W.baseChange (AlgebraicClosure K)))) =
      ((-2 : ℤ) : WithTop ℤ) := by
  have hbc := ordAtInftyBaseChange_holds W (AlgebraicClosure K)
  rw [oneSubFrobeniusIsogBaseChange_pullback,
    IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_x_gen W (AlgebraicClosure K) hq,
    hbc _
      (fun h0 => by
        have hcoe := ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K W hq
        rw [(((W_smooth W).ordAtInfty_eq_top_iff _).mpr h0)] at hcoe
        exact WithTop.top_ne_coe hcoe),
    ordAtInfty_isogOneSub_negFrobenius_pullback_x_gen_K W hq]

/-- **`ord_∞^{K̄}((1 − π)_{K̄}^* y_gen) = -3`** — the pole of order `3` at `O` over `K̄`.  The
`y`-analogue of `ordAtInfty_oneSub_pullback_x_gen`. -/
theorem ordAtInfty_oneSub_pullback_y_gen
    (hq : 2 ≤ Fintype.card K) :
    (W_smooth (W.baseChange (AlgebraicClosure K))).ordAtInfty
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
            (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback
            (HasseWeil.y_gen (W.baseChange (AlgebraicClosure K)))) =
      ((-3 : ℤ) : WithTop ℤ) := by
  have hbc := ordAtInftyBaseChange_holds W (AlgebraicClosure K)
  rw [oneSubFrobeniusIsogBaseChange_pullback,
    IsogenyBaseChangeConcrete.oneSubFrobeniusPullback_L_y_gen W (AlgebraicClosure K) hq,
    hbc _
      (fun h0 => by
        have hcoe := ordAtInfty_isogOneSub_negFrobenius_pullback_y_gen_K W hq
        rw [(((W_smooth W).ordAtInfty_eq_top_iff _).mpr h0)] at hcoe
        exact WithTop.top_ne_coe hcoe),
    ordAtInfty_isogOneSub_negFrobenius_pullback_y_gen_K W hq]

section FieldGeneral

variable {F : Type*} [Field F] [DecidableEq F]

/-- **`InftyOrdTransport φ` from the two infinity orders** (field-general).  For any isogeny `φ` of an
elliptic curve `E / F` with `ord_∞(φ^* x_gen) = -2` and `ord_∞(φ^* y_gen) = -3`, the order-transport
at infinity `ord_∞(φ^* h) = ord_∞ h` holds.  Verbatim generalisation of `inftyOrdTransport_mulByInt`:
the comap `w = ordAtInftyValuation ∘ φ^*` sends `x_gen ↦ exp 2`, `y_gen ↦ exp 3`, fixes `F^×`, so
`w = ordAtInftyValuation` by the master pinning `eq_ordAtInftyValuation_of_x_y`; reading off `ord_∞`
gives the transport. -/
theorem inftyOrdTransport_of_ordAtInfty_x_y (W' : WeierstrassCurve F) [W'.toAffine.IsElliptic]
    (φ : Isogeny W'.toAffine W'.toAffine)
    (hx : (W_smooth W').ordAtInfty (φ.pullback (HasseWeil.x_gen W')) = ((-2 : ℤ) : WithTop ℤ))
    (hy : (W_smooth W').ordAtInfty (φ.pullback (HasseWeil.y_gen W')) = ((-3 : ℤ) : WithTop ℤ)) :
    DivisorPullback.InftyOrdTransport φ := by
  set τ := φ.pullback
  set w := ((W_smooth W').ordAtInftyValuation).comap τ.toRingHom
  have hw_apply : ∀ g, w g = (W_smooth W').ordAtInftyValuation (τ g) := fun g =>
    Valuation.comap_apply _ _ _
  have hwx : w (HasseWeil.x_gen W') = WithZero.exp 2 := by
    have hx_ne : φ.pullback (HasseWeil.x_gen W') ≠ 0 := fun h0 => by
      rw [(((W_smooth W').ordAtInfty_eq_top_iff _).mpr h0)] at hx; exact WithTop.top_ne_coe hx
    rw [hw_apply,
      (W_smooth W').ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hx_ne hx]
    norm_num
  have hwy : w (HasseWeil.y_gen W') = WithZero.exp 3 := by
    have hy_ne : φ.pullback (HasseWeil.y_gen W') ≠ 0 := fun h0 => by
      rw [(((W_smooth W').ordAtInfty_eq_top_iff _).mpr h0)] at hy; exact WithTop.top_ne_coe hy
    rw [hw_apply,
      (W_smooth W').ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hy_ne hy]
    norm_num
  have hwc : ∀ c : F, c ≠ 0 → w (algebraMap F W'.toAffine.FunctionField c) = 1 := fun c hc => by
    rw [hw_apply, show τ (algebraMap F W'.toAffine.FunctionField c) =
        algebraMap F W'.toAffine.FunctionField c from τ.commutes c]
    have h_ne : algebraMap F W'.toAffine.FunctionField c ≠ 0 :=
      fun h => hc (FaithfulSMul.algebraMap_injective F _ (h.trans (map_zero _).symm))
    have h_ord : (W_smooth W').ordAtInfty (algebraMap F W'.toAffine.FunctionField c) =
        ((0 : ℤ) : WithTop ℤ) := by
      rw [HasseWeil.ordAtInfty_algebraMap_F_nonzero W' hc]; rfl
    rw [(W_smooth W').ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq h_ne h_ord]
    norm_num
  have hval : w = (W_smooth W').ordAtInftyValuation :=
    HasseWeil.eq_ordAtInftyValuation_of_x_y W' w hwx hwy hwc
  intro h
  rcases eq_or_ne h 0 with rfl | hh
  · rw [map_zero]
  · have hτh_ne : τ h ≠ 0 := fun h0 => hh (τ.injective (h0.trans (map_zero τ).symm))
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (W_smooth W').ordAtInfty (τ h) = (m : WithTop ℤ) :=
      ⟨_, (W_smooth W').ordAtInfty_of_ne hτh_ne⟩
    obtain ⟨n, hn⟩ : ∃ n : ℤ, (W_smooth W').ordAtInfty h = (n : WithTop ℤ) :=
      ⟨_, (W_smooth W').ordAtInfty_of_ne hh⟩
    have hval_at : (W_smooth W').ordAtInftyValuation (τ h) =
        (W_smooth W').ordAtInftyValuation h := by
      have hwh := congrFun (congrArg DFunLike.coe hval) h
      rw [hw_apply] at hwh
      exact hwh
    rw [(W_smooth W').ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hτh_ne hm,
      (W_smooth W').ordAtInftyValuation_eq_exp_neg_of_ordAtInfty_eq hh hn,
      WithZero.exp_inj] at hval_at
    change ((W_smooth W').ordAtInfty (τ h)).untopD 0 = ((W_smooth W').ordAtInfty h).untopD 0
    rw [hm, hn, WithTop.untopD_coe, WithTop.untopD_coe]
    lia

/-- `-Q ∈ ker φ` when `φ(Q) = O` (`φ(-Q) = -φ(Q) = -O = O`). -/
theorem neg_mem_kernel_of_image_zero (W' : WeierstrassCurve F) [W'.toAffine.IsElliptic]
    (φ : Isogeny W'.toAffine W'.toAffine) (Q : W'.toAffine.Point)
    (hQ : φ.toAddMonoidHom Q = (0 : W'.toAffine.Point)) :
    (-Q : W'.toAffine.Point) ∈ φ.kernel := by
  rw [HasseWeil.Isogeny.mem_kernel_iff, map_neg, hQ, neg_zero]

/-- **The infinity comap identity from the two infinity orders + kernel-invariance** (field-general).
For any isogeny `φ` of an elliptic curve and a smooth point `P` with `φ(P) = O`,
`(pointValuation P).comap φ^* = ordAtInftyValuation`, provided
* `ord_∞(φ^* x_gen) = -2`, `ord_∞(φ^* y_gen) = -3` (the two infinity orders), and
* `hcov`: for every `k ∈ ker φ`, `τ_k(φ^* z) = φ^* z` (kernel-translation invariance).

Verbatim generalisation of `comap_pointValuation_mulByInt_eq_infty`: `k = -P ∈ ker φ`, the
pullback generators are `τ_k`-invariant, so `ord_P(φ^* x_gen) = ord_∞(φ^* x_gen) = -2` (likewise
`y`, `-3`) by the field-general translation transport, and the comap valuation sends
`x_gen ↦ exp 2`, `y_gen ↦ exp 3`, fixes `F^×`, hence equals `ordAtInftyValuation` by
`eq_ordAtInftyValuation_of_x_y`. -/
theorem comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant
    (W' : WeierstrassCurve F) [W'.toAffine.IsElliptic]
    (φ : Isogeny W'.toAffine W'.toAffine)
    (hx : (W_smooth W').ordAtInfty (φ.pullback (HasseWeil.x_gen W')) = ((-2 : ℤ) : WithTop ℤ))
    (hy : (W_smooth W').ordAtInfty (φ.pullback (HasseWeil.y_gen W')) = ((-3 : ℤ) : WithTop ℤ))
    (hcov : ∀ (k : φ.kernel) (z : W'.toAffine.FunctionField),
      HasseWeil.translateAlgEquivOfPoint W' k.val (φ.pullback z) = φ.pullback z)
    (P : (W_smooth W').SmoothPoint)
    (hQ : φ.toAddMonoidHom (Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P) =
      (0 : W'.toAffine.Point)) :
    ((W_smooth W').pointValuation P).comap φ.pullback.toRingHom =
      (W_smooth W').ordAtInftyValuation := by
  set k : (W_smooth W').toAffine.Point :=
    -(Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P) with hk
  have hk_mem : k ∈ φ.kernel := neg_mem_kernel_of_image_zero W' φ _ hQ
  have h_zero : Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P + k = Affine.Point.zero := by
    rw [hk]; exact add_neg_cancel _
  have h_compat := HasseWeil.isTranslateOrdAtInftyCompatible_translateAlgEquivOfPoint W' P k h_zero
  have h_ordx : (W_smooth W').ord_P P (φ.pullback (HasseWeil.x_gen W')) = ((-2 : ℤ) : WithTop ℤ) :=
    (HasseWeil.ord_P_eq_ordAtInfty_of_invariant_and_compatible W' P k h_zero h_compat
      (φ.pullback (HasseWeil.x_gen W')) (hcov ⟨k, hk_mem⟩ (HasseWeil.x_gen W'))).trans hx
  have h_ordy : (W_smooth W').ord_P P (φ.pullback (HasseWeil.y_gen W')) = ((-3 : ℤ) : WithTop ℤ) :=
    (HasseWeil.ord_P_eq_ordAtInfty_of_invariant_and_compatible W' P k h_zero h_compat
      (φ.pullback (HasseWeil.y_gen W')) (hcov ⟨k, hk_mem⟩ (HasseWeil.y_gen W'))).trans hy
  set w := ((W_smooth W').pointValuation P).comap φ.pullback.toRingHom
  have hw_apply : ∀ g, w g = (W_smooth W').pointValuation P (φ.pullback g) := fun g =>
    Valuation.comap_apply _ _ _
  have hwx : w (HasseWeil.x_gen W') = WithZero.exp 2 := by
    have hx_ne : φ.pullback (HasseWeil.x_gen W') ≠ 0 := fun h0 => by
      rw [(((W_smooth W').ordAtInfty_eq_top_iff _).mpr h0)] at hx; exact WithTop.top_ne_coe hx
    rw [hw_apply,
      HasseWeil.pointValuation_eq_exp_neg_of_ord_P_eq (C := W_smooth W') (P := P) hx_ne h_ordx]
    norm_num
  have hwy : w (HasseWeil.y_gen W') = WithZero.exp 3 := by
    have hy_ne : φ.pullback (HasseWeil.y_gen W') ≠ 0 := fun h0 => by
      rw [(((W_smooth W').ordAtInfty_eq_top_iff _).mpr h0)] at hy; exact WithTop.top_ne_coe hy
    rw [hw_apply,
      HasseWeil.pointValuation_eq_exp_neg_of_ord_P_eq (C := W_smooth W') (P := P) hy_ne h_ordy]
    norm_num
  have hwc : ∀ c : F, c ≠ 0 → w (algebraMap F W'.toAffine.FunctionField c) = 1 := fun c hc => by
    rw [hw_apply, show φ.pullback (algebraMap F W'.toAffine.FunctionField c) =
        algebraMap F W'.toAffine.FunctionField c from φ.pullback.commutes c]
    exact HasseWeil.pointValuation_algebraMap_F_eq_one_of_ne_zero W' P hc
  exact HasseWeil.eq_ordAtInftyValuation_of_x_y W' w hwx hwy hwc

end FieldGeneral

/-- **`InftyOrdTransport (1 − π)_{K̄}`** — the `infinity` field (Silverman III.8, `φ(O) = O`).  The
field-general pinning `inftyOrdTransport_of_ordAtInfty_x_y` applied to the two `K̄` infinity orders
`ordAtInfty_oneSub_pullback_x_gen` (`= -2`), `ordAtInfty_oneSub_pullback_y_gen` (`= -3`).  This is the
`(1 − π)` analogue of the proven `inftyOrdTransport_mulByInt`. -/
theorem inftyOrdTransport_oneSub
    (hq : 2 ≤ Fintype.card K) :
    DivisorPullback.InftyOrdTransport
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)) :=
  inftyOrdTransport_of_ordAtInfty_x_y (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (ordAtInfty_oneSub_pullback_x_gen W p r hq) (ordAtInfty_oneSub_pullback_y_gen W p r hq)

/-- **Kernel-translation invariance for `(1 − π)_{K̄}`** (Silverman III.4.10c): for `k ∈ ker(1 − π)`,
the function-field translation `τ_k` fixes the pullback range: `τ_k((1 − π)^* z) = (1 − π)^* z`.

This is the `(1 − π)` analogue of `hxy_mulByInt` — the input of the translation-invariance trick.  It
is `hcov_of_mapTranslateGenericPoint_canonical` (the kernel specialisation `S = k`, `φ(k) = 0` ⟹
`τ_{φ k} = τ_0 = id`) fed the Wall A generic-point covariance
`mapTranslateGenericPoint_oneSub_canonical` (proved CoordHom-free). -/
theorem oneSub_hcov_kernel (hq : 2 ≤ Fintype.card K)
    (k : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).kernel)
    (z : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) k.val
        ((oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback z) =
      (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback z :=
  hcov_of_mapTranslateGenericPoint_canonical (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (mapTranslateGenericPoint_oneSub_canonical W p r hq) k z

/-- **The infinity comap identity for `(1 − π)_{K̄}`** — the `affineToInfty` field (Silverman
III.4.10c).  For an affine smooth point `P` of `E_{K̄}` whose image `(1 − π)(P) = O` (a kernel point),
`(pointValuation P).comap (1 − π)^* = ordAtInftyValuation`.

The field-general translation-invariance trick `comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant`
fed the two `K̄` infinity orders (`ordAtInfty_oneSub_pullback_x_gen` = `-2`,
`ordAtInfty_oneSub_pullback_y_gen` = `-3`) and the kernel-translation invariance `oneSub_hcov_kernel`.
This is the `(1 − π)` analogue of the proven `comap_pointValuation_mulByInt_eq_infty`. -/
theorem comap_pointValuation_oneSub_eq_infty
    (hq : 2 ≤ Fintype.card K)
    (P : (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
      SmoothPlaneCurve (AlgebraicClosure K)).SmoothPoint)
    (hQ : (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
        (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).toAddMonoidHom
        (Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint P) = (0 : (W.baseChange (AlgebraicClosure K)).toAffine.Point)) :
    ((⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).pointValuation P).comap
        (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
          (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq)).pullback.toRingHom =
      (⟨(W.baseChange (AlgebraicClosure K)).toAffine⟩ :
        SmoothPlaneCurve (AlgebraicClosure K)).ordAtInftyValuation :=
  comap_pointValuation_eq_infty_of_ordAtInfty_x_y_of_kernelInvariant
    (W.baseChange (AlgebraicClosure K))
    (oneSubFrobeniusIsogBaseChange W p r (AlgebraicClosure K)
      (oneSubFrobeniusPullback_L W (AlgebraicClosure K) hq))
    (ordAtInfty_oneSub_pullback_x_gen W p r hq) (ordAtInfty_oneSub_pullback_y_gen W p r hq)
    (oneSub_hcov_kernel W p r hq) P hQ

end HasseWeil.WeilPairing
