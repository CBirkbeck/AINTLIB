import HasseWeil.AdditionPullback
import HasseWeil.OmegaPullbackCoeff
import HasseWeil.EC.GenericPointZsmul

/-!
# The `[m] ⊞ [1] = [m+1]` addition recurrence on the generic point (Silverman III.5.3)

`addPullback_x/y W (mulByInt m)` (the chord-addition of the generic point `P` and `[m]P`) equals the
`[m+1]`-coordinates `mulByInt_x/y W (m+1)`. This is `P ⊞ [m]P = [m+1]P` read off on the function
field, derived from `zsmul_genericPoint_eq` (`n • genericPoint = (mulByInt_x n, mulByInt_y n)`) and
the affine chord formula.

This lives in its own minimal-import module to avoid an `AddCommGroup` instance diamond on
`(W_KE W).toAffine.Point` that appears when the heavier `SilvermanIV14` / `OpenLemmaPrimitives`
modules are in scope (there the canonical `zsmul` lemmas fail to fire on `m • genericPoint`).
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
  (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField
local notation "R" => W.toAffine.CoordinateRing

set_option maxHeartbeats 1000000 in
/-- **RB-ID core** (Silverman III.5.3 addition recurrence): the addition-pullback of the generic
point against `[m]` equals the `[m+1]`-coordinates. -/
theorem addPullback_xy_mulByInt_eq_succ (m : ℤ) (hm : m ≠ 0) (hm1 : m + 1 ≠ 0)
    (hx_ne : x_gen W ≠ mulByInt_x W m) :
    addPullback_x W (mulByInt W.toAffine m) = mulByInt_x W (m + 1) ∧
      addPullback_y W (mulByInt W.toAffine m) = mulByInt_y W (m + 1) := by
  -- The chord-addition coordinate identities `P ⊞ [m]P = [m+1]P` are discharged as `addX`/`addY`
  -- field equalities in `GenericPointZsmul` (`addX_addY_genericPoint_mulByInt_eq_succ`), where the
  -- `(W_KE W).toAffine.Point` group-law instances are canonical. Here (with `AdditionPullback`'s
  -- heavier imports in scope) those point-group instances diamond, so we keep everything on the
  -- `K(E)`-field side: unfold `addPullback_x/y`/`addSlope` and fold the `[m]`-pullbacks to
  -- `mulByInt_x/y m`, matching the helper's conclusion verbatim.
  have hpmx : (mulByInt W.toAffine m).pullback (x_gen W) = mulByInt_x W m :=
    mulByInt_pullback_x W m hm
  have hpmy : (mulByInt W.toAffine m).pullback (y_gen W) = mulByInt_y W m :=
    mulByInt_pullback_y W m hm
  unfold addPullback_x addPullback_y addSlope
  rw [hpmx, hpmy]
  -- Expand the secant slope (`x_gen ≠ mulByInt_x m`). This removes the `slope` function — and with
  -- it the `DecidableEq K(E)` instance whose two competing values (`instDecidableEqFunctionField`
  -- here vs mathlib's `FractionRing.instDecidableEq` in the helper) would otherwise force an
  -- explosive `whnf` defeq over the `FunctionField` tower. The resulting goal is built only from
  -- instance-stable `K(E)` field operations and matches the helper's conclusion verbatim.
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx_ne]
  exact addX_addY_genericPoint_mulByInt_eq_succ W m hm hm1 hx_ne

/-- **Non-inverseness of the `([m], [1])` pair**: for `m ≠ 0`, `m + 1 ≠ 0`, the generic-point
images of `[m]` and `[1]` are not mutual inverses. Chord case (`m ≠ 1`) by the
division-polynomial `x`-distinctness (`mulByInt_x_ne_mulByInt_x`, lawful since `m ≠ ±1`);
tangent case (`m = 1`) by the 2-torsion-freeness of the generic point
(`mulByInt_y_one_ne_negY`). -/
theorem addNonInversePair_mulByInt_one (m : ℤ) (hm : m ≠ 0) (hm1 : m + 1 ≠ 0) :
    AddNonInversePair (mulByInt W.toAffine m) (mulByInt W.toAffine 1) := by
  have hpmx : (mulByInt W.toAffine m).pullback (x_gen W) = mulByInt_x W m :=
    mulByInt_pullback_x W m hm
  have hpmy : (mulByInt W.toAffine m).pullback (y_gen W) = mulByInt_y W m :=
    mulByInt_pullback_y W m hm
  have hp1x : (mulByInt W.toAffine 1).pullback (x_gen W) = mulByInt_x W 1 :=
    mulByInt_pullback_x W 1 one_ne_zero
  have hp1y : (mulByInt W.toAffine 1).pullback (y_gen W) = mulByInt_y W 1 :=
    mulByInt_pullback_y W 1 one_ne_zero
  rcases eq_or_ne m 1 with rfl | hm_ne_one
  · apply AddNonInversePair_of_y_ne
    rw [hpmy, hp1x]
    exact mulByInt_y_one_ne_negY W
  · apply AddNonInversePair_of_x_ne
    rw [hpmx, hp1x]
    exact mulByInt_x_ne_mulByInt_x W m 1 hm one_ne_zero hm_ne_one
      (fun h => hm1 (by omega))

set_option maxHeartbeats 1000000 in
/-- **Pair-order RB-ID** (`[m] ⊞ [1] = [m+1]`, Silverman III.5.3): the pair
addition-pullback of `([m], [1])` realises the `[m+1]`-coordinates. Pair-order mirror of
`addPullback_xy_mulByInt_eq_succ` (which is the `(id, [m])` order), additionally covering
the tangent branch `m = 1` (via the explicit-slope doubling identities
`addX_addY_mulByInt_one_self_eq_two`). Consumed by the BRIDGE-003 instance
`formalIsogenySeries_FGL_additivity` (`GapQfKernel`). -/
theorem addPullback_xy_pair_mulByInt_one_eq_succ (m : ℤ) (hm : m ≠ 0) (hm1 : m + 1 ≠ 0) :
    addPullback_x_pair (mulByInt W.toAffine m) (mulByInt W.toAffine 1)
        = mulByInt_x W (m + 1) ∧
      addPullback_y_pair (mulByInt W.toAffine m) (mulByInt W.toAffine 1)
        = mulByInt_y W (m + 1) := by
  have hpmx : (mulByInt W.toAffine m).pullback (x_gen W) = mulByInt_x W m :=
    mulByInt_pullback_x W m hm
  have hpmy : (mulByInt W.toAffine m).pullback (y_gen W) = mulByInt_y W m :=
    mulByInt_pullback_y W m hm
  rcases eq_or_ne m 1 with rfl | hm_ne_one
  · -- Tangent branch: `[1] ⊞ [1] = [2]`.
    unfold addPullback_x_pair addPullback_y_pair addSlopePair
    rw [hpmx, hpmy,
      WeierstrassCurve.Affine.slope_of_Y_ne rfl (mulByInt_y_one_ne_negY W)]
    exact addX_addY_mulByInt_one_self_eq_two W
  · -- Chord branch: `m ∉ {0, ±1}` (`m = -1` is excluded by `hm1`).
    have hx_ne : mulByInt_x W m ≠ mulByInt_x W 1 :=
      mulByInt_x_ne_mulByInt_x W m 1 hm one_ne_zero hm_ne_one
        (fun h => hm1 (by omega))
    have hp1x : (mulByInt W.toAffine 1).pullback (x_gen W) = mulByInt_x W 1 :=
      mulByInt_pullback_x W 1 one_ne_zero
    have hp1y : (mulByInt W.toAffine 1).pullback (y_gen W) = mulByInt_y W 1 :=
      mulByInt_pullback_y W 1 one_ne_zero
    have hx_ne' : mulByInt_x W m ≠ x_gen W := by
      rw [← mulByInt_x_one W]
      exact hx_ne
    unfold addPullback_x_pair addPullback_y_pair addSlopePair
    rw [hpmx, hpmy, hp1x, hp1y, WeierstrassCurve.Affine.slope_of_X_ne hx_ne,
      mulByInt_x_one, mulByInt_y_one]
    exact addX_addY_mulByInt_genericPoint_eq_succ W m hm hm1 hx_ne'

/-- **Wall C (isogeny form), Silverman III.4.2b**: `[·] : ℤ → End E` is injective on the nonzero
integers. If `mulByInt a = mulByInt b` as isogenies (`a, b ≠ 0`), then `a = b`. Via the pullback
acting on the generators (`mulByInt_pullback_x/y`) reduced to `mulByInt_xy_inj` (the generic point
has infinite order). EXACT injectivity — no `±` ambiguity — so it soundly extracts `deg β = N` from
an endomorphism identity `[deg β] = [N]` (the III.6.3 degree-quadratic-form sign resolution). -/
theorem mulByInt_left_injective (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : mulByInt W.toAffine a = mulByInt W.toAffine b) : a = b := by
  have hpb : (mulByInt W.toAffine a).pullback = (mulByInt W.toAffine b).pullback :=
    congrArg Isogeny.pullback hab
  have hx : mulByInt_x W a = mulByInt_x W b := by
    rw [← mulByInt_pullback_x W a ha, ← mulByInt_pullback_x W b hb, hpb]
  have hy : mulByInt_y W a = mulByInt_y W b := by
    rw [← mulByInt_pullback_y W a ha, ← mulByInt_pullback_y W b hb, hpb]
  exact mulByInt_xy_inj W a b ha hb hx hy

end HasseWeil
