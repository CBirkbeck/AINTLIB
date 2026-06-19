import HasseWeil.MulByIntPullback
import HasseWeil.FormalGroup
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Local Expansion at the Identity O (Phase 1 of the Local Expansion Bridge)

We construct the **local expansion functor** `localExpand : K(E) → LaurentSeries F`,
which expands an element of the function field of an elliptic curve as a Laurent
series in the local parameter `t = -x/y` at the identity `O`.

This is the foundation of the bridge between the formal-power-series world (where
`pullbackCoeff_add` is already proved in `FormalGroupAssoc.lean`) and the
function-field-pullback world (where `omegaPullbackCoeff` lives).

## Strategy (Silverman IV.1)

The unique formal series `w(z) ∈ F[[z]]` with `w(z) = z³ + a₁ z w(z) + a₂ z² w(z)
+ a₃ w(z)² + a₄ z w(z)² + a₆ w(z)³` is constructed in `FormalGroup.lean` as
`formalW W`. From this we recover:

* `x(z) = z / w(z) = z⁻² · u(z)⁻¹` where `u(z) = w(z) / z³` is a unit power series
* `y(z) = -1 / w(z) = -z⁻³ · u(z)⁻¹`

These satisfy the Weierstrass equation `y² + a₁xy + a₃y - x³ - a₂x² - a₄x - a₆ = 0`
because `w(z)` satisfies its defining recurrence (this is exactly Silverman IV.1.1
multiplied through by `-w³`).

By the universal property of the function field, the substitution `(x_gen, y_gen) ↦
(formalX, formalY)` extends to a unique ring homomorphism `K(E) → LaurentSeries F`
(the target is a field, so any nonzero ring hom is injective and the substitution
extends from the coordinate ring through to the fraction field).

## Main definitions

* `formalU W : PowerSeries F` — the unit `w(z) / z³ = 1 + a₁z + ...`
* `formalY W : LaurentSeries F` — the Laurent series for `y` in terms of `t = -x/y`
* `formalX W : LaurentSeries F` — the Laurent series for `x` in terms of `t`
* `localParam W : K(E)` — the local parameter `t = -x_gen / y_gen`
* `localExpand W : K(E) →+* LaurentSeries F` — the expansion ring hom

## Status

This file establishes the API surface. The hard parts (Weierstrass equation
verification for `formalX, formalY`, and the construction of `localExpand` via the
universal property of the function field) are currently `sorry`-marked with
detailed comments. Phase 2 (`IsogenyLocalExpansion.lean`) builds on this API.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, IV.1 (pp. 115–119)
-/

open WeierstrassCurve PowerSeries LaurentSeries

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "R" => W.toAffine.CoordinateRing
local notation "KE" => W.toAffine.FunctionField

/-! ### The unit part `u(z) = w(z) / z³` -/

/-- The "unit part" of `formalW`: `u(z) = 1 + a₁z + (a₁² + a₂)z² + ...`.
    Constructed by shifting `formalW_coeff` down by 3 (since `formalW` has leading
    term `z³`). Has constant coefficient 1, hence is a unit in `F⟦X⟧`. -/
noncomputable def formalU : PowerSeries F :=
  PowerSeries.mk (fun n ↦ formalW_coeff W (n + 3))

/-- The constant coefficient of `formalU` is 1. -/
@[simp] theorem formalU_constantCoeff :
    @PowerSeries.constantCoeff F _ (formalU W) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, formalU, PowerSeries.coeff_mk,
      zero_add, formalW_coeff_three]

/-- `formalU W` is a unit in `F⟦X⟧`. -/
theorem formalU_isUnit : IsUnit (formalU W) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [formalU_constantCoeff]
  exact isUnit_one

/-- The (multiplicative) inverse of `formalU`: also a power series with constant
    coefficient 1, since `formalU` is a unit. -/
noncomputable def formalU_inv : PowerSeries F :=
  PowerSeries.invOfUnit (formalU W) 1

/-- `formalU * formalU_inv = 1` in `F⟦X⟧`. -/
@[simp] theorem formalU_mul_inv : formalU W * formalU_inv W = 1 :=
  PowerSeries.mul_invOfUnit (formalU W) 1
    (by rw [formalU_constantCoeff]; rfl)

/-- `formalU_inv * formalU = 1` in `F⟦X⟧`. -/
@[simp] theorem formalU_inv_mul : formalU_inv W * formalU W = 1 :=
  PowerSeries.invOfUnit_mul (formalU W) 1
    (by rw [formalU_constantCoeff]; rfl)

/-- The constant coefficient of `formalU_inv` is 1. -/
@[simp] theorem formalU_inv_constantCoeff :
    @PowerSeries.constantCoeff F _ (formalU_inv W) = 1 := by
  rw [formalU_inv, PowerSeries.constantCoeff_invOfUnit]
  rfl

/-! ### The Laurent series for `x` and `y`

Following Silverman IV.1, in the formal completion of `K(E)` at `O` with local
parameter `t = -x/y`:
* `x(t) = t⁻² · u(t)⁻¹` (leading order `t⁻²`)
* `y(t) = -t⁻³ · u(t)⁻¹` (leading order `-t⁻³`) -/

/-- The Laurent series `y(t) = -t⁻³ · u(t)⁻¹` representing the y-coordinate. -/
noncomputable def formalY : LaurentSeries F :=
  -(HahnSeries.single (-3 : ℤ) 1) *
    HahnSeries.ofPowerSeries ℤ F (formalU_inv W)

/-- The Laurent series `x(t) = t⁻² · u(t)⁻¹` representing the x-coordinate. -/
noncomputable def formalX : LaurentSeries F :=
  HahnSeries.single (-2 : ℤ) 1 *
    HahnSeries.ofPowerSeries ℤ F (formalU_inv W)

/-! ### Order computations for `formalX` and `formalY`

In `LaurentSeries F`, `formalX W` has order `-2` and `formalY W` has order `-3`.
These follow because `formalU_inv W` has order `0` (constant coeff = 1) and
`single (-2) 1` resp. `single (-3) 1` have orders `-2` resp. `-3`. -/

/-- `ofPowerSeries ℤ F (formalU_inv W)` is nonzero in `LaurentSeries F`. -/
theorem ofPowerSeries_formalU_inv_ne_zero :
    (HahnSeries.ofPowerSeries ℤ F (formalU_inv W) : LaurentSeries F) ≠ 0 := by
  intro h
  have h_nonzero : @HahnSeries.coeff ℤ F _ _
      (HahnSeries.ofPowerSeries ℤ F (formalU_inv W)) 0 = 1 := by
    have := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (formalU_inv W) 0
    simp only [Nat.cast_zero] at this
    rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact formalU_inv_constantCoeff W
  rw [h] at h_nonzero
  exact one_ne_zero h_nonzero.symm

/-- `formalX W ≠ 0`. -/
theorem formalX_ne_zero : formalX W ≠ 0 := by
  rw [formalX]
  exact mul_ne_zero (HahnSeries.single_ne_zero one_ne_zero)
    (ofPowerSeries_formalU_inv_ne_zero W)

/-- `formalY W ≠ 0`. -/
theorem formalY_ne_zero : formalY W ≠ 0 := by
  rw [formalY]
  refine mul_ne_zero ?_ (ofPowerSeries_formalU_inv_ne_zero W)
  rw [ne_eq, neg_eq_zero]
  exact HahnSeries.single_ne_zero one_ne_zero

/-- `ofPowerSeries ℤ F (formalU_inv W)` has `orderTop = 0`. This is because the
    series has constant coefficient 1, so its order is ≤ 0; and all coefficients
    at negative indices vanish (since `ofPowerSeries` embeds `ℕ ↪ ℤ`), so its order
    is ≥ 0. -/
theorem ofPowerSeries_formalU_inv_orderTop :
    (HahnSeries.ofPowerSeries ℤ F (formalU_inv W) : LaurentSeries F).orderTop = (0 : ℤ) := by
  set S : LaurentSeries F := HahnSeries.ofPowerSeries ℤ F (formalU_inv W) with hS
  have hS_ne : S ≠ 0 := ofPowerSeries_formalU_inv_ne_zero W
  have h0 : S.coeff (0 : ℤ) = 1 := by
    have := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (formalU_inv W) 0
    simp only [Nat.cast_zero] at this
    rw [hS, this, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact formalU_inv_constantCoeff W
  have h_le : S.orderTop ≤ (0 : ℤ) := by
    apply HahnSeries.orderTop_le_of_coeff_ne_zero
    rw [h0]; exact one_ne_zero
  have h_ge : (0 : ℤ) ≤ S.orderTop := by
    rw [HahnSeries.le_orderTop_iff_forall]
    intro n hn
    have : ((formalU_inv W : PowerSeries F) : LaurentSeries F).coeff n = 0 := by
      rw [PowerSeries.coeff_coe, if_pos]; exact_mod_cast hn
    exact this
  exact le_antisymm h_le h_ge

/-- `formalX W` has `orderTop = -2` in `LaurentSeries F`. -/
theorem formalX_orderTop :
    (formalX W).orderTop = ((-2 : ℤ) : WithTop ℤ) := by
  rw [formalX, HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero,
      ofPowerSeries_formalU_inv_orderTop]
  rfl

/-- `formalY W` has `orderTop = -3` in `LaurentSeries F`. -/
theorem formalY_orderTop :
    (formalY W).orderTop = ((-3 : ℤ) : WithTop ℤ) := by
  rw [formalY, HahnSeries.orderTop_mul]
  have hs : (-HahnSeries.single (-3 : ℤ) (1 : F)).orderTop = ((-3 : ℤ) : WithTop ℤ) := by
    rw [HahnSeries.orderTop_neg, HahnSeries.orderTop_single one_ne_zero]
  rw [hs, ofPowerSeries_formalU_inv_orderTop]
  rfl

/-! ### Leading coefficients of `formalX` and `formalY`

In `LaurentSeries F`, `formalX W` has leading coefficient `1` and `formalY W`
has leading coefficient `-1`. These come from expanding the definitions:
`formalX = single(-2,1) · (lifted u_inv)` with `(lifted u_inv).leadingCoeff = 1`
(since `u_inv` has constant coefficient `1`). -/

/-- The leading coefficient of the lifted `formalU_inv` is `1` (its constant
    coefficient as a power series). -/
theorem ofPowerSeries_formalU_inv_leadingCoeff :
    (HahnSeries.ofPowerSeries ℤ F (formalU_inv W) : LaurentSeries F).leadingCoeff = 1 := by
  set S : LaurentSeries F := HahnSeries.ofPowerSeries ℤ F (formalU_inv W) with hS
  have hS_ne : S ≠ 0 := ofPowerSeries_formalU_inv_ne_zero W
  have h_ord : S.orderTop = (0 : ℤ) := ofPowerSeries_formalU_inv_orderTop W
  rw [HahnSeries.leadingCoeff_of_ne_zero hS_ne]
  have h_untop : S.orderTop.untop (HahnSeries.orderTop_ne_top.2 hS_ne) = (0 : ℤ) := by
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, h_ord]
  rw [h_untop]
  -- goal: S.coeff 0 = 1
  have := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (formalU_inv W) 0
  simp only [Nat.cast_zero] at this
  rw [hS, this, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact formalU_inv_constantCoeff W

/-- `formalX W` has leading coefficient `1`. -/
theorem formalX_leadingCoeff :
    (formalX W).leadingCoeff = 1 := by
  rw [formalX, HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_of_single,
      ofPowerSeries_formalU_inv_leadingCoeff, mul_one]

/-- `formalY W` has leading coefficient `-1`. -/
theorem formalY_leadingCoeff :
    (formalY W).leadingCoeff = -1 := by
  rw [formalY, HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_neg,
      HahnSeries.leadingCoeff_of_single, ofPowerSeries_formalU_inv_leadingCoeff, mul_one]

/-! ### The Weierstrass equation for `(formalX, formalY)`

We follow Silverman IV.1 directly. The defining recurrence
`w(z) = z³ + a₁zw + a₂z²w + a₃w² + a₄zw² + a₆w³` (Silverman IV.1.1) IS the
Weierstrass equation `y² + a₁xy + a₃y - x³ - ... - a₆ = 0` after substituting
`x = z/w`, `y = -1/w` and multiplying through by `-w³`.

So the proof of `formalXY_weierstrass` is essentially: state the recurrence,
clear denominators in the field `LaurentSeries F`, and conclude via the recurrence. -/

-- The Silverman IV.1.1 recurrence `formalW_recurrence` is now proved in
-- `HasseWeil/FormalGroup.lean` and used directly here.

/-- `formalW W ≠ 0` because its coefficient at index 3 is 1. -/
theorem formalW_ne_zero : formalW W ≠ 0 := by
  intro h
  have h3 : @PowerSeries.coeff F _ 3 (formalW W) = 0 := by
    rw [h]; simp
  have : @PowerSeries.coeff F _ 3 (formalW W) = 1 := by
    change @PowerSeries.coeff F _ 3 (PowerSeries.mk (formalW_coeff W)) = 1
    rw [PowerSeries.coeff_mk]; exact formalW_coeff_three W
  rw [this] at h3
  exact one_ne_zero h3

/-- `HahnSeries.ofPowerSeries ℤ F (formalW W) ≠ 0` in `LaurentSeries F`. -/
theorem lifted_formalW_ne_zero :
    HahnSeries.ofPowerSeries ℤ F (formalW W) ≠ 0 := by
  intro h
  exact formalW_ne_zero W
    (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))

/-- `formalW = X^3 * formalU` as `PowerSeries F`. -/
theorem formalW_eq_X3_mul_U :
    formalW W = PowerSeries.X ^ 3 * formalU W := by
  ext n
  change @PowerSeries.coeff F _ n (PowerSeries.mk (formalW_coeff W))
    = @PowerSeries.coeff F _ n (PowerSeries.X ^ 3 * formalU W)
  rw [PowerSeries.coeff_mk]
  by_cases hn : n < 3
  · -- For n < 3: formalW_coeff W n = 0 by helper, and (X^3 * _).coeff n = 0
    have hLHS : formalW_coeff W n = 0 := by
      interval_cases n
      · exact formalW_coeff_zero W
      · exact formalW_coeff_one W
      · exact formalW_coeff_two W
    rw [hLHS]
    -- RHS: (X^3 * formalU).coeff n = 0 for n < 3
    rw [PowerSeries.coeff_X_pow_mul']
    rw [if_neg (by omega : ¬ 3 ≤ n)]
  · push Not at hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_comm 3 m, PowerSeries.coeff_X_pow_mul]
    change formalW_coeff W (m + 3) = @PowerSeries.coeff F _ m (formalU W)
    rw [show formalU W = PowerSeries.mk (fun n ↦ formalW_coeff W (n + 3)) from rfl,
        PowerSeries.coeff_mk]

/-- `formalW W` has `PowerSeries.order` equal to 3 (since `formalW = X^3 * formalU`
    and `formalU` is a unit). -/
theorem formalW_ps_order : (formalW W).order = 3 := by
  rw [formalW_eq_X3_mul_U, PowerSeries.order_mul, PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_unit (formalU_isUnit W)]
  rfl

/-- Helper: `HahnSeries.C a * HahnSeries.single n 1 = HahnSeries.single n a` in
    `LaurentSeries F`. -/
private theorem hC_single' (a : F) (n : ℤ) :
    (HahnSeries.C a : LaurentSeries F) * HahnSeries.single n (1 : F) =
      HahnSeries.single n a := by
  rw [show (HahnSeries.C a : LaurentSeries F) = HahnSeries.single (0 : ℤ) a from rfl,
      HahnSeries.single_mul_single, zero_add, mul_one]

/-- Helper: `HahnSeries.single 1 1 ^ k = HahnSeries.single (k : ℤ) 1` in
    `LaurentSeries F`. -/
private theorem single_one_pow' (k : ℕ) :
    (HahnSeries.single (1 : ℤ) (1 : F)) ^ k = HahnSeries.single (k : ℤ) (1 : F) := by
  rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]

/-- The lifted version of `formalW_recurrence` in `LaurentSeries F`, in a form
    where `ring` can handle the algebraic structure. Uses `z := single 1 1` as
    the formal variable and `HahnSeries.C aᵢ` as the constants. -/
private theorem formalW_recurrence_lift :
    HahnSeries.ofPowerSeries ℤ F (formalW W) =
      (HahnSeries.single (1 : ℤ) (1 : F)) ^ 3 +
        HahnSeries.C W.a₁ * (HahnSeries.single (1 : ℤ) (1 : F)) *
          HahnSeries.ofPowerSeries ℤ F (formalW W) +
        HahnSeries.C W.a₂ * (HahnSeries.single (1 : ℤ) (1 : F)) ^ 2 *
          HahnSeries.ofPowerSeries ℤ F (formalW W) +
        HahnSeries.C W.a₃ *
          (HahnSeries.ofPowerSeries ℤ F (formalW W)) ^ 2 +
        HahnSeries.C W.a₄ * (HahnSeries.single (1 : ℤ) (1 : F)) *
          (HahnSeries.ofPowerSeries ℤ F (formalW W)) ^ 2 +
        HahnSeries.C W.a₆ *
          (HahnSeries.ofPowerSeries ℤ F (formalW W)) ^ 3 := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ F) (formalW_recurrence W)
  simp only [map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_X] at h
  exact h

/-- Helper: `formalY W * lifted_formalW W = -1` in `LaurentSeries F`. -/
private theorem formalY_mul_formalW :
    formalY W * HahnSeries.ofPowerSeries ℤ F (formalW W) = -1 := by
  rw [formalY, formalW_eq_X3_mul_U, map_mul, HahnSeries.ofPowerSeries_X_pow]
  -- -single (-3) 1 * u_inv_lift * (single 3 1 * u_lift) = -1
  have h1 : HahnSeries.single (-3 : ℤ) (1 : F) * HahnSeries.single (3 : ℤ) (1 : F) = 1 := by
    rw [HahnSeries.single_mul_single, neg_add_cancel, mul_one]
    rfl
  have h2 : HahnSeries.ofPowerSeries ℤ F (formalU_inv W) *
      HahnSeries.ofPowerSeries ℤ F (formalU W) = 1 := by
    rw [← map_mul, formalU_inv_mul, map_one]
  calc -HahnSeries.single (-3 : ℤ) (1 : F) *
        HahnSeries.ofPowerSeries ℤ F (formalU_inv W) *
        (HahnSeries.single (3 : ℤ) (1 : F) * HahnSeries.ofPowerSeries ℤ F (formalU W))
      = -(HahnSeries.single (-3 : ℤ) (1 : F) * HahnSeries.single (3 : ℤ) (1 : F)) *
        (HahnSeries.ofPowerSeries ℤ F (formalU_inv W) *
          HahnSeries.ofPowerSeries ℤ F (formalU W)) := by ring
    _ = -(1 : LaurentSeries F) * 1 := by rw [h1, h2]
    _ = -1 := by ring

/-- Helper: `formalX W * lifted_formalW W = single 1 1` in `LaurentSeries F`. -/
private theorem formalX_mul_formalW :
    formalX W * HahnSeries.ofPowerSeries ℤ F (formalW W) =
      HahnSeries.single (1 : ℤ) (1 : F) := by
  rw [formalX, formalW_eq_X3_mul_U, map_mul, HahnSeries.ofPowerSeries_X_pow]
  have h1 : HahnSeries.single (-2 : ℤ) (1 : F) * HahnSeries.single (3 : ℤ) (1 : F) =
      HahnSeries.single (1 : ℤ) (1 : F) := by
    rw [HahnSeries.single_mul_single]
    change HahnSeries.single ((-2 : ℤ) + 3) ((1 : F) * 1) = HahnSeries.single (1 : ℤ) (1 : F)
    rw [show ((-2 : ℤ) + 3) = (1 : ℤ) from by ring, mul_one]
  have h2 : HahnSeries.ofPowerSeries ℤ F (formalU_inv W) *
      HahnSeries.ofPowerSeries ℤ F (formalU W) = 1 := by
    rw [← map_mul, formalU_inv_mul, map_one]
  calc HahnSeries.single (-2 : ℤ) (1 : F) *
        HahnSeries.ofPowerSeries ℤ F (formalU_inv W) *
        (HahnSeries.single (3 : ℤ) (1 : F) * HahnSeries.ofPowerSeries ℤ F (formalU W))
      = (HahnSeries.single (-2 : ℤ) (1 : F) * HahnSeries.single (3 : ℤ) (1 : F)) *
        (HahnSeries.ofPowerSeries ℤ F (formalU_inv W) *
          HahnSeries.ofPowerSeries ℤ F (formalU W)) := by ring
    _ = HahnSeries.single (1 : ℤ) (1 : F) * 1 := by rw [h1, h2]
    _ = HahnSeries.single (1 : ℤ) (1 : F) := mul_one _

/-- `formalY W = -1 / lifted_formalW W` in `LaurentSeries F`. -/
theorem formalY_eq_div :
    formalY W = -1 / HahnSeries.ofPowerSeries ℤ F (formalW W) := by
  rw [eq_div_iff (lifted_formalW_ne_zero W)]
  exact formalY_mul_formalW W

/-- `formalX W = (single 1 1) / lifted_formalW W` in `LaurentSeries F`. -/
theorem formalX_eq_div :
    formalX W = HahnSeries.single (1 : ℤ) (1 : F) /
      HahnSeries.ofPowerSeries ℤ F (formalW W) := by
  rw [eq_div_iff (lifted_formalW_ne_zero W)]
  exact formalX_mul_formalW W

/-- `(formalX W, formalY W)` satisfies the Weierstrass equation of `W` over `F`,
    interpreted as an identity in `LaurentSeries F`.

    **Proof (Silverman IV.1)**: substitute `x = z/w, y = -1/w` and clear
    denominators. The result is exactly the recurrence
    `w = z³ + a₁zw + a₂z²w + a₃w² + a₄zw² + a₆w³` (Silverman IV.1.1). -/
theorem formalXY_weierstrass :
    (formalY W) ^ 2 +
        (HahnSeries.ofPowerSeries ℤ F (@PowerSeries.C F _ W.a₁)) *
          (formalX W) * (formalY W) +
        (HahnSeries.ofPowerSeries ℤ F (@PowerSeries.C F _ W.a₃)) * (formalY W) -
      (formalX W) ^ 3 -
        (HahnSeries.ofPowerSeries ℤ F (@PowerSeries.C F _ W.a₂)) * (formalX W) ^ 2 -
        (HahnSeries.ofPowerSeries ℤ F (@PowerSeries.C F _ W.a₄)) * (formalX W) -
        (HahnSeries.ofPowerSeries ℤ F (@PowerSeries.C F _ W.a₆)) =
    0 := by
  rw [formalX_eq_div, formalY_eq_div]
  set w := HahnSeries.ofPowerSeries ℤ F (formalW W) with hw_def
  have hw_ne : w ≠ 0 := lifted_formalW_ne_zero W
  set z : LaurentSeries F := HahnSeries.single (1 : ℤ) (1 : F) with hz_def
  -- The Weierstrass equation, after substituting x = z/w, y = -1/w, becomes
  -- (1/w² - a₁ z/w² - a₃/w - z³/w³ - a₂ z²/w² - a₄ z/w - a₆ = 0).
  -- Multiplying by w³ gives: w - a₁zw - a₃w² - z³ - a₂z²w - a₄zw² - a₆w³ = 0.
  -- Rearranging: w = z³ + a₁zw + a₂z²w + a₃w² + a₄zw² + a₆w³, which is formalW_recurrence_lift.
  simp only [HahnSeries.ofPowerSeries_C]
  -- Use formalW_recurrence_lift
  have hrec : w =
      z ^ 3 +
        HahnSeries.C W.a₁ * z * w +
        HahnSeries.C W.a₂ * z ^ 2 * w +
        HahnSeries.C W.a₃ * w ^ 2 +
        HahnSeries.C W.a₄ * z * w ^ 2 +
        HahnSeries.C W.a₆ * w ^ 3 := formalW_recurrence_lift W
  -- The Weierstrass LHS times w^3 equals (RHS_hrec - LHS_hrec) which is 0.
  -- Use field_simp and linear_combination.
  field_simp
  linear_combination hrec

/-! ### The local parameter and `y_gen ≠ 0`

To define the local parameter `t = -x/y` in `K(E)`, we need `y_gen ≠ 0`. This
follows because if `y_gen = 0`, the Weierstrass equation forces
`x_gen³ + a₂x_gen² + a₄x_gen + a₆ = 0`, contradicting the transcendence of
`x_gen` over `F` (since the leading coefficient is `1 ≠ 0`). -/

/-- `y_gen ≠ 0` in `K(E)`.

    This follows from `y_gen = algebraMap R KE (AdjoinRoot.root W.polynomial)`
    being the image of `Y` modulo the Weierstrass polynomial `W.polynomial`,
    which is a polynomial of natDegree 1 in the outer variable. Since
    `W.polynomial` has natDegree 2 > 1, the class of `Y` is nonzero in the
    coordinate ring by `AdjoinRoot.mk_ne_zero_of_natDegree_lt`. The algebra
    map to the function field is injective (`IsFractionRing.injective`), so
    `y_gen ≠ 0` in `K(E)`.

    Reference: Silverman III.3 (the coordinate ring of an affine Weierstrass
    curve is a two-dimensional extension of `F[x]`). -/
theorem y_gen_ne_zero : y_gen W ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap W.toAffine.CoordinateRing KE) :=
    IsFractionRing.injective _ _
  have h_root_zero : AdjoinRoot.root W.toAffine.polynomial =
      (0 : W.toAffine.CoordinateRing) := by
    apply hinj
    show algebraMap W.toAffine.CoordinateRing KE
        (AdjoinRoot.root W.toAffine.polynomial) = algebraMap _ _ 0
    rw [map_zero]
    exact h
  have h_root_ne : AdjoinRoot.root W.toAffine.polynomial ≠
      (0 : W.toAffine.CoordinateRing) := by
    change AdjoinRoot.mk W.toAffine.polynomial Polynomial.X ≠ 0
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt Affine.monic_polynomial
      Polynomial.X_ne_zero
    rw [Polynomial.natDegree_X, Affine.natDegree_polynomial]
    decide
  exact h_root_ne h_root_zero

/-- The **local parameter** at `O`: `t = -x/y` in `K(E)`. This is a uniformizer
    at the place corresponding to `O` (Silverman IV.1). -/
noncomputable def localParam : KE :=
  -(x_gen W) / y_gen W

/-- `x_gen ≠ 0` in `K(E)`. Follows from the same argument as `y_gen_ne_zero`:
    `x_gen = algebraMap R KE (mk W.polynomial (C X))`, where `C X` has natDegree 0
    in the outer variable (< 2), so its class in `R = F[X][Y]/(W.polynomial)` is
    nonzero by `AdjoinRoot.mk_ne_zero_of_natDegree_lt`, and the algebra map
    `R → KE` is injective. -/
theorem x_gen_ne_zero : x_gen W ≠ 0 := by
  intro h
  have hinj_R : Function.Injective (algebraMap W.toAffine.CoordinateRing KE) :=
    IsFractionRing.injective _ _
  have h_poly_zero : algebraMap (Polynomial F) W.toAffine.CoordinateRing
      Polynomial.X = (0 : W.toAffine.CoordinateRing) := by
    apply hinj_R
    change algebraMap W.toAffine.CoordinateRing KE
        (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X) =
      algebraMap _ _ 0
    rw [map_zero]
    exact h
  have h_poly_ne : algebraMap (Polynomial F) W.toAffine.CoordinateRing
      Polynomial.X ≠ (0 : W.toAffine.CoordinateRing) := by
    change (Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) ≠ 0
    apply AdjoinRoot.mk_ne_zero_of_natDegree_lt Affine.monic_polynomial
    · exact Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero
    · rw [Polynomial.natDegree_C, Affine.natDegree_polynomial]; decide
  exact h_poly_ne h_poly_zero

/-- The local parameter is nonzero in `K(E)`. -/
theorem localParam_ne_zero : localParam W ≠ 0 := by
  unfold localParam
  rw [ne_eq, div_eq_zero_iff, not_or, neg_eq_zero]
  exact ⟨x_gen_ne_zero W, y_gen_ne_zero W⟩

/-! ### The local expansion ring homomorphism

The substitution `x_gen ↦ formalX W, y_gen ↦ formalY W` extends to a unique ring
homomorphism `K(E) → LaurentSeries F` because:

1. `(formalX W, formalY W)` satisfies the Weierstrass equation (`formalXY_weierstrass`),
   so the substitution is well-defined on the coordinate ring `R = F[X,Y]/(W)`.
2. `K(E) = Frac(R)` is the fraction field, and `LaurentSeries F` is itself a field
   (when `F` is a field), so the substitution extends to the fraction field via
   the universal property of localization.

The construction is currently a sorry; it requires assembling the substitution
through `AdjoinRoot.lift` and `IsLocalization.lift`. -/

/-- The inner ring hom `F[X] →+* LaurentSeries F` that sends the variable `X` to
    `formalX W`. -/
noncomputable def localExpand_inner : Polynomial F →+* LaurentSeries F :=
  Polynomial.eval₂RingHom (algebraMap F (LaurentSeries F)) (formalX W)

/-- The inner ring hom sends `Polynomial.X` to `formalX W`. -/
@[simp] theorem localExpand_inner_X :
    localExpand_inner W Polynomial.X = formalX W := by
  simp [localExpand_inner]

/-- The inner ring hom sends constants to their algebra image. -/
@[simp] theorem localExpand_inner_C (a : F) :
    localExpand_inner W (Polynomial.C a) = algebraMap F (LaurentSeries F) a := by
  simp [localExpand_inner]

/-- The Weierstrass polynomial, evaluated via the inner ring hom at `formalY W`,
    vanishes. This is `formalXY_weierstrass` expressed in terms of `Polynomial.eval₂`. -/
private theorem localExpand_weierstrass_eval :
    Polynomial.eval₂ (localExpand_inner W) (formalY W)
        W.toAffine.polynomial = 0 := by
  -- Unfold `localExpand_inner` and use `eval₂_eval₂RingHom_apply` to rewrite as
  -- `evalEval` over the mapped polynomial.
  unfold localExpand_inner
  rw [Polynomial.eval₂_eval₂RingHom_apply, ← Affine.map_polynomial,
    Affine.evalEval_polynomial]
  -- The goal matches `formalXY_weierstrass` up to `algebraMap F _ a ↔ ofPowerSeries C a`.
  have h_alg : ∀ (a : F), (algebraMap F (LaurentSeries F) a : LaurentSeries F) =
      HahnSeries.ofPowerSeries ℤ F (@PowerSeries.C F _ a) := by
    intro a
    rw [HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    h_alg]
  linear_combination formalXY_weierstrass W

/-- Lift to the coordinate ring `R = F[X][Y]/(W.polynomial)`. -/
private noncomputable def localExpand_coordHom :
    W.toAffine.CoordinateRing →+* LaurentSeries F :=
  AdjoinRoot.lift (localExpand_inner W) (formalY W) (localExpand_weierstrass_eval W)

/-- The coordinate ring lift sends `AdjoinRoot.root` to `formalY W`. -/
@[simp] private theorem localExpand_coordHom_root :
    localExpand_coordHom W (AdjoinRoot.root W.toAffine.polynomial) = formalY W := by
  simp [localExpand_coordHom, AdjoinRoot.lift_root]

/-- `(formalX W ^ n).orderTop = -2 * n` in `LaurentSeries F` (for `n : ℕ`). -/
theorem formalX_pow_orderTop (n : ℕ) :
    ((formalX W) ^ n).orderTop = ((-2 * n : ℤ) : WithTop ℤ) := by
  induction n with
  | zero =>
    rw [pow_zero]
    show (1 : LaurentSeries F).orderTop = _
    rw [HahnSeries.orderTop_one]
    rfl
  | succ k ih =>
    rw [pow_succ, HahnSeries.orderTop_mul, ih, formalX_orderTop]
    rw [← WithTop.coe_add]
    congr 1
    push_cast
    ring

/-- `(formalX W ^ n).leadingCoeff = 1` in `LaurentSeries F` (for `n : ℕ`). -/
theorem formalX_pow_leadingCoeff (n : ℕ) :
    ((formalX W) ^ n).leadingCoeff = 1 := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact HahnSeries.leadingCoeff_one
  | succ k ih =>
    rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, formalX_leadingCoeff, mul_one]

/-- Auxiliary: for a polynomial `p : F[X]` with `p ≠ 0`, the image
    `localExpand_inner W p` has `orderTop = -2 * p.natDegree` in `LaurentSeries F`.

    Proof strategy: induction on `p.natDegree`. The base case is degree 0 (`p =
    C a` for `a ≠ 0`, giving `orderTop = 0`). For higher degree, the leading
    term has `orderTop = -2 * p.natDegree` (minimal), while `p.eraseLead` has
    strictly smaller `natDegree`, so its image has *larger* `orderTop`, and
    the sum's `orderTop` equals the leading term's by `orderTop_add_eq_right`. -/
theorem localExpand_inner_orderTop_eq {p : Polynomial F} (hp : p ≠ 0) :
    (localExpand_inner W p).orderTop = ((-2 * p.natDegree : ℤ) : WithTop ℤ) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      have hpC : p = Polynomial.C (p.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hn
      have hc : p.coeff 0 ≠ 0 := by
        intro h
        rw [hpC, h, Polynomial.C_0] at hp
        exact hp rfl
      rw [hpC, localExpand_inner_C, LaurentSeries.algebraMap_apply]
      show (HahnSeries.single (0 : ℤ) (p.coeff 0)).orderTop = _
      rw [HahnSeries.orderTop_single hc]
      rfl
    · have hLead' : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      have h_eraseLead_le : p.eraseLead.natDegree ≤ n - 1 := by
        rw [← hn]; exact Polynomial.eraseLead_natDegree_le p
      have h_eraseLead_lt : p.eraseLead.natDegree < n := by omega
      have hDecomp : p = p.eraseLead + Polynomial.C p.leadingCoeff * Polynomial.X ^ n := by
        conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow p, hn]
      rw [hDecomp, map_add, map_mul, map_pow, localExpand_inner_C, localExpand_inner_X,
          LaurentSeries.algebraMap_apply]
      set A := localExpand_inner W p.eraseLead with hA_def
      set B : LaurentSeries F :=
        (HahnSeries.single (0 : ℤ) p.leadingCoeff) * (formalX W) ^ n with hB_def
      have hB_ord : B.orderTop = (((-2 * (n : ℤ)) : ℤ) : WithTop ℤ) := by
        rw [hB_def, HahnSeries.orderTop_mul, HahnSeries.orderTop_single hLead',
            formalX_pow_orderTop]
        -- ↑0 + ↑(-2 * ↑n) = ↑(-2 * ↑n)
        rw [← WithTop.coe_add]; congr 1; ring
      have h_lt : B.orderTop < A.orderTop := by
        rw [hB_ord]
        by_cases hEL : p.eraseLead = 0
        · rw [hA_def, hEL, map_zero, HahnSeries.orderTop_zero]
          exact WithTop.coe_lt_top _
        · have hA_ord : A.orderTop = (((-2 * (p.eraseLead.natDegree : ℤ)) : ℤ) : WithTop ℤ) :=
            ih _ h_eraseLead_lt hEL rfl
          rw [hA_ord, WithTop.coe_lt_coe]
          have : p.eraseLead.natDegree < n := h_eraseLead_lt
          nlinarith
      exact (HahnSeries.orderTop_add_eq_right h_lt).trans hB_ord

/-- Auxiliary: for a nonzero polynomial `p : F[X]`, `localExpand_inner W p ≠ 0`. -/
theorem localExpand_inner_ne_zero_of_ne_zero {p : Polynomial F} (hp : p ≠ 0) :
    localExpand_inner W p ≠ 0 := by
  intro h
  have horder := localExpand_inner_orderTop_eq W hp
  rw [h, HahnSeries.orderTop_zero] at horder
  exact absurd horder WithTop.top_ne_coe

/-- Auxiliary: for a polynomial `p : F[X]` with `p ≠ 0`, the image
    `localExpand_inner W p` has leading coefficient equal to `p.leadingCoeff`.

    Proof strategy: identical induction to `localExpand_inner_orderTop_eq`.
    The leading term `C p.leadingCoeff * X^n` maps to
    `single(0, p.leadingCoeff) · formalX^n`, which has leading coefficient
    `p.leadingCoeff · 1 = p.leadingCoeff` and orderTop `-2n` (minimal).
    `p.eraseLead` has strictly larger (less negative) orderTop, so
    `leadingCoeff_add_eq_right` gives the result. -/
theorem localExpand_inner_leadingCoeff {p : Polynomial F} (hp : p ≠ 0) :
    (localExpand_inner W p).leadingCoeff = p.leadingCoeff := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      have hpC : p = Polynomial.C (p.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero hn
      have hc : p.coeff 0 ≠ 0 := by
        intro h
        rw [hpC, h, Polynomial.C_0] at hp
        exact hp rfl
      rw [hpC, localExpand_inner_C, LaurentSeries.algebraMap_apply]
      change (HahnSeries.single (0 : ℤ) (p.coeff 0)).leadingCoeff = _
      rw [HahnSeries.leadingCoeff_of_single, Polynomial.leadingCoeff_C]
    · have hLead' : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      have h_eraseLead_le : p.eraseLead.natDegree ≤ n - 1 := by
        rw [← hn]; exact Polynomial.eraseLead_natDegree_le p
      have h_eraseLead_lt : p.eraseLead.natDegree < n := by omega
      have hDecomp : p = p.eraseLead + Polynomial.C p.leadingCoeff * Polynomial.X ^ n := by
        conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow p, hn]
      rw [hDecomp, map_add, map_mul, map_pow, localExpand_inner_C, localExpand_inner_X,
          LaurentSeries.algebraMap_apply]
      set A := localExpand_inner W p.eraseLead with hA_def
      -- Rewrite `HahnSeries.C` to `HahnSeries.single 0` (definitionally equal).
      change (A + (HahnSeries.single (0 : ℤ) p.leadingCoeff) * (formalX W) ^ n).leadingCoeff =
        (p.eraseLead + Polynomial.C p.leadingCoeff * Polynomial.X ^ n).leadingCoeff
      set B : LaurentSeries F :=
        (HahnSeries.single (0 : ℤ) p.leadingCoeff) * (formalX W) ^ n with hB_def
      have hB_ord : B.orderTop = (((-2 * (n : ℤ)) : ℤ) : WithTop ℤ) := by
        rw [hB_def, HahnSeries.orderTop_mul, HahnSeries.orderTop_single hLead',
            formalX_pow_orderTop]
        rw [← WithTop.coe_add]; congr 1; ring
      have hB_lead : B.leadingCoeff = p.leadingCoeff := by
        rw [hB_def, HahnSeries.leadingCoeff_mul, HahnSeries.leadingCoeff_of_single,
            formalX_pow_leadingCoeff, mul_one]
      have h_lt : B.orderTop < A.orderTop := by
        rw [hB_ord]
        by_cases hEL : p.eraseLead = 0
        · rw [hA_def, hEL, map_zero, HahnSeries.orderTop_zero]
          exact WithTop.coe_lt_top _
        · have hA_ord : A.orderTop = (((-2 * (p.eraseLead.natDegree : ℤ)) : ℤ) : WithTop ℤ) :=
            localExpand_inner_orderTop_eq W hEL
          rw [hA_ord, WithTop.coe_lt_coe]
          have : p.eraseLead.natDegree < n := h_eraseLead_lt
          nlinarith
      rw [HahnSeries.leadingCoeff_add_eq_right h_lt, hB_lead, ← hDecomp]

/-- Auxiliary: `(localExpand_inner W q) * formalY W` has odd `orderTop`
    (`= -2 * natDegree q - 3`) when `q ≠ 0`. -/
theorem localExpand_inner_mul_formalY_orderTop
    {q : Polynomial F} (hq : q ≠ 0) :
    ((localExpand_inner W q) * formalY W).orderTop =
      (((-2 * (q.natDegree : ℤ) - 3 : ℤ)) : WithTop ℤ) := by
  rw [HahnSeries.orderTop_mul, localExpand_inner_orderTop_eq W hq, formalY_orderTop,
    ← WithTop.coe_add]
  rfl

/-- The coordinate ring lift is injective.

    **Proof (Silverman IV.1)**: We use `exists_smul_basis_eq` to write any
    `r : R` as `r = p • 1 + q • (mk W Y)` for unique `p q : F[X]`. Its image
    under `localExpand_coordHom` is `p(formalX) + q(formalX) · formalY`.

    The parity argument: `p(formalX)` has `orderTop = -2 * natDegree p` (even,
    non-positive) when `p ≠ 0`, while `q(formalX) · formalY` has `orderTop =
    -2 * natDegree q - 3` (odd) when `q ≠ 0`. Even and odd differ, so a nonzero
    even-order series plus a nonzero odd-order series has `orderTop` equal to
    the smaller of the two — hence nonzero. So the sum is zero iff both
    summands are zero, iff `p = q = 0`, iff `r = 0`. -/
private theorem localExpand_coordHom_injective :
    Function.Injective (localExpand_coordHom W) :=
  (injective_iff_map_eq_zero _).mpr fun r hr ↦ by
    obtain ⟨p, q, rfl⟩ := Affine.CoordinateRing.exists_smul_basis_eq r
    -- Compute the image: `p • 1 + q • mk Y ↦ localExpand_inner p + localExpand_inner q * formalY`.
    have h_img : ∀ (f : Polynomial F) (x : W.toAffine.CoordinateRing),
        localExpand_coordHom W (f • x) =
          localExpand_inner W f * localExpand_coordHom W x := by
      intro f x
      rw [Affine.CoordinateRing.smul, map_mul]
      congr 1
      -- localExpand_coordHom W (mk (C f)) = localExpand_inner W f
      change localExpand_coordHom W
        ((AdjoinRoot.of W.toAffine.polynomial) f) = localExpand_inner W f
      simp [localExpand_coordHom, AdjoinRoot.lift_of]
    -- `mk W Y = AdjoinRoot.mk W.polynomial (Polynomial.X : F[X][X])`. But
    -- `AdjoinRoot.root W.polynomial = AdjoinRoot.mk W.polynomial X` (by def).
    have hY_eq :
        (Affine.CoordinateRing.mk W.toAffine (Polynomial.X : Polynomial (Polynomial F))) =
        AdjoinRoot.root W.toAffine.polynomial := rfl
    rw [map_add, h_img, h_img, map_one, mul_one, hY_eq, localExpand_coordHom_root] at hr
    -- hr : localExpand_inner W p + localExpand_inner W q * formalY W = 0
    set P := localExpand_inner W p with hP_def
    set Q := localExpand_inner W q with hQ_def
    -- Step 1: show `p = 0`.
    have hp_zero : p = 0 := by
      by_contra hp
      have hP_ord : P.orderTop = (((-2 * (p.natDegree : ℤ) : ℤ)) : WithTop ℤ) :=
        localExpand_inner_orderTop_eq W hp
      have hP_ne : P ≠ 0 := localExpand_inner_ne_zero_of_ne_zero W hp
      by_cases hq : q = 0
      · rw [hQ_def, hq, map_zero, zero_mul, add_zero] at hr
        exact hP_ne hr
      · have hQmul_ord : (Q * formalY W).orderTop =
            (((-2 * (q.natDegree : ℤ) - 3 : ℤ)) : WithTop ℤ) :=
          localExpand_inner_mul_formalY_orderTop W hq
        -- Orders differ because one is even, the other odd.
        have h_ne : P.orderTop ≠ (Q * formalY W).orderTop := by
          rw [hP_ord, hQmul_ord, Ne, WithTop.coe_inj]
          omega
        -- Sum with different orderTops is nonzero.
        rcases lt_or_gt_of_ne h_ne with h_lt | h_lt
        · have hsum : (P + Q * formalY W).orderTop = P.orderTop :=
            HahnSeries.orderTop_add_eq_left h_lt
          rw [hr, HahnSeries.orderTop_zero, hP_ord] at hsum
          exact absurd hsum WithTop.top_ne_coe
        · have hsum : (P + Q * formalY W).orderTop = (Q * formalY W).orderTop :=
            HahnSeries.orderTop_add_eq_right h_lt
          rw [hr, HahnSeries.orderTop_zero, hQmul_ord] at hsum
          exact absurd hsum WithTop.top_ne_coe
    -- Step 2: now `p = 0`, so show `q = 0`.
    subst hp_zero
    rw [hP_def, map_zero, zero_add] at hr
    have hfY_ne : formalY W ≠ 0 := formalY_ne_zero W
    have hQ_zero : Q = 0 := (mul_eq_zero.mp hr).resolve_right hfY_ne
    have hq_zero : q = 0 := by
      by_contra hq
      exact localExpand_inner_ne_zero_of_ne_zero W hq hQ_zero
    subst hq_zero
    -- Goal: 0 • 1 + 0 • mk W X = 0
    rw [Affine.CoordinateRing.smul, Polynomial.C_0, map_zero, zero_mul, zero_add,
        Affine.CoordinateRing.smul, Polynomial.C_0, map_zero, zero_mul]

/-- The **local expansion** ring hom `K(E) → LaurentSeries F`, sending `x_gen ↦
    formalX W` and `y_gen ↦ formalY W`.

The construction:
1. Build the inner ring hom `i : F[X] →+* LaurentSeries F` sending `X ↦ formalX W`.
2. Lift to `R = AdjoinRoot W.polynomial = F[X][Y]/(W) →+* LaurentSeries F` via
   `AdjoinRoot.lift` with root `formalY W`, using `formalXY_weierstrass` for
   the evaluation condition.
3. Extend to `K(E) = FractionRing R →+* LaurentSeries F` via `IsFractionRing.lift`,
   using that the coordinate ring lift is injective (source is a domain, target
   is a field, and the map is nonzero — sends `1` to `1`). -/
noncomputable def localExpand : KE →+* LaurentSeries F :=
  IsFractionRing.lift (localExpand_coordHom_injective W)

/-- `localExpand` sends `x_gen` to `formalX W`. -/
@[simp] theorem localExpand_x_gen : localExpand W (x_gen W) = formalX W := by
  unfold localExpand x_gen
  rw [IsFractionRing.lift_algebraMap]
  -- Goal: localExpand_coordHom W (algebraMap (Polynomial F) R X) = formalX W
  change localExpand_coordHom W
    ((AdjoinRoot.of W.toAffine.polynomial) Polynomial.X) = formalX W
  simp [localExpand_coordHom, AdjoinRoot.lift_of, localExpand_inner]

/-- `localExpand` sends `y_gen` to `formalY W`. -/
@[simp] theorem localExpand_y_gen : localExpand W (y_gen W) = formalY W := by
  unfold localExpand y_gen
  rw [IsFractionRing.lift_algebraMap, localExpand_coordHom_root]

/-- `localExpand` is an `F`-algebra hom. -/
theorem localExpand_algebraMap (a : F) :
    localExpand W (algebraMap F KE a) =
      HahnSeries.ofPowerSeries ℤ F (@PowerSeries.C F _ a) := by
  -- Factor algebraMap F KE = algebraMap R KE ∘ algebraMap F R
  rw [IsScalarTower.algebraMap_apply F W.toAffine.CoordinateRing KE,
    localExpand, IsFractionRing.lift_algebraMap]
  -- Factor algebraMap F R = (AdjoinRoot.of W.polynomial) ∘ C ∘ C
  change localExpand_coordHom W ((algebraMap F W.toAffine.CoordinateRing) a) = _
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) W.toAffine.CoordinateRing]
  change localExpand_coordHom W
    ((AdjoinRoot.of W.toAffine.polynomial) (algebraMap F (Polynomial F) a)) = _
  simp [localExpand_coordHom, AdjoinRoot.lift_of, localExpand_inner,
    LaurentSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]

/-- `localExpand` agrees with the inner ring hom `localExpand_inner` on the image
    of `F[X]` in `K(E)`: `localExpand (algebraMap (Polynomial F) KE p) =
    localExpand_inner W p`. Both factor the algebra map through the coordinate ring
    `R = AdjoinRoot W.polynomial` (where `algebraMap (Polynomial F) R = AdjoinRoot.of`),
    and `localExpand` is `IsFractionRing.lift` of `localExpand_coordHom = AdjoinRoot.lift
    localExpand_inner _`. -/
theorem localExpand_algebraMap_polynomial (p : Polynomial F) :
    localExpand W (algebraMap (Polynomial F) KE p) = localExpand_inner W p := by
  rw [IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing KE,
    localExpand, IsFractionRing.lift_algebraMap]
  change localExpand_coordHom W ((AdjoinRoot.of W.toAffine.polynomial) p) =
    localExpand_inner W p
  simp [localExpand_coordHom, AdjoinRoot.lift_of]

/-- The `orderTop` of the local expansion of `algebraMap (Polynomial F) KE p` for a
    nonzero polynomial `p` is `-2 · natDegree p`. This is `localExpand_inner_orderTop_eq`
    transported through `localExpand_algebraMap_polynomial`. -/
theorem orderTop_localExpand_algebraMap_polynomial {p : Polynomial F} (hp : p ≠ 0) :
    (localExpand W (algebraMap (Polynomial F) KE p)).orderTop =
      ((-2 * p.natDegree : ℤ) : WithTop ℤ) := by
  rw [localExpand_algebraMap_polynomial]
  exact localExpand_inner_orderTop_eq W hp

/-- `localExpand` sends `localParam W` to the variable `t` of `LaurentSeries F`.
    This is the key compatibility: the local parameter expands to the formal variable. -/
theorem localExpand_localParam :
    localExpand W (localParam W) = HahnSeries.single (1 : ℤ) 1 := by
  -- localExpand(-x_gen/y_gen) = -formalX W / formalY W
  rw [localParam, map_div₀, map_neg, localExpand_x_gen, localExpand_y_gen]
  -- Goal: -formalX W / formalY W = single 1 1
  rw [formalX_eq_div, formalY_eq_div]
  -- -formalX W = -(z / formalW W), formalY W = -(1 / formalW W)
  have hw_ne : (HahnSeries.ofPowerSeries ℤ F (formalW W) : LaurentSeries F) ≠ 0 :=
    lifted_formalW_ne_zero W
  set w := HahnSeries.ofPowerSeries ℤ F (formalW W) with hw_def
  -- -(z/w) / (-(1/w)) = (z/w) / (1/w) = z
  field_simp

end HasseWeil
