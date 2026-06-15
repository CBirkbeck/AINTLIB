/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.MulByIntPullback
import HasseWeil.Curves.Infinity

/-!
# Bridge from `W.toAffine` to `SmoothPlaneCurve` for `ordAtInfty`

This file provides the minimal bridge needed to apply worker-I's
`ordAtInfty` infrastructure (in `HasseWeil/Curves/Infinity.lean`) to the
generic-point framework used by `MulByIntPullback.lean` and
`AdditionPullback.lean`.

Concretely: given `W : WeierstrassCurve F` with `W.toAffine.IsElliptic`,
we wrap `W.toAffine` as a `SmoothPlaneCurve F` and re-export the
`ordAtInfty` results for `x_gen W` and `y_gen W` (and the
basefield-algebraMap) in a directly usable form.

The downstream consumer is the witness-parametric pole argument
`addPullback_x_ne_const_of_pole` (`AdditionPullback.lean`), whose pole
witnesses are supplied per-isogeny (e.g. in `AdditionPullback/Frobenius.lean`).

## Main results

* `W_smooth W : SmoothPlaneCurve F` — the bridge wrapper.
* `ordAtInfty_x_gen` — `ord_∞(x_gen) = -2`.
* `ordAtInfty_y_gen` — `ord_∞(y_gen) = -3`.
* `ordAtInfty_algebraMap_F_nonzero` — constants from `F` have `ord_∞ = 0`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, IV.1.
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "KE" => W.toAffine.FunctionField

/-- Wrap `W.toAffine` as a `SmoothPlaneCurve F` so that worker-I's
`ordAtInfty` infrastructure applies. -/
noncomputable def W_smooth : SmoothPlaneCurve F :=
  ⟨W.toAffine⟩

@[simp] theorem W_smooth_toAffine : (W_smooth W).toAffine = W.toAffine := rfl

/-- The function field of the SmoothPlaneCurve wrapper equals `KE`
definitionally (both are `W.toAffine.FunctionField`). -/
@[simp] theorem W_smooth_functionField :
    (W_smooth W).FunctionField = KE := rfl

/-- The `coordX` of the wrapper matches our `x_gen W` at the function-field
level. Both are `algebraMap (Polynomial F) KE Polynomial.X`. -/
theorem coordX_W_smooth_eq_x_gen : (W_smooth W).coordX = x_gen W := by
  show (algebraMap (Polynomial F) (W_smooth W).FunctionField Polynomial.X) =
    algebraMap W.toAffine.CoordinateRing KE
      (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)
  rw [← IsScalarTower.algebraMap_apply (Polynomial F) W.toAffine.CoordinateRing KE]
  rfl

/-- `ord_∞(x_gen W) = -2` — Silverman II.1 / IV.1 for the generic x. -/
theorem ordAtInfty_x_gen :
    (W_smooth W).ordAtInfty (x_gen W) = ((-2 : ℤ) : WithTop ℤ) := by
  rw [← coordX_W_smooth_eq_x_gen]
  exact (W_smooth W).ordAtInfty_coordX

/-- The `coordY` of the wrapper matches our `y_gen W` at the function-field
level. Both are the image of `AdjoinRoot.root W.polynomial` under the
algebraMap to `KE`. The `basis_one` lemma identifies
`basis 1 = AdjoinRoot.mk _ X = AdjoinRoot.root _`. -/
theorem coordY_W_smooth_eq_y_gen : (W_smooth W).coordY = y_gen W := by
  unfold SmoothPlaneCurve.coordY y_gen
  rw [Affine.CoordinateRing.basis_one]
  rfl

/-- `ord_∞(y_gen W) = -3` — Silverman II.1 / IV.1 for the generic y. -/
theorem ordAtInfty_y_gen :
    (W_smooth W).ordAtInfty (y_gen W) = ((-3 : ℤ) : WithTop ℤ) := by
  rw [← coordY_W_smooth_eq_y_gen]
  exact (W_smooth W).ordAtInfty_coordY

/-- `ord_∞(algebraMap F KE c) = 0` for nonzero `c : F`. Direct corollary of
`SmoothPlaneCurve.ordAtInfty_algebraMap_F_nonzero` applied to `W_smooth W`. -/
theorem ordAtInfty_algebraMap_F_nonzero {c : F} (hc : c ≠ 0) :
    (W_smooth W).ordAtInfty (algebraMap F KE c) = 0 :=
  (W_smooth W).ordAtInfty_algebraMap_F_nonzero hc

/-! ### Powers of generators -/

/-- `x_gen W ≠ 0` follows from `(W_smooth W).coordX_ne_zero` via the bridge. -/
theorem x_gen_ne_zero : x_gen W ≠ 0 := by
  rw [← coordX_W_smooth_eq_x_gen]; exact (W_smooth W).coordX_ne_zero

/-- `y_gen W ≠ 0` follows from `(W_smooth W).coordY_ne_zero` via the bridge. -/
theorem y_gen_ne_zero : y_gen W ≠ 0 := by
  rw [← coordY_W_smooth_eq_y_gen]; exact (W_smooth W).coordY_ne_zero

/-- `ord_∞(x_gen^n) = n • (-2)`. -/
theorem ordAtInfty_x_gen_pow (n : ℕ) :
    (W_smooth W).ordAtInfty (x_gen W ^ n) = n • ((-2 : ℤ) : WithTop ℤ) := by
  have h := HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_pow (W_smooth W)
    (x_gen_ne_zero W) n
  rw [ordAtInfty_x_gen] at h
  exact h

/-- `ord_∞(y_gen^n) = n • (-3)`. -/
theorem ordAtInfty_y_gen_pow (n : ℕ) :
    (W_smooth W).ordAtInfty (y_gen W ^ n) = n • ((-3 : ℤ) : WithTop ℤ) := by
  have h := HasseWeil.Curves.SmoothPlaneCurve.ordAtInfty_pow (W_smooth W)
    (y_gen_ne_zero W) n
  rw [ordAtInfty_y_gen] at h
  exact h

/-! ### Tower bridges for `Φ_ff` / `ΨSq_ff` to `algebraMap (Polynomial F) KE`

Both `Φ_ff W n` and `ΨSq_ff W n` are defined as
`algebraMap R KE (algebraMap (Polynomial F) R poly)`. By scalar tower
`F[X] → R → KE`, this equals `algebraMap (Polynomial F) KE poly` directly.
This bridges to `ordAtInfty_algebraMap_polynomial_of_ne_zero` for the
ord computation. -/

/-- `Φ_ff W n = algebraMap (Polynomial F) KE (W.Φ n)` via the scalar tower
`F[X] → CoordinateRing → FunctionField`. -/
theorem Φ_ff_eq_algebraMap_polynomial (n : ℤ) :
    Φ_ff W n = algebraMap (Polynomial F) KE (W.Φ n) :=
  (IsScalarTower.algebraMap_apply
    (Polynomial F) W.toAffine.CoordinateRing KE (W.Φ n)).symm

/-- `ΨSq_ff W n = algebraMap (Polynomial F) KE (W.ΨSq n)` via the scalar tower
`F[X] → CoordinateRing → FunctionField`. -/
theorem ΨSq_ff_eq_algebraMap_polynomial (n : ℤ) :
    ΨSq_ff W n = algebraMap (Polynomial F) KE (W.ΨSq n) :=
  (IsScalarTower.algebraMap_apply
    (Polynomial F) W.toAffine.CoordinateRing KE (W.ΨSq n)).symm

/-! ### `ordAtInfty` of `Φ_ff` / `ΨSq_ff`

Direct from the tower bridge + `ordAtInfty_algebraMap_polynomial_of_ne_zero` +
mathlib's `natDegree_Φ` / `natDegree_ΨSq`. -/

/-- `ord_∞(Φ_ff W n) = -2 · n.natAbs²`. -/
theorem ordAtInfty_Φ_ff (n : ℤ) :
    (W_smooth W).ordAtInfty (Φ_ff W n) =
      ((-2 * (n.natAbs : ℤ) ^ 2 : ℤ) : WithTop ℤ) := by
  rw [Φ_ff_eq_algebraMap_polynomial]
  show (W_smooth W).ordAtInfty
    (algebraMap (Polynomial F) (W_smooth W).FunctionField (W.Φ n)) = _
  rw [(W_smooth W).ordAtInfty_algebraMap_polynomial_of_ne_zero (W.Φ_ne_zero n),
      W.natDegree_Φ n]
  push_cast
  ring_nf

/-- `ord_∞(ΨSq_ff W n) = -2 · (n.natAbs² - 1)` for `(n : F) ≠ 0`. -/
theorem ordAtInfty_ΨSq_ff (n : ℤ) (hnF : (n : F) ≠ 0) :
    (W_smooth W).ordAtInfty (ΨSq_ff W n) =
      ((-2 * ((n.natAbs : ℤ) ^ 2 - 1) : ℤ) : WithTop ℤ) := by
  rw [ΨSq_ff_eq_algebraMap_polynomial]
  show (W_smooth W).ordAtInfty
    (algebraMap (Polynomial F) (W_smooth W).FunctionField (W.ΨSq n)) = _
  rw [(W_smooth W).ordAtInfty_algebraMap_polynomial_of_ne_zero (W.ΨSq_ne_zero hnF),
      W.natDegree_ΨSq hnF]
  have h_pos : 1 ≤ n.natAbs ^ 2 := by
    have hn_ne : n.natAbs ≠ 0 := by
      intro h; apply hnF
      have : n = 0 := Int.natAbs_eq_zero.mp h
      rw [this, Int.cast_zero]
    have : 1 ≤ n.natAbs := Nat.one_le_iff_ne_zero.mpr hn_ne
    calc 1 = 1 ^ 2 := by norm_num
      _ ≤ n.natAbs ^ 2 := Nat.pow_le_pow_left this 2
  push_cast [Nat.cast_sub h_pos]
  ring_nf

/-- The composition `algebraMap (Polynomial F) → CoordinateRing → FunctionField`
is injective. Composes `Affine.CoordinateRing.algebraMap_poly_injective` with
`IsFractionRing.injective`. -/
private theorem algebraMap_polynomial_KE_injective :
    Function.Injective (algebraMap (Polynomial F) W.toAffine.FunctionField) := by
  show Function.Injective ((algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
    (algebraMap (Polynomial F) W.toAffine.CoordinateRing))
  exact (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
    Affine.CoordinateRing.algebraMap_poly_injective

omit [DecidableEq F] in
/-- `Φ_ff W n ≠ 0` for any n. Direct from `W.Φ_ne_zero` + algebraMap injectivity. -/
theorem Φ_ff_ne_zero (n : ℤ) : Φ_ff W n ≠ 0 := by
  classical
  rw [Φ_ff_eq_algebraMap_polynomial]
  intro h
  exact W.Φ_ne_zero n
    (algebraMap_polynomial_KE_injective W (h.trans (map_zero _).symm))

/-- `mulByInt_x W n ≠ 0` for `n ≠ 0`. Direct from `Φ_ff_ne_zero` and
`ΨSq_ff_ne_zero`. -/
theorem mulByInt_x_ne_zero (n : ℤ) (hn : n ≠ 0) : mulByInt_x W n ≠ 0 := by
  unfold mulByInt_x
  exact div_ne_zero (Φ_ff_ne_zero W n) (ΨSq_ff_ne_zero W hn)

/-- `ord_∞(mulByInt_x W n) = -2` for `n ≠ 0` and `(n : F) ≠ 0`.

Direct from `ordAtInfty_Φ_ff`, `ordAtInfty_ΨSq_ff`, and division: the
`-2 · n.natAbs²` and `-2 · (n.natAbs² - 1)` cancel down to `-2`. -/
theorem ordAtInfty_mulByInt_x (n : ℤ) (hn : n ≠ 0) (hnF : (n : F) ≠ 0) :
    (W_smooth W).ordAtInfty (mulByInt_x W n) = ((-2 : ℤ) : WithTop ℤ) := by
  unfold mulByInt_x
  have hΦ_ne := Φ_ff_ne_zero W n
  have hΨ_ne := ΨSq_ff_ne_zero W hn
  have h_inv_ne : (ΨSq_ff W n)⁻¹ ≠ 0 := inv_ne_zero hΨ_ne
  have h_div_eq : Φ_ff W n / ΨSq_ff W n = Φ_ff W n * (ΨSq_ff W n)⁻¹ := div_eq_mul_inv _ _
  have h_mul : (W_smooth W).ordAtInfty (Φ_ff W n * (ΨSq_ff W n)⁻¹) =
      (W_smooth W).ordAtInfty (Φ_ff W n) + (W_smooth W).ordAtInfty ((ΨSq_ff W n)⁻¹) :=
    (W_smooth W).ordAtInfty_mul hΦ_ne h_inv_ne
  rw [h_div_eq, h_mul, (W_smooth W).ordAtInfty_inv,
      ordAtInfty_Φ_ff W n, ordAtInfty_ΨSq_ff W n hnF]
  rw [show ((-2 * (n.natAbs : ℤ) ^ 2 : ℤ) : WithTop ℤ) +
          -(((-2 * ((n.natAbs : ℤ) ^ 2 - 1) : ℤ) : WithTop ℤ)) =
        (((-2) : ℤ) : WithTop ℤ) from by
      rw [show -(((-2 * ((n.natAbs : ℤ) ^ 2 - 1) : ℤ) : WithTop ℤ)) =
            ((-(-2 * ((n.natAbs : ℤ) ^ 2 - 1)) : ℤ) : WithTop ℤ) from by
        push_cast; rfl]
      rw [show ((-2 * (n.natAbs : ℤ) ^ 2 : ℤ) : WithTop ℤ) +
            ((-(-2 * ((n.natAbs : ℤ) ^ 2 - 1)) : ℤ) : WithTop ℤ) =
          (((-2 * (n.natAbs : ℤ) ^ 2) + (-(-2 * ((n.natAbs : ℤ) ^ 2 - 1))) : ℤ) :
              WithTop ℤ) from by
        push_cast; rfl]
      congr 1
      ring]

/-- **Unconditional pole of `mulByInt_x W n`**: `ord_∞(mulByInt_x W n) < 0` for
every `n ≠ 0`, with **no** `(n : F) ≠ 0` hypothesis.

Unlike `ordAtInfty_mulByInt_x` (which pins the exact value `-2`, valid only when
`(n : F) ≠ 0` so that `natDegree (ΨSq n) = n.natAbs² - 1`), this weaker bound
holds even in the inseparable case `(n : F) = 0` (e.g. `n = r·q` with `q = #K`).
The key is mathlib's *unconditional* degree facts: `natDegree (Φ n) = n.natAbs²`
(`natDegree_Φ`) and `natDegree (ΨSq n) ≤ n.natAbs² - 1` (`natDegree_ΨSq_le`). The
numerator therefore strictly out-degrees the denominator, so the ratio
`Φ_ff / ΨSq_ff` has a pole at `O`:
`ord = -2·natAbs² - (-2·natDegree (ΨSq n)) ≤ -2·natAbs² + 2(natAbs² - 1) = -2 < 0`.

This is exactly the brick needed for the V-side "summand reduces to `O`" facts,
where the Frobenius factor `r·q` lands in the inseparable regime. -/
theorem ordAtInfty_mulByInt_x_neg (n : ℤ) (hn : n ≠ 0) :
    (W_smooth W).ordAtInfty (mulByInt_x W n) < 0 := by
  classical
  have hΦ_ne := Φ_ff_ne_zero W n
  have hΨ_ne := ΨSq_ff_ne_zero W hn
  have h_inv_ne : (ΨSq_ff W n)⁻¹ ≠ 0 := inv_ne_zero hΨ_ne
  -- `ord (Φ_ff / ΨSq_ff) = ord Φ_ff - ord ΨSq_ff`.
  have h_div_eq : Φ_ff W n / ΨSq_ff W n = Φ_ff W n * (ΨSq_ff W n)⁻¹ := div_eq_mul_inv _ _
  have h_mul : (W_smooth W).ordAtInfty (Φ_ff W n * (ΨSq_ff W n)⁻¹) =
      (W_smooth W).ordAtInfty (Φ_ff W n) + (W_smooth W).ordAtInfty ((ΨSq_ff W n)⁻¹) :=
    (W_smooth W).ordAtInfty_mul hΦ_ne h_inv_ne
  unfold mulByInt_x
  rw [h_div_eq, h_mul, (W_smooth W).ordAtInfty_inv]
  -- `ord Φ_ff = -2·natAbs n²` (unconditional).
  rw [ordAtInfty_Φ_ff W n]
  -- `ord ΨSq_ff = -2·natDegree (ΨSq n)` (unconditional polynomial-ord lemma).
  have h_ΨSq_ord : (W_smooth W).ordAtInfty (ΨSq_ff W n) =
      ((-2 * (W.ΨSq n).natDegree : ℤ) : WithTop ℤ) := by
    rw [ΨSq_ff_eq_algebraMap_polynomial]
    exact (W_smooth W).ordAtInfty_algebraMap_polynomial_of_ne_zero (ΨSq_poly_ne_zero W hn)
  rw [h_ΨSq_ord]
  -- Goal: (-2·natAbs²) + -(-2·natDegree (ΨSq n)) < 0, i.e. the cast inequality.
  -- Degree bound: natDegree (ΨSq n) ≤ natAbs² - 1, and natAbs ≥ 1 ⟹ natAbs² ≥ 1.
  have h_deg_le : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := W.natDegree_ΨSq_le n
  have h_natAbs_pos : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
  -- ℕ-level: natDegree (ΨSq n) < natAbs n², hence the ℤ-cast inequality.
  have h_nat_lt : (W.ΨSq n).natDegree < n.natAbs ^ 2 := by
    have h_one_le : 1 ≤ n.natAbs ^ 2 := by nlinarith [h_natAbs_pos]
    omega
  -- Combine into a strict integer inequality, then transport across the casts.
  have h_int : (-2 * (n.natAbs ^ 2 : ℕ) : ℤ) + -(-2 * ((W.ΨSq n).natDegree : ℕ) : ℤ) < 0 := by
    have h2 : ((W.ΨSq n).natDegree : ℤ) < (n.natAbs ^ 2 : ℕ) := by exact_mod_cast h_nat_lt
    push_cast at h2 ⊢
    linarith
  -- Transport `h_int` across the `WithTop ℤ` coercions.
  exact_mod_cast h_int

/-- **`ord_∞(mulByInt_x W n)` is an explicit even value `≤ -2`** for every `n ≠ 0`, with **no**
`(n : F) ≠ 0` hypothesis — so it holds in the *inseparable* case `(n : F) = 0` (e.g. `n = r` with
`p ∣ r`).

There exists `M ≤ -2` with `ord_∞(mulByInt_x W n) = M` and `M` *even*.  Concretely
`M = -2·(natAbs n² - natDegree (ΨSq n))`, and `natDegree (ΨSq n) < natAbs n²`
(`natDegree_ΨSq_le` + `natAbs n ≥ 1`) gives `natAbs n² - natDegree (ΨSq n) ≥ 1`, hence `M ≤ -2`.
Evenness is recorded because the curve-equation `y`-order is `3M/2`, which requires `M` even.

This strengthens `ordAtInfty_mulByInt_x_neg` (which only states `< 0`) to the sharp form needed for
the **asymmetric** inseparable pole analysis of the pencil `r·π − s` when `p ∣ r`. -/
theorem exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two (n : ℤ) (hn : n ≠ 0) :
    ∃ M : ℤ, (W_smooth W).ordAtInfty (mulByInt_x W n) = ((M : ℤ) : WithTop ℤ) ∧
      M ≤ -2 ∧ Even M := by
  classical
  have hΦ_ne := Φ_ff_ne_zero W n
  have hΨ_ne := ΨSq_ff_ne_zero W hn
  have h_inv_ne : (ΨSq_ff W n)⁻¹ ≠ 0 := inv_ne_zero hΨ_ne
  have h_div_eq : Φ_ff W n / ΨSq_ff W n = Φ_ff W n * (ΨSq_ff W n)⁻¹ := div_eq_mul_inv _ _
  have h_mul : (W_smooth W).ordAtInfty (Φ_ff W n * (ΨSq_ff W n)⁻¹) =
      (W_smooth W).ordAtInfty (Φ_ff W n) + (W_smooth W).ordAtInfty ((ΨSq_ff W n)⁻¹) :=
    (W_smooth W).ordAtInfty_mul hΦ_ne h_inv_ne
  -- `ord ΨSq_ff = -2·natDegree (ΨSq n)` (unconditional polynomial-ord lemma).
  have h_ΨSq_ord : (W_smooth W).ordAtInfty (ΨSq_ff W n) =
      ((-2 * (W.ΨSq n).natDegree : ℤ) : WithTop ℤ) := by
    rw [ΨSq_ff_eq_algebraMap_polynomial]
    exact (W_smooth W).ordAtInfty_algebraMap_polynomial_of_ne_zero (ΨSq_poly_ne_zero W hn)
  refine ⟨-2 * ((n.natAbs : ℤ) ^ 2 - (W.ΨSq n).natDegree), ?_, ?_, ?_⟩
  · unfold mulByInt_x
    rw [h_div_eq, h_mul, (W_smooth W).ordAtInfty_inv, ordAtInfty_Φ_ff W n, h_ΨSq_ord]
    rw [show -(((-2 * ((W.ΨSq n).natDegree : ℤ)) : ℤ) : WithTop ℤ) =
          (((-(-2 * ((W.ΨSq n).natDegree : ℤ))) : ℤ) : WithTop ℤ) from by push_cast; rfl]
    rw [show ((-2 * (n.natAbs : ℤ) ^ 2 : ℤ) : WithTop ℤ) +
          (((-(-2 * ((W.ΨSq n).natDegree : ℤ))) : ℤ) : WithTop ℤ) =
        ((((-2 * (n.natAbs : ℤ) ^ 2) + (-(-2 * ((W.ΨSq n).natDegree : ℤ)))) : ℤ) :
            WithTop ℤ) from by push_cast; rfl]
    congr 1
    ring
  · -- `natDegree (ΨSq n) < natAbs n²`, so `natAbs n² − natDegree (ΨSq n) ≥ 1`, so `M ≤ -2`.
    have h_deg_le : (W.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 := W.natDegree_ΨSq_le n
    have h_natAbs_pos : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
    have h_one_le : 1 ≤ n.natAbs ^ 2 := by nlinarith [h_natAbs_pos]
    have h_nat_lt : (W.ΨSq n).natDegree < n.natAbs ^ 2 := by omega
    have h2 : ((W.ΨSq n).natDegree : ℤ) < ((n.natAbs : ℤ) ^ 2) := by exact_mod_cast h_nat_lt
    nlinarith [h2]
  · exact ⟨-((n.natAbs : ℤ) ^ 2 - (W.ΨSq n).natDegree), by ring⟩

end HasseWeil
