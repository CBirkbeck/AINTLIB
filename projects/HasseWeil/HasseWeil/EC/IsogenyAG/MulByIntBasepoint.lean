/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG
import HasseWeil.OrdAtInftyBridge
import HasseWeil.OmegaPullbackCoeff
import HasseWeil.AdditionPullback
import HasseWeil.Curves.OrdAtInftyRamification
import HasseWeil.Curves.WithTopArith

/-!
# The basepoint condition for `[n]`: `MulByIntBasepoint` holds unconditionally

This file discharges `HasseWeil.EC.MulByIntBasepoint W hn` (the
`ord_∞`-regularity basepoint condition for the pullback of `[n]`,
`IsogenyAG.lean`) for **every** `n ≠ 0`, with **no** separability hypothesis
`(n : F) ≠ 0` — the inseparable case `char F ∣ n` is covered.

## The `{1, y}`-parity route

Every `f ∈ K(E)` decomposes as `f = r₁ + r₂·y` with `r₁, r₂ ∈ F(x)`
(`exists_decomp`), and the orders of the two summands have opposite parity, so
`ord_∞ f = min(ord_∞ r₁, ord_∞ r₂ − 3)` (`ordAtInfty_basis_eq_min`).  Hence
`ord_∞ f ≥ 0` forces `ord_∞ r₁ ≥ 0` and `ord_∞ r₂ ≥ 3` separately.

Applying `[n]^* = mulByInt_pullbackAlgHom`:
`[n]^*f = r₁(ξ) + r₂(ξ)·η` where `ξ = mulByInt_x W n` (a rational function of
`x` with `ord_∞ ξ = 2m` for an explicit even `2m ≤ -2`,
`exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two`) and `η = mulByInt_y W n`
with `ord_∞ η ≥ 3m` (curve-equation bound, `le_ordAtInfty_mulByInt_y`).

* For a rational `r = p/q ∈ F(x)` the dominant-term lemma
  (`ordAtInfty_aeval_of_ord_eq`) gives `ord_∞(r(ξ)) = (deg p − deg q)·2m`, so
  `ord_∞ r ≥ 0 ⟹ deg p ≤ deg q ⟹ ord_∞(r₁(ξ)) ≥ 0`.
* For the `y`-term, `ord_∞ r₂ ≥ 3` forces `deg q₂ − deg p₂ ≥ 2`, so
  `ord_∞(r₂(ξ)·η) ≥ (−2)·2m + 3m = −m ≥ 1 > 0`.

The ultrametric inequality `ordAtInfty_add_ge_min` then yields
`ord_∞([n]^*f) ≥ 0`.

## Main results

* `Curves.SmoothPlaneCurve.ordAtInfty_aeval_of_ord_eq` — dominant-term order of
  a polynomial evaluated at an element of strictly negative order.
* `le_ordAtInfty_mulByInt_y` — `ord_∞(mulByInt_y W n) ≥ 3m` whenever
  `ord_∞(mulByInt_x W n) = 2m ≤ -2` (one-sided, no `(n : F) ≠ 0`).
* `mulByInt_pullbackAlgHom_ordAtInfty_nonneg` — the workhorse.
* `EC.mulByIntBasepoint_holds` — `MulByIntBasepoint W hn` for all `n ≠ 0`.
* `EC.Isogeny.mulByInt` — `[n]` as an `EC.Isogeny W W`, witness-free.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.1, III.4.
-/

open WeierstrassCurve Polynomial

namespace HasseWeil

/-! ### Dominant-term order lemmas for polynomial evaluation

For `g` with `ord_∞ g = M < 0` and `p ∈ F[X]` of degree `d`, the summands of
`p(g) = Σ cᵢ gⁱ` have orders `i·M`, all `≥ d·M` with the leading term attaining
`d·M` strictly below the rest; the ultrametric gives `ord_∞ p(g) = d·M`. -/

namespace Curves.SmoothPlaneCurve

variable {F : Type*} [Field F] (C : SmoothPlaneCurve F)

/-- **Ultrametric lower bound for polynomial evaluation**: if `ord_∞ g = M < 0`
and `natDegree p ≤ k`, then `ord_∞(p(g)) ≥ k·M`. -/
theorem le_ordAtInfty_aeval {g : C.FunctionField} {M : ℤ}
    (hg : C.ordAtInfty g = ((M : ℤ) : WithTop ℤ)) (hM : M < 0)
    (p : Polynomial F) {k : ℕ} (hk : p.natDegree ≤ k) :
    (((k : ℤ) * M : ℤ) : WithTop ℤ) ≤ C.ordAtInfty (Polynomial.aeval g p) := by
  have hg_ne : g ≠ 0 :=
    (C.ordAtInfty_eq_top_iff g).not.mp (ne_of_eq_of_ne hg WithTop.coe_ne_top)
  rw [Polynomial.aeval_eq_sum_range]
  refine le_ordAtInfty_sum _ _ (fun i hi ↦ ?_)
  rcases eq_or_ne (p.coeff i) 0 with hc | hc
  · rw [hc, zero_smul, C.ordAtInfty_zero]
    exact le_top
  · have hc_ne : algebraMap F C.FunctionField (p.coeff i) ≠ 0 :=
      (map_ne_zero (algebraMap F C.FunctionField)).mpr hc
    rw [Algebra.smul_def,
      C.ordAtInfty_mul hc_ne (pow_ne_zero i hg_ne),
      C.ordAtInfty_algebraMap_F_nonzero hc,
      C.ord_pow_concrete hg_ne M i hg, zero_add]
    have hik : i ≤ k :=
      le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hk
    have : (k : ℤ) * M ≤ (i : ℤ) * M :=
      mul_le_mul_of_nonpos_right (by exact_mod_cast hik) hM.le
    exact_mod_cast this

/-- **Dominant-term order of polynomial evaluation**: if `ord_∞ g = M < 0` and
`p ≠ 0`, then `ord_∞(p(g)) = natDegree p · M` — the leading term strictly
dominates, so there is no cancellation. -/
theorem ordAtInfty_aeval_of_ord_eq {g : C.FunctionField} {M : ℤ}
    (hg : C.ordAtInfty g = ((M : ℤ) : WithTop ℤ)) (hM : M < 0)
    {p : Polynomial F} (hp : p ≠ 0) :
    C.ordAtInfty (Polynomial.aeval g p) =
      (((p.natDegree : ℤ) * M : ℤ) : WithTop ℤ) := by
  have hg_ne : g ≠ 0 :=
    (C.ordAtInfty_eq_top_iff g).not.mp (ne_of_eq_of_ne hg WithTop.coe_ne_top)
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  rcases Nat.eq_zero_or_pos p.natDegree with hd | hd
  · -- constant case: `p = C c`, `ord_∞ = 0 = 0·M`.
    have hc : p.coeff 0 ≠ 0 := by rw [← hd]; exact hlead
    have hRHS : (((p.natDegree : ℤ) * M : ℤ) : WithTop ℤ) = (0 : WithTop ℤ) := by
      rw [hd]; norm_num
    rw [hRHS]
    conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
    rw [Polynomial.aeval_C]
    exact C.ordAtInfty_algebraMap_F_nonzero hc
  · -- `d ≥ 1`: split off the leading term.
    have hlc_ne : algebraMap F C.FunctionField p.leadingCoeff ≠ 0 :=
      (map_ne_zero (algebraMap F C.FunctionField)).mpr hlead
    have h_split : Polynomial.aeval g p =
        Polynomial.aeval g p.eraseLead +
          algebraMap F C.FunctionField p.leadingCoeff * g ^ p.natDegree := by
      conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow p]
      rw [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    have h_lead_ord : C.ordAtInfty
        (algebraMap F C.FunctionField p.leadingCoeff * g ^ p.natDegree) =
        (((p.natDegree : ℤ) * M : ℤ) : WithTop ℤ) := by
      rw [C.ordAtInfty_mul hlc_ne (pow_ne_zero _ hg_ne),
        C.ordAtInfty_algebraMap_F_nonzero hlead,
        C.ord_pow_concrete hg_ne M _ hg, zero_add]
    have h_erase_ord : ((((p.natDegree : ℤ) - 1) * M : ℤ) : WithTop ℤ) ≤
        C.ordAtInfty (Polynomial.aeval g p.eraseLead) := by
      have hdeg : p.eraseLead.natDegree ≤ p.natDegree - 1 :=
        Polynomial.eraseLead_natDegree_le p
      have h := C.le_ordAtInfty_aeval hg hM p.eraseLead hdeg
      rwa [show (((p.natDegree - 1 : ℕ) : ℤ)) = ((p.natDegree : ℤ) - 1) by
        omega] at h
    have h_lt : C.ordAtInfty
        (algebraMap F C.FunctionField p.leadingCoeff * g ^ p.natDegree) <
        C.ordAtInfty (Polynomial.aeval g p.eraseLead) := by
      rw [h_lead_ord]
      refine lt_of_lt_of_le ?_ h_erase_ord
      have : ((p.natDegree : ℤ) - 1) * M = (p.natDegree : ℤ) * M - M := by ring
      exact_mod_cast (by rw [this]; linarith :
        (p.natDegree : ℤ) * M < ((p.natDegree : ℤ) - 1) * M)
    rw [h_split, add_comm, C.ordAtInfty_add_eq_of_lt h_lt]
    exact h_lead_ord

/-- A polynomial evaluated at an element of strictly negative order is nonzero
(its order is finite). -/
theorem aeval_ne_zero_of_ord_neg {g : C.FunctionField} {M : ℤ}
    (hg : C.ordAtInfty g = ((M : ℤ) : WithTop ℤ)) (hM : M < 0)
    {p : Polynomial F} (hp : p ≠ 0) :
    Polynomial.aeval g p ≠ 0 :=
  (C.ordAtInfty_eq_top_iff _).not.mp
    (ne_of_eq_of_ne (C.ordAtInfty_aeval_of_ord_eq hg hM hp) WithTop.coe_ne_top)

/-- Multiplying by a base-field constant cannot decrease `ord_∞` below a given
bound (the constant has order `0`, or the product vanishes). -/
theorem le_ordAtInfty_algebraMap_mul (c : F) {f : C.FunctionField}
    {b : WithTop ℤ} (hb : b ≤ C.ordAtInfty f) :
    b ≤ C.ordAtInfty (algebraMap F C.FunctionField c * f) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, zero_mul, C.ordAtInfty_zero]
    exact le_top
  rcases eq_or_ne f 0 with rfl | hf
  · rw [mul_zero, C.ordAtInfty_zero]
    exact le_top
  · have hc_ne : algebraMap F C.FunctionField c ≠ 0 :=
      (map_ne_zero (algebraMap F C.FunctionField)).mpr hc
    rw [C.ordAtInfty_mul hc_ne hf, C.ordAtInfty_algebraMap_F_nonzero hc,
      zero_add]
    exact hb

/-- **One-sided `y`-order bound from a Weierstrass-type equation**: if
`(X, Y)` satisfies `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` over the constant
field and `ord_∞ X = 2m` with `m ≤ -1`, then `ord_∞ Y ≥ 3m`.

The right side has order `≥ 6m`; if `ord_∞ Y = v < 3m`, then on the left side
the `Y²` term strictly dominates (`2v < 2m + v` and `2v < v`), so the left
side has order `2v < 6m` — a contradiction. -/
theorem le_ordAtInfty_y_of_weierstrass {X Y : C.FunctionField}
    {a₁ a₂ a₃ a₄ a₆ : F} {m : ℤ} (hm : m ≤ -1)
    (hX : C.ordAtInfty X = ((2 * m : ℤ) : WithTop ℤ))
    (h_eq : Y ^ 2 + algebraMap F C.FunctionField a₁ * X * Y +
        algebraMap F C.FunctionField a₃ * Y =
      X ^ 3 + algebraMap F C.FunctionField a₂ * X ^ 2 +
        algebraMap F C.FunctionField a₄ * X +
        algebraMap F C.FunctionField a₆) :
    ((3 * m : ℤ) : WithTop ℤ) ≤ C.ordAtInfty Y := by
  by_contra! hcon
  have hX_ne : X ≠ 0 :=
    (C.ordAtInfty_eq_top_iff X).not.mp (ne_of_eq_of_ne hX WithTop.coe_ne_top)
  -- `ord_∞ Y` is a finite integer `v < 3m`, and `Y ≠ 0`.
  obtain ⟨v, hv, hv_lt'⟩ := WithTop.lt_iff_exists_coe.mp hcon
  have hv_lt : v < 3 * m := by exact_mod_cast hv_lt'
  have hY_ne : Y ≠ 0 :=
    (C.ordAtInfty_eq_top_iff Y).not.mp (ne_of_eq_of_ne hv WithTop.coe_ne_top)
  -- the right side has order ≥ 6m
  have hX3 : C.ordAtInfty (X ^ 3) = ((6 * m : ℤ) : WithTop ℤ) :=
    (C.ord_pow_concrete hX_ne (2 * m) 3 hX).trans
      (WithTop.coe_inj.mpr (by push_cast; ring))
  have hX2 : C.ordAtInfty (X ^ 2) = ((4 * m : ℤ) : WithTop ℤ) :=
    (C.ord_pow_concrete hX_ne (2 * m) 2 hX).trans
      (WithTop.coe_inj.mpr (by push_cast; ring))
  have h_r2 : ((6 * m : ℤ) : WithTop ℤ) ≤ C.ordAtInfty
      (algebraMap F C.FunctionField a₂ * X ^ 2) :=
    C.le_ordAtInfty_algebraMap_mul a₂ (le_of_le_of_eq
      (by exact_mod_cast (by linarith : (6 * m : ℤ) ≤ 4 * m)) hX2.symm)
  have h_r3 : ((6 * m : ℤ) : WithTop ℤ) ≤ C.ordAtInfty
      (algebraMap F C.FunctionField a₄ * X) :=
    C.le_ordAtInfty_algebraMap_mul a₄ (le_of_le_of_eq
      (by exact_mod_cast (by linarith : (6 * m : ℤ) ≤ 2 * m)) hX.symm)
  have h_r4 : ((6 * m : ℤ) : WithTop ℤ) ≤ C.ordAtInfty
      (algebraMap F C.FunctionField a₆) := by
    rcases eq_or_ne a₆ 0 with rfl | h6
    · rw [map_zero, C.ordAtInfty_zero]
      exact le_top
    · rw [C.ordAtInfty_algebraMap_F_nonzero h6]
      exact_mod_cast (by linarith : (6 * m : ℤ) ≤ 0)
  have h_rhs : ((6 * m : ℤ) : WithTop ℤ) ≤ C.ordAtInfty
      (X ^ 3 + algebraMap F C.FunctionField a₂ * X ^ 2 +
        algebraMap F C.FunctionField a₄ * X +
        algebraMap F C.FunctionField a₆) := by
    have h12 := le_trans (le_min hX3.symm.le h_r2)
      (C.ordAtInfty_add_ge_min _ _)
    have h123 := le_trans (le_min h12 h_r3) (C.ordAtInfty_add_ge_min _ _)
    exact le_trans (le_min h123 h_r4) (C.ordAtInfty_add_ge_min _ _)
  -- the left side has order exactly `2v < 6m`
  have hY2 : C.ordAtInfty (Y ^ 2) = ((2 * v : ℤ) : WithTop ℤ) :=
    (C.ord_pow_concrete hY_ne v 2 hv).trans
      (WithTop.coe_inj.mpr (by push_cast; ring))
  have hXY : C.ordAtInfty (X * Y) = ((2 * m + v : ℤ) : WithTop ℤ) := by
    rw [C.ordAtInfty_mul hX_ne hY_ne, hX, hv, ← WithTop.coe_add]
  have h_t2 : ((2 * m + v : ℤ) : WithTop ℤ) ≤ C.ordAtInfty
      (algebraMap F C.FunctionField a₁ * X * Y) := by
    rw [mul_assoc]
    exact C.le_ordAtInfty_algebraMap_mul a₁ hXY.symm.le
  have h_t3 : ((v : ℤ) : WithTop ℤ) ≤ C.ordAtInfty
      (algebraMap F C.FunctionField a₃ * Y) :=
    C.le_ordAtInfty_algebraMap_mul a₃ hv.symm.le
  have hstep1 : C.ordAtInfty (Y ^ 2 +
      algebraMap F C.FunctionField a₁ * X * Y) =
      ((2 * v : ℤ) : WithTop ℤ) := by
    refine (C.ordAtInfty_add_eq_of_lt ?_).trans hY2
    rw [hY2]
    refine lt_of_lt_of_le ?_ h_t2
    exact_mod_cast (by linarith : 2 * v < 2 * m + v)
  have hstep2 : C.ordAtInfty (Y ^ 2 +
      algebraMap F C.FunctionField a₁ * X * Y +
      algebraMap F C.FunctionField a₃ * Y) =
      ((2 * v : ℤ) : WithTop ℤ) := by
    refine (C.ordAtInfty_add_eq_of_lt ?_).trans hstep1
    rw [hstep1]
    refine lt_of_lt_of_le ?_ h_t3
    exact_mod_cast (by linarith : 2 * v < v)
  rw [h_eq] at hstep2
  rw [hstep2] at h_rhs
  have : (6 * m : ℤ) ≤ 2 * v := by exact_mod_cast h_rhs
  linarith

end Curves.SmoothPlaneCurve

/-! ### The pullback of `[n]` on the `x`-subfield -/

open HasseWeil.Curves HasseWeil.Curves.SmoothPlaneCurve

variable {F : Type*} [Field F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

local notation "R" => W.toAffine.CoordinateRing
local notation "KE" => W.toAffine.FunctionField

/-- `[n]^*(x_gen) = mulByInt_x W n`, stated for `mulByInt_pullbackAlgHom`
directly (the `AlgHom` form of `mulByInt_pullback_x`). -/
theorem mulByInt_pullbackAlgHom_x_gen (n : ℤ) (hn : n ≠ 0) :
    mulByInt_pullbackAlgHom W n hn (x_gen W) = mulByInt_x W n := by
  classical
  have hpb : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn :=
    dif_neg hn
  exact hpb ▸ mulByInt_pullback_x W n hn

/-- `[n]^*(y_gen) = mulByInt_y W n`, stated for `mulByInt_pullbackAlgHom`
directly (the `AlgHom` form of `mulByInt_pullback_y`). -/
theorem mulByInt_pullbackAlgHom_y_gen (n : ℤ) (hn : n ≠ 0) :
    mulByInt_pullbackAlgHom W n hn (y_gen W) = mulByInt_y W n := by
  classical
  have hpb : (mulByInt W.toAffine n).pullback = mulByInt_pullbackAlgHom W n hn :=
    dif_neg hn
  exact hpb ▸ mulByInt_pullback_y W n hn

/-- `mulByInt_y W n ≠ 0`: it is the image of `y_gen ≠ 0` under the field
embedding `[n]^*`. -/
theorem mulByInt_y_ne_zero' (n : ℤ) (hn : n ≠ 0) : mulByInt_y W n ≠ 0 := by
  classical
  rw [← mulByInt_pullbackAlgHom_y_gen W n hn]
  exact (map_ne_zero (mulByInt_pullbackAlgHom W n hn)).mpr (y_gen_ne_zero W)

/-- `y_gen W` and `(W_smooth W).coordYInFunctionField` are the same element of
`KE`. -/
theorem y_gen_eq_coordYInFunctionField' :
    y_gen W = (W_smooth W).coordYInFunctionField := by
  classical
  exact (coordY_W_smooth_eq_y_gen W).symm.trans
    ((W_smooth W).coordY_eq_coordYInFunctionField)

/-- The pullback of a polynomial in `x`: `[n]^*(p(x)) = p(mulByInt_x W n)`.
The algebraMap factors through the coordinate ring, where the pullback is
`mulByInt_coordHom = AdjoinRoot.lift (mulByInt_xHom W n) …`, and on
`F[X]`-images `AdjoinRoot.lift` evaluates the first argument. -/
theorem mulByInt_pullbackAlgHom_algebraMap_polynomial (n : ℤ) (hn : n ≠ 0)
    (p : Polynomial F) :
    mulByInt_pullbackAlgHom W n hn (algebraMap (Polynomial F) KE p) =
      Polynomial.aeval (mulByInt_x W n) p := by
  rw [IsScalarTower.algebraMap_apply (Polynomial F) R KE p]
  change mulByInt_pullbackRingHom W n hn
    (algebraMap R KE (algebraMap (Polynomial F) R p)) = _
  rw [mulByInt_pullbackRingHom, IsLocalization.lift_eq]
  change mulByInt_coordHom W n hn (algebraMap (Polynomial F) R p) = _
  rw [show algebraMap (Polynomial F) R p =
      AdjoinRoot.of W.toAffine.polynomial p from rfl,
    mulByInt_coordHom, AdjoinRoot.lift_of]
  rw [mulByInt_xHom, Polynomial.aeval_def]
  rfl

/-- **Order transport for `F(x)`-elements under `[n]^*`**: for `r ∈ F(x)`
nonzero and `ord_∞(mulByInt_x W n) = M < 0`, there is `t ∈ ℤ` (the
`intDegree` of `r`) with `ord_∞ r = -2t` in `K(E)` and
`ord_∞([n]^* r) = t·M`. -/
theorem ord_mulByInt_pullback_algebraMap_fracPolyX (n : ℤ) (hn : n ≠ 0)
    {M : ℤ} (hM : (W_smooth W).ordAtInfty (mulByInt_x W n) = ((M : ℤ) : WithTop ℤ))
    (hMneg : M < 0) {r : FractionRing (Polynomial F)} (hr : r ≠ 0) :
    ∃ t : ℤ,
      (W_smooth W).ordAtInfty
        (algebraMap (FractionRing (Polynomial F)) KE r) =
        ((-2 * t : ℤ) : WithTop ℤ) ∧
      (W_smooth W).ordAtInfty
        (mulByInt_pullbackAlgHom W n hn
          (algebraMap (FractionRing (Polynomial F)) KE r)) =
        ((t * M : ℤ) : WithTop ℤ) := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := Polynomial F) r
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hpq
    exact hr hpq.symm
  -- the image of `r` in `K(E)` is the quotient of the two polynomial images
  have himg : algebraMap (FractionRing (Polynomial F)) KE r =
      algebraMap (Polynomial F) KE p / algebraMap (Polynomial F) KE q := by
    rw [← hpq, map_div₀,
      ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE,
      ← IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE]
  have haq_ne : algebraMap (Polynomial F) KE q ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (Polynomial F) (FractionRing (Polynomial F)) KE]
    intro h
    exact hq0 (FaithfulSMul.algebraMap_injective (Polynomial F)
      (FractionRing (Polynomial F))
      (((algebraMap (FractionRing (Polynomial F)) KE).injective
        (h.trans (map_zero _).symm)).trans (map_zero _).symm))
  refine ⟨(p.natDegree : ℤ) - (q.natDegree : ℤ), ?_, ?_⟩
  · -- source order: `-2·deg p - (-2·deg q) = -2t`
    have h := (W_smooth W).ord_div_concrete haq_ne
      (-2 * p.natDegree) (-2 * q.natDegree)
      ((W_smooth W).ordAtInfty_algebraMap_polynomial_of_ne_zero hp0)
      ((W_smooth W).ordAtInfty_algebraMap_polynomial_of_ne_zero hq0)
    rw [himg]
    exact h.trans (WithTop.coe_inj.mpr (by ring))
  · -- image order: `deg p · M - deg q · M = t·M`
    have hpb : mulByInt_pullbackAlgHom W n hn
        (algebraMap (FractionRing (Polynomial F)) KE r) =
        Polynomial.aeval (mulByInt_x W n) p /
          Polynomial.aeval (mulByInt_x W n) q := by
      rw [himg, map_div₀, mulByInt_pullbackAlgHom_algebraMap_polynomial,
        mulByInt_pullbackAlgHom_algebraMap_polynomial]
    have hq_img_ne : Polynomial.aeval (mulByInt_x W n) q ≠ 0 :=
      (W_smooth W).aeval_ne_zero_of_ord_neg hM hMneg hq0
    have h := (W_smooth W).ord_div_concrete hq_img_ne
      ((p.natDegree : ℤ) * M) ((q.natDegree : ℤ) * M)
      ((W_smooth W).ordAtInfty_aeval_of_ord_eq hM hMneg hp0)
      ((W_smooth W).ordAtInfty_aeval_of_ord_eq hM hMneg hq0)
    rw [hpb]
    exact h.trans (WithTop.coe_inj.mpr (by ring))

/-! ### The one-sided `y`-order bound from the curve equation -/

omit [W.toAffine.IsElliptic] in
private theorem le_ordAtInfty_zero' (b : WithTop ℤ) :
    b ≤ (W_smooth W).ordAtInfty (0 : KE) :=
  le_of_le_of_eq le_top ((W_smooth W).ordAtInfty_zero).symm

/-- **One-sided `y`-order bound**: if `ord_∞(mulByInt_x W n) = 2m` with
`m ≤ -1`, then `ord_∞(mulByInt_y W n) ≥ 3m` — **no** `(n : F) ≠ 0` hypothesis.

The pair `(mulByInt_x, mulByInt_y)` satisfies the Weierstrass equation
(`pullback_equation` + `mulByInt_pullback_x/y`), so the abstract bound
`le_ordAtInfty_y_of_weierstrass` applies. One-sided companion of
`ordAtInfty_mulByInt_y_eq_of_x` (`AdditionPullback/Frobenius.lean`, which is
`[Fintype K]`-scoped). -/
theorem le_ordAtInfty_mulByInt_y (n : ℤ) (hn : n ≠ 0) {m : ℤ} (hm : m ≤ -1)
    (hM : (W_smooth W).ordAtInfty (mulByInt_x W n) = ((2 * m : ℤ) : WithTop ℤ)) :
    ((3 * m : ℤ) : WithTop ℤ) ≤ (W_smooth W).ordAtInfty (mulByInt_y W n) := by
  classical
  -- the curve equation for `(mulByInt_x, mulByInt_y)`
  have h_eq : mulByInt_y W n ^ 2 +
        algebraMap F KE W.toAffine.a₁ * mulByInt_x W n * mulByInt_y W n +
        algebraMap F KE W.toAffine.a₃ * mulByInt_y W n =
      mulByInt_x W n ^ 3 +
        algebraMap F KE W.toAffine.a₂ * mulByInt_x W n ^ 2 +
        algebraMap F KE W.toAffine.a₄ * mulByInt_x W n +
        algebraMap F KE W.toAffine.a₆ := by
    have h_alg := pullback_equation W (mulByInt W.toAffine n)
    have hx_pb : (mulByInt W.toAffine n).pullback (x_gen W) = mulByInt_x W n := by
      change (mulByInt W.toAffine n).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (algebraMap (Polynomial F) W.toAffine.CoordinateRing Polynomial.X)) = _
      exact mulByInt_pullback_x W n hn
    have hy_pb : (mulByInt W.toAffine n).pullback (y_gen W) = mulByInt_y W n := by
      change (mulByInt W.toAffine n).pullback
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (AdjoinRoot.root W.toAffine.polynomial)) = _
      exact mulByInt_pullback_y W n hn
    rw [hx_pb, hy_pb] at h_alg
    rw [WeierstrassCurve.Affine.equation_iff] at h_alg
    exact h_alg
  exact (W_smooth W).le_ordAtInfty_y_of_weierstrass hm hM h_eq

/-! ### The basepoint condition -/

/-- **The `[n]`-pullback preserves regularity at infinity** (the basepoint
condition for `mulByInt`), for **every** `n ≠ 0` — including the inseparable
case `char F ∣ n`.

Route: `{1, y}`-parity decomposition of `f`, the dominant-term order transport
for the two `F(x)`-coefficients, the unconditional even `x`-order
`ord_∞(mulByInt_x) = 2m ≤ -2`, and the curve-equation bound
`ord_∞(mulByInt_y) ≥ 3m`. -/
theorem mulByInt_pullbackAlgHom_ordAtInfty_nonneg (n : ℤ) (hn : n ≠ 0)
    (f : KE) (hf : 0 ≤ (W_smooth W).ordAtInfty f) :
    0 ≤ (W_smooth W).ordAtInfty (mulByInt_pullbackAlgHom W n hn f) := by
  classical
  -- the even `x`-order `M = 2m ≤ -2`
  obtain ⟨M, hM, hMle, hMeven⟩ :=
    exists_ordAtInfty_mulByInt_x_eq_even_le_neg_two W n hn
  obtain ⟨m, hm2⟩ := hMeven
  have hMeq : M = 2 * m := by omega
  rw [hMeq] at hM hMle
  have hm_le : m ≤ -1 := by omega
  have hMneg : 2 * m < 0 := by omega
  -- decompose `f = r₁ + r₂·y_gen`
  obtain ⟨r₁, r₂, hf_decomp⟩ := (W_smooth W).exists_decomp f
  have hf_eq : f = algebraMap (FractionRing (Polynomial F)) KE r₁ +
      algebraMap (FractionRing (Polynomial F)) KE r₂ * y_gen W := by
    rw [hf_decomp, y_gen_eq_coordYInFunctionField' W, Algebra.smul_def, mul_one,
      Algebra.smul_def]
    rfl
  -- split the hypothesis through the parity/min formula
  have h_min : (W_smooth W).ordAtInfty f =
      min ((W_smooth W).ordAtInfty
            (algebraMap (FractionRing (Polynomial F)) KE r₁))
          ((W_smooth W).ordAtInfty
            (algebraMap (FractionRing (Polynomial F)) KE r₂) +
           (W_smooth W).ordAtInfty (y_gen W)) := by
    rw [hf_eq]
    exact (W_smooth W).ordAtInfty_basis_eq_min r₁ r₂
  rw [h_min, le_min_iff] at hf
  obtain ⟨hf1, hf2⟩ := hf
  rw [ordAtInfty_y_gen W] at hf2
  -- the image decomposition
  have himg : mulByInt_pullbackAlgHom W n hn f =
      mulByInt_pullbackAlgHom W n hn
        (algebraMap (FractionRing (Polynomial F)) KE r₁) +
      mulByInt_pullbackAlgHom W n hn
        (algebraMap (FractionRing (Polynomial F)) KE r₂) * mulByInt_y W n := by
    rw [hf_eq, map_add, map_mul, mulByInt_pullbackAlgHom_y_gen W n hn]
  rw [himg]
  refine le_trans (le_min ?_ ?_) ((W_smooth W).ordAtInfty_add_ge_min _ _)
  · -- the `F(x)`-part: `ord ≥ 0` transports to `ord ≥ 0`
    rcases eq_or_ne r₁ 0 with rfl | hr₁
    · rw [map_zero, map_zero]
      exact le_ordAtInfty_zero' W _
    · obtain ⟨t, hsrc, himg1⟩ :=
        ord_mulByInt_pullback_algebraMap_fracPolyX W n hn hM hMneg hr₁
      rw [hsrc] at hf1
      have ht : t ≤ 0 := by
        have : (0 : ℤ) ≤ -2 * t := by exact_mod_cast hf1
        linarith
      rw [himg1]
      have : (0 : ℤ) ≤ t * (2 * m) := by
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -t)
          (by linarith : (0:ℤ) ≤ -(2 * m))]
      exact_mod_cast this
  · -- the `y`-part: `ord ≥ 3` on the coefficient transports to `ord > 0`
    rcases eq_or_ne r₂ 0 with rfl | hr₂
    · rw [map_zero, map_zero, zero_mul]
      exact le_ordAtInfty_zero' W _
    · obtain ⟨t, hsrc, himg2⟩ :=
        ord_mulByInt_pullback_algebraMap_fracPolyX W n hn hM hMneg hr₂
      rw [hsrc] at hf2
      have ht : t ≤ -2 := by
        have h0 : (0 : WithTop ℤ) ≤ ((-2 * t + -3 : ℤ) : WithTop ℤ) := by
          rw [WithTop.coe_add]
          exact_mod_cast hf2
        have : (0 : ℤ) ≤ -2 * t + -3 := by exact_mod_cast h0
        omega
      have h_y := le_ordAtInfty_mulByInt_y W n hn hm_le hM
      have himg2_ne : mulByInt_pullbackAlgHom W n hn
          (algebraMap (FractionRing (Polynomial F)) KE r₂) ≠ 0 :=
        ((W_smooth W).ordAtInfty_eq_top_iff _).not.mp
          (ne_of_eq_of_ne himg2 WithTop.coe_ne_top)
      have hy_ne : mulByInt_y W n ≠ 0 :=
        mulByInt_y_ne_zero' W n hn
      have hmul := (W_smooth W).ordAtInfty_mul himg2_ne hy_ne
      rw [himg2] at hmul
      calc (0 : WithTop ℤ) ≤ ((t * (2 * m) + 3 * m : ℤ) : WithTop ℤ) := by
            have : (0 : ℤ) ≤ t * (2 * m) + 3 * m := by
              nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -2 - t)
                (by linarith : (0:ℤ) ≤ -(2 * m))]
            exact_mod_cast this
        _ = ((t * (2 * m) : ℤ) : WithTop ℤ) + ((3 * m : ℤ) : WithTop ℤ) := by
            rw [← WithTop.coe_add]
        _ ≤ ((t * (2 * m) : ℤ) : WithTop ℤ) +
              (W_smooth W).ordAtInfty (mulByInt_y W n) :=
            add_le_add le_rfl h_y
        _ = (W_smooth W).ordAtInfty
              (mulByInt_pullbackAlgHom W n hn
                (algebraMap (FractionRing (Polynomial F)) KE r₂) *
               mulByInt_y W n) := hmul.symm

namespace EC

variable {F : Type*} [Field F]

/-- **`MulByIntBasepoint W hn` holds for every `n ≠ 0`** — the keystone
residual of `IsogenyAG.lean`. No separability hypothesis: the inseparable case
`char F ∣ n` is included (the even `x`-order is `2m ≤ -2` rather than `-2`,
and all bounds are one-sided). -/
theorem mulByIntBasepoint_holds (W : Affine F) [W.IsElliptic] {n : ℤ}
    (hn : n ≠ 0) : MulByIntBasepoint W hn :=
  fun f hf ↦ mulByInt_pullbackAlgHom_ordAtInfty_nonneg (W := W) n hn f hf

/-- **`[n]` as an `EC.Isogeny`, witness-free** (Silverman III.4): the
basepoint condition is now a theorem (`mulByIntBasepoint_holds`), so the
multiplication-by-`n` isogeny exists unconditionally for `n ≠ 0`. -/
noncomputable def Isogeny.mulByInt (W : Affine F) [W.IsElliptic] {n : ℤ}
    (hn : n ≠ 0) : Isogeny W W :=
  Isogeny.mulByIntOfBasepoint W hn (mulByIntBasepoint_holds W hn)

@[simp] theorem Isogeny.mulByInt_pullback (W : Affine F) [W.IsElliptic]
    {n : ℤ} (hn : n ≠ 0) (f : W.FunctionField) :
    (Isogeny.mulByInt W hn).toCurveMap.pullback f =
      HasseWeil.mulByInt_pullbackAlgHom W n hn f := rfl

end EC

end HasseWeil
