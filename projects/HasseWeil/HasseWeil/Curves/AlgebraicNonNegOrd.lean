/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Divisors
import Mathlib.RingTheory.Valuation.Integral

/-!
# Algebraic elements have nonnegative order at every smooth point

For a smooth plane curve `C` over a field `F` and a smooth point `P ∈ C`,
the additive valuation `ord_P : F(C) → WithTop ℤ` satisfies:

```
f algebraic over F ⟹ 0 ≤ ord_P f.
```

This is the **algebraic-Liouville** inequality at a finite place. Its
contrapositive is the standard transcendence-from-pole criterion: if `f`
has a *negative* order at any single place trivial on `F`, then `f` is
transcendental over `F`. This avoids needing the global "constant field of
`F(C)` is `F`" theorem.

## Main result

* `SmoothPlaneCurve.ord_P_nonneg_of_isAlgebraic` — the algebraic-Liouville
  inequality at every finite smooth point.
* `SmoothPlaneCurve.transcendental_of_neg_ord_P` — contrapositive
  transcendence criterion.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, II.1 (algebraic Liouville).
-/

open WeierstrassCurve Polynomial

namespace HasseWeil.Curves

namespace SmoothPlaneCurve

variable {F : Type*} [Field F] {C : SmoothPlaneCurve F}

/-- Every element of `F` (lifted to `F(C)` via the algebra map) has
`pointValuation ≤ 1`, i.e. lives in the valuation ring at every smooth
point. Direct from `pointValuation_algebraMap_le_one` via the scalar
tower. -/
theorem pointValuation_algebraMap_F_le_one
    (P : C.SmoothPoint) (c : F) :
    C.pointValuation P (algebraMap F C.FunctionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField c]
  exact C.pointValuation_algebraMap_le_one _ P

/-- **Algebraic-Liouville inequality at a finite place** (Silverman II.1):
every element of `F(C)` algebraic over `F` has nonnegative order at every
smooth point `P ∈ C`.

Proof: let `O := (pointValuation P).integer` be the valuation ring at `P`.
Since constants from `F` map into `O`
(`pointValuation_algebraMap_F_le_one`), any monic witness polynomial for
`f` over `F` lifts to a monic polynomial over `O` evaluating to zero at
`f`. Hence `f` is integral over `O`, and by Mathlib's
`Valuation.Integers.isIntegral_iff_v_le_one`, `pointValuation P f ≤ 1`,
which translates to `0 ≤ ord_P P f`. -/
theorem ord_P_nonneg_of_isAlgebraic
    (P : C.SmoothPoint) {f : C.FunctionField}
    (h_alg : IsAlgebraic F f) :
    (0 : WithTop ℤ) ≤ C.ord_P P f := by
  -- The ring hom `φ : F → (pointValuation P).integer` corestricting the
  -- algebra map, valid because constants land in the valuation ring.
  let φ : F →+* (C.pointValuation P).integer :=
    (algebraMap F C.FunctionField).codRestrict (C.pointValuation P).integer
      (C.pointValuation_algebraMap_F_le_one P)
  obtain ⟨p, hp_monic, hp_eval⟩ : IsIntegral F f := h_alg.isIntegral
  have h_int_O : IsIntegral (C.pointValuation P).integer f := by
    refine ⟨p.map φ, hp_monic.map _, ?_⟩
    change (Polynomial.aeval f) (p.map φ) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact hp_eval
  have h_v_le : C.pointValuation P f ≤ 1 :=
    (Valuation.integer.integers (C.pointValuation P)).isIntegral_iff_v_le_one.mp h_int_O
  by_cases hf : f = 0
  · rw [hf, ord_P_zero]; exact le_top
  · have hv : C.pointValuation P f ≠ 0 := (C.pointValuation P).ne_zero_iff.mpr hf
    unfold ord_P
    rw [dif_neg hv, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
      WithTop.coe_le_coe]
    -- The order is `-toAdd (unzero hv)`, so `≤ 1` for the valuation becomes
    -- `toAdd (unzero hv) ≤ toAdd 1 = 0`, giving `0 ≤ -toAdd (unzero hv)`.
    have h_unz_le : WithZero.unzero hv ≤ 1 := by
      rw [← WithZero.coe_le_coe, WithZero.coe_one, WithZero.coe_unzero]; exact h_v_le
    have h_toAdd : (WithZero.unzero hv).toAdd ≤ 0 := Multiplicative.toAdd_le.mpr h_unz_le
    omega

/-- **Transcendence-from-pole criterion**: if `f ∈ F(C)` has *negative*
order at any single smooth point `P ∈ C`, then `f` is transcendental over
`F`. The contrapositive of `ord_P_nonneg_of_isAlgebraic`. -/
theorem transcendental_of_neg_ord_P
    {P : C.SmoothPoint} {f : C.FunctionField}
    (h_neg : C.ord_P P f < 0) :
    Transcendental F f := by
  intro h_alg
  exact absurd (C.ord_P_nonneg_of_isAlgebraic P h_alg) (not_le.mpr h_neg)

end SmoothPlaneCurve

end HasseWeil.Curves
