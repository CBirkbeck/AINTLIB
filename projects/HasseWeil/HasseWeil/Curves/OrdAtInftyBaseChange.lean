/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.Infinity
import HasseWeil.Curves.CurveMapBaseChange
import HasseWeil.Curves.IntegralClosure

/-!
# Base change of the order at infinity (Silverman I.2 + IV.1)

For a smooth plane curve `C / K` and a field extension `L / K`, the order at the point at infinity
is preserved by the function-field base change `functionFieldMap : K(C) → L(C_L)`:

  `ord_∞^{L}(functionFieldMap z) = ord_∞^{K} z`   (for `z ≠ 0`).

Geometrically `O ∈ C(K)` is a `K`-rational point, so it stays rational (`e = 1`) over `L` and the
pole/zero order at `O` is unchanged.  Concretely, `ord_∞(f) = -intDegree (N(f))` (the algebra
norm `N : K(C) → K(X)`, `Curves/Infinity.lean`); this file proves the two-step base-change identity:

1. **Norm transport** (`norm_coordRingMap`): for an integral element `u ∈ K[C]`,
   `N_{L[X]}(coordRingMap u) = (N_{K[X]} u).map (algebraMap K L)`.  Proved from mathlib's *explicit*
   coordinate-ring norm formula `norm_smul_basis`
   (`N(p·1 + q·y) = p² − pq(a₁X+a₃) − q²(X³+a₂X²+a₄X+a₆)`) — a polynomial identity commuting with
   the coefficient map `K[X] → L[X]` (the `aᵢ` base-change as `algebraMap K L aᵢ`).
2. **Degree preservation**: `natDegree` is unchanged under the injective coefficient map `K → L`
   (`Polynomial.natDegree_map_eq_of_injective`).

Reducing a general `z = algebraMap u / algebraMap v` (`IsFractionRing.div_surjective`) through
`ordAtInfty_div_eq_mul_inv` / `ordAtInfty_inv` and the integral transport then gives the result.

This is the infinity analogue of the affine `pointValuation` / omega-coefficient base-change
transports; it discharges the `OrdAtInftyBaseChange` leaf of the `(1 − π)_{K̄}` infinity third.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, I.2 (base change), IV.1 (`ord_∞`).
-/

open WeierstrassCurve

namespace HasseWeil.Curves.SmoothPlaneCurve

variable {K : Type*} [Field K] (C : SmoothPlaneCurve K)
variable (L : Type*) [Field L] [Algebra K L]

set_option linter.style.longLine false

/-- `coordRingMap` on the `K[X]`-basis decomposition `p • 1 + q • y`: it sends the coefficients
`p, q` through `Polynomial.map (algebraMap K L)` and fixes the basis `{1, y}`. -/
theorem coordRingMap_smul_basis (p q : Polynomial K) :
    C.coordRingMap L (p • (1 : C.CoordinateRing) +
        q • WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Polynomial.X) =
      (p.map (algebraMap K L)) • (1 : (C.baseChange L).CoordinateRing) +
        (q.map (algebraMap K L)) •
          WeierstrassCurve.Affine.CoordinateRing.mk (C.baseChange L).toAffine Polynomial.X := by
  change WeierstrassCurve.Affine.CoordinateRing.map C.toAffine (algebraMap K L) _ = _
  rw [map_add, WeierstrassCurve.Affine.CoordinateRing.map_smul,
    WeierstrassCurve.Affine.CoordinateRing.map_smul, map_one]
  congr 2
  rw [WeierstrassCurve.Affine.CoordinateRing.map_mk, Polynomial.map_X]; rfl

/-- **Norm transport** (the explicit-formula form): for `u ∈ K[C]`,
`N_{L[X]}(coordRingMap u) = (N_{K[X]} u).map (algebraMap K L)`.  Both sides are the explicit
`norm_smul_basis` polynomial in the basis coefficients; the identity commutes with the coefficient
map because the Weierstrass coefficients base-change as `algebraMap K L aᵢ`. -/
theorem norm_coordRingMap (u : C.CoordinateRing) :
    Algebra.norm (Polynomial L) (C.coordRingMap L u) =
      (Algebra.norm (Polynomial K) u).map (algebraMap K L) := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq u
  rw [coordRingMap_smul_basis, WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis,
    WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_C, Polynomial.map_X, SmoothPlaneCurve.baseChange_a₁,
    SmoothPlaneCurve.baseChange_a₂, SmoothPlaneCurve.baseChange_a₃,
    SmoothPlaneCurve.baseChange_a₄, SmoothPlaneCurve.baseChange_a₆]

/-- `ord_∞` of an integral element transports: `ord_∞^{L}(algebraMap (coordRingMap u)) =
ord_∞^{K}(algebraMap u)`.  Via `ordAtInfty_algebraMap_coordinateRing` (`ord = -natDegree(N)`), the
norm transport, and `natDegree` preservation under the injective `algebraMap K L`. -/
theorem ordAtInfty_algebraMap_coordRingMap (u : C.CoordinateRing) :
    (C.baseChange L).ordAtInfty
        (algebraMap (C.baseChange L).CoordinateRing (C.baseChange L).FunctionField
          (C.coordRingMap L u)) =
      C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField u) := by
  by_cases hu : u = 0
  · subst hu; simp
  · have hcu : C.coordRingMap L u ≠ 0 := fun h =>
      hu ((C.coordRingMap_injective L) (by rw [h, map_zero]))
    rw [(C.baseChange L).ordAtInfty_algebraMap_coordinateRing _ hcu,
      C.ordAtInfty_algebraMap_coordinateRing _ hu, norm_coordRingMap,
      Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective K L)]

/-- **Base change of the order at infinity** (Silverman I.2 + IV.1): for nonzero `z ∈ K(C)`,
`ord_∞^{L}(functionFieldMap z) = ord_∞^{K} z`.  Decompose `z = algebraMap u / algebraMap v`
(`IsFractionRing.div_surjective`); both orders split as
`ord(algebraMap u) − ord(algebraMap v)` (`ordAtInfty_div_eq_mul_inv` / `ordAtInfty_inv`); each
integral order transports by `ordAtInfty_algebraMap_coordRingMap`, and `functionFieldMap` commutes
with `algebraMap` and `/` (`functionFieldMap_algebraMap`, `map_div₀`). -/
theorem ordAtInfty_functionFieldMap (z : C.FunctionField) (hz : z ≠ 0) :
    (C.baseChange L).ordAtInfty (C.functionFieldMap L z) = C.ordAtInfty z := by
  obtain ⟨u, v, hv_nzd, heq⟩ := IsFractionRing.div_surjective (A := C.CoordinateRing) z
  have hv_ne : v ≠ 0 := nonZeroDivisors.ne_zero hv_nzd
  have hv_map_ne : algebraMap C.CoordinateRing C.FunctionField v ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C.CoordinateRing C.FunctionField)).mpr hv_ne
  have hu_ne : u ≠ 0 := by
    intro h; exact hz (by rw [← heq, h, map_zero, zero_div])
  have hu_map_ne : algebraMap C.CoordinateRing C.FunctionField u ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective C.CoordinateRing C.FunctionField)).mpr hu_ne
  rw [← heq, C.ordAtInfty_div_eq_mul_inv _ hu_map_ne hv_map_ne, C.ordAtInfty_inv]
  rw [map_div₀, SmoothPlaneCurve.functionFieldMap_algebraMap,
    SmoothPlaneCurve.functionFieldMap_algebraMap]
  have hcu_map_ne : algebraMap (C.baseChange L).CoordinateRing (C.baseChange L).FunctionField
      (C.coordRingMap L u) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h => hu_ne ((C.coordRingMap_injective L) (by rw [h, map_zero])))
  have hcv_map_ne : algebraMap (C.baseChange L).CoordinateRing (C.baseChange L).FunctionField
      (C.coordRingMap L v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (fun h => hv_ne ((C.coordRingMap_injective L) (by rw [h, map_zero])))
  rw [(C.baseChange L).ordAtInfty_div_eq_mul_inv _ hcu_map_ne hcv_map_ne,
    (C.baseChange L).ordAtInfty_inv,
    ordAtInfty_algebraMap_coordRingMap, ordAtInfty_algebraMap_coordRingMap]

end HasseWeil.Curves.SmoothPlaneCurve
