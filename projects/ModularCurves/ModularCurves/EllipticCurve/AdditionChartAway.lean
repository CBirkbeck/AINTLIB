/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.AdditionChartDomain
import ModularCurves.EllipticCurve.AdditionChartHom

/-!
# The addition laws as chart morphisms on the localized chart-product (T-W7.0c-c5β, β3)

Instantiating `chartHomOfTriple` (β3's ring core) at

  `S := Localization.Away (lawTwoTriple W i j k)`   over   `A := biChartRing W i j`,

whose on-curve hypothesis is `equation_lawTwoTriple_of_isDomain` (β2b) and whose invertibility
hypothesis is `IsLocalization.Away.mul_invSelf`. The result, `addOnYPieceHom`, is the `k`-th
piece of `addOnY` on the `(i,j)` chart-product; `addOnZPieceHom` is the same for mathlib's
`addXYZ` (law 1). Applying `Spec` and composing with `Proj.awayι` gives the chart morphisms
themselves; β1's `chartPieceIso` identifies the source with an open of `E ×_R E`.
-/

open MvPolynomial ModularCurves

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i j k : Fin 3)

/-- The image of a chart-product triple in the localization inverting its `k`-th coordinate. -/
noncomputable def awayTriple (t : Fin 3 → biChartRing W i j) :
    Fin 3 → Localization.Away (t k) :=
  fun m => algebraMap (biChartRing W i j) (Localization.Away (t k)) (t m)

/-- The `k`-th coordinate becomes invertible, with the localization's own inverse. -/
lemma awayTriple_mul_invSelf (t : Fin 3 → biChartRing W i j) :
    awayTriple W i j k t k * IsLocalization.Away.invSelf (t k) = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- An on-curve triple stays on the curve in the localization. -/
lemma equation_awayTriple (t : Fin 3 → biChartRing W i j)
    (ht : (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation t) :
    (W.map (algebraMap R (Localization.Away (t k)))).toProjective.Equation
      (awayTriple W i j k t) := by
  have h := ht.map (algebraMap (biChartRing W i j) (Localization.Away (t k)))
  have hmap : (W.map (algebraMap R (biChartRing W i j))).map
      (algebraMap (biChartRing W i j) (Localization.Away (t k))) =
      W.map (algebraMap R (Localization.Away (t k))) := by
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
  exact hmap ▸ h

/-- **(β3)** The `k`-th chart morphism of the second Bosma–Lenstra law on the `(i,j)`
chart-product: the chart ring of the model maps to the localization of the chart-product ring
inverting the law's `k`-th coordinate, sending `X m / X k` to `t m / t k`. -/
noncomputable def addOnYPieceHom [IsJacobsonRing R] [IsDomain (biChartRing W i j)]
    (hΔ : IsUnit W.Δ) :
    chartAway W k →ₐ[R] Localization.Away (lawTwoTriple W i j k) :=
  chartAwayHomOfTriple W k (awayTriple W i j k (lawTwoTriple W i j))
    (IsLocalization.Away.invSelf (lawTwoTriple W i j k))
    (awayTriple_mul_invSelf W i j k _)
    (equation_awayTriple W i j k _ (equation_lawTwoTriple_of_isDomain W i j hΔ))

/-- **(β3)** The same for mathlib's addition law `addXYZ` (law 1) — the `k`-th chart morphism
of `addOnZ` on the `(i,j)` chart-product. -/
noncomputable def addOnZPieceHom [IsJacobsonRing R] [IsDomain (biChartRing W i j)]
    (hΔ : IsUnit W.Δ) :
    chartAway W k →ₐ[R] Localization.Away (lawOneTriple W i j k) :=
  chartAwayHomOfTriple W k (awayTriple W i j k (lawOneTriple W i j))
    (IsLocalization.Away.invSelf (lawOneTriple W i j k))
    (awayTriple_mul_invSelf W i j k _)
    (equation_awayTriple W i j k _ (equation_lawOneTriple_of_isDomain W i j hΔ))

end WeierstrassCurve.Projective
