import HasseWeil.Pic0.RouteCGeometric

/-!
# Route C (geometric): discharging the `hcompat` residual from the construction

This file discharges (in part) the `hcompat` residual carried by
`degree_eq_N_via_picDual_geometric_v3` (`HasseWeil/Pic0/RouteCGeometric.lean`).

## What `hcompat` is

For the genuine `r·π − s·id` isogeny `α := genuineIsogSmulSub W r s …` (a
`HasseWeil.Isogeny`, whose `toAddMonoidHom` and `pullback` are **independent**
stored fields, `HasseWeil/Basic.lean`), `hcompat` is the per-rational-point
identification of the **stored** additive point map with the **geometric**
comorphism image:

```
α.toAddMonoidHom (some x y h)
  = (CurveMap.toPointMap coordHom ⟨x, y, h⟩).toAffinePoint
```

where `coordHom : φ.CoordHom` is a `CurveMap` coordinate-ring witness with
`coordHom.toAlgHom = ch.toAlgHom` (`ch : α.CoordHom`).  The geometric image has
coordinates `evalAt ⟨x,y,h⟩ (coordHom.toAlgHom (mk (C X)))` and
`evalAt ⟨x,y,h⟩ (coordHom.toAlgHom (mk Y))` (`CurveMap.toPointMap`,
`PointFunctor.lean`).

## What ships here

* **Frobenius building block (`frobeniusIsog_toPointMap_compat`):** for the
  Frobenius isogeny `frobeniusIsog W` — whose stored `toAddMonoidHom` is the
  identity and whose pullback `f ↦ f^q` **does** restrict to the coordinate ring
  (`frobeniusAlgHom K R`) — the geometric comorphism image of a `K`-rational
  point `(x, y)` is `(x^q, y^q) = (x, y)` (`FiniteField.pow_card`), matching the
  stored identity map.  This is the `hcompat` identity for the building block,
  proven completely and axiom-clean.

The `mulByInt` and `addIsog`/`addPullbackAlgHomPair` blocks, and their
composition into `genuineIsogSmulSub`, are tracked as the precise residual (see
the module note at the end of the file).
-/

open WeierstrassCurve
open scoped nonZeroDivisors

namespace HasseWeil.Pic0.RouteCGeometric

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### Frobenius building block

The Frobenius isogeny `frobeniusIsog W` (`HasseWeil/Frobenius.lean`) has:
* stored `toAddMonoidHom = AddMonoidHom.id` (Frobenius is the identity on
  `K`-rational points, since `x^q = x`);
* `pullback = frobeniusAlgHom K K(E)` (`f ↦ f^q`), which restricts to the
  coordinate ring `R := E.CoordinateRing` as `frobeniusAlgHom K R`.

We package the function-field pullback as a `CurveMap` and its coordinate-ring
restriction as the canonical `CoordHom`, then verify the `hcompat` identity. -/

/-- The `CurveMap` underlying `frobeniusIsog W`: its pullback is the Frobenius
algebra hom `f ↦ f^q` on the function field. -/
noncomputable def frobeniusCurveMap :
    HasseWeil.Curves.CurveMap ⟨W.toAffine⟩ ⟨W.toAffine⟩ where
  pullback := FiniteField.frobeniusAlgHom K W.toAffine.FunctionField

@[simp] theorem frobeniusCurveMap_pullback :
    (frobeniusCurveMap W).pullback =
      FiniteField.frobeniusAlgHom K W.toAffine.FunctionField := rfl

/-- The canonical coordinate-ring witness for the Frobenius curve map: Frobenius
`f ↦ f^q` restricts to `R := E.CoordinateRing` (since `R^q ⊆ R`), and the
algebra map `R → K(E)` commutes with `q`-th powers. -/
noncomputable def frobeniusCurveMapCoordHom :
    (frobeniusCurveMap W).CoordHom where
  toAlgHom := FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing
  compat := fun u => by
    change FiniteField.frobeniusAlgHom K W.toAffine.FunctionField
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField u) =
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing u)
    simp only [FiniteField.coe_frobeniusAlgHom, map_pow]

@[simp] theorem frobeniusCurveMapCoordHom_toAlgHom :
    (frobeniusCurveMapCoordHom W).toAlgHom =
      FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing := rfl

set_option maxHeartbeats 800000 in
/-- **Frobenius geometric image at a rational point is the identity.** The image
of `(x, y) ∈ W(K)` under the Frobenius comorphism `CurveMap.toPointMap` has
coordinates `(x^q, y^q) = (x, y)` by `FiniteField.pow_card`.  Hence the geometric
point map equals the source point. -/
theorem frobeniusCurveMap_toPointMap (x y : K) (h : W.toAffine.Nonsingular x y) :
    HasseWeil.Curves.CurveMap.toPointMap (frobeniusCurveMapCoordHom W)
        (⟨x, y, h⟩ :
          (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve K).SmoothPoint) =
      ⟨x, y, h⟩ := by
  ext
  · -- x-coordinate: evalAt ⟨x,y,h⟩ (frob (mk (C X))) = x^q = x.
    change HasseWeil.Curves.CurveMap.evalAtPullback (frobeniusCurveMapCoordHom W)
      (⟨x, y, h⟩ : (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve K).SmoothPoint)
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C Polynomial.X)) = x
    rw [HasseWeil.Curves.CurveMap.evalAtPullback_apply]
    change HasseWeil.Curves.SmoothPlaneCurve.evalAt
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve K) ⟨x, y, h⟩
      (FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing
        (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
          (Polynomial.C Polynomial.X))) = x
    rw [show (FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing)
        (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
          (Polynomial.C Polynomial.X)) =
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.C Polynomial.X)) ^ Fintype.card K from
        congr_fun (FiniteField.coe_frobeniusAlgHom (K := K)
          (R := W.toAffine.CoordinateRing)) _,
      map_pow, HasseWeil.Curves.SmoothPlaneCurve.evalAt_x, FiniteField.pow_card]
  · -- y-coordinate: evalAt ⟨x,y,h⟩ (frob (mk Y)) = y^q = y.
    change HasseWeil.Curves.CurveMap.evalAtPullback (frobeniusCurveMapCoordHom W)
      (⟨x, y, h⟩ : (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve K).SmoothPoint)
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.X (R := Polynomial K))) = y
    rw [HasseWeil.Curves.CurveMap.evalAtPullback_apply]
    change HasseWeil.Curves.SmoothPlaneCurve.evalAt
      (⟨W.toAffine⟩ : HasseWeil.Curves.SmoothPlaneCurve K) ⟨x, y, h⟩
      (FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing
        (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
          (Polynomial.X (R := Polynomial K)))) = y
    rw [show (FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing)
        (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
          (Polynomial.X (R := Polynomial K))) =
      (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
        (Polynomial.X (R := Polynomial K))) ^ Fintype.card K from
        congr_fun (FiniteField.coe_frobeniusAlgHom (K := K)
          (R := W.toAffine.CoordinateRing)) _,
      map_pow, HasseWeil.Curves.SmoothPlaneCurve.evalAt_y, FiniteField.pow_card]

/-- **Frobenius `hcompat` building block.** The stored additive point map of
`frobeniusIsog W` (the identity on `K`-rational points) agrees with the geometric
comorphism image `CurveMap.toPointMap (frobeniusCurveMapCoordHom W)`.  This is the
`hcompat`-shaped identity for the Frobenius building block of `genuineIsogSmulSub`.

Proven completely: the LHS is `some x y h` (`frobeniusIsog.toAddMonoidHom = id`);
the RHS is the geometric image, which equals `some x y h` by
`frobeniusCurveMap_toPointMap`. -/
theorem frobeniusIsog_toPointMap_compat (x y : K) (h : W.toAffine.Nonsingular x y) :
    (frobeniusIsog W).toAddMonoidHom (WeierstrassCurve.Affine.Point.some x y h) =
      (HasseWeil.Curves.CurveMap.toPointMap (frobeniusCurveMapCoordHom W)
        (⟨x, y, h⟩ :
          (⟨W.toAffine⟩ :
            HasseWeil.Curves.SmoothPlaneCurve K).SmoothPoint)).toAffinePoint := by
  rw [frobeniusCurveMap_toPointMap]
  -- `frobeniusIsog.toAddMonoidHom = AddMonoidHom.id`, so LHS = `some x y h`; RHS is `toAffinePoint`.
  rfl

end HasseWeil.Pic0.RouteCGeometric
