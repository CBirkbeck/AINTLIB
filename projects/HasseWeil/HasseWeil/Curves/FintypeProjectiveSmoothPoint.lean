/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Curves.PicZero
import HasseWeil.Frobenius

/-!
# `Fintype` instance for `ProjectiveSmoothPoint`

The projective smooth points on `W : WeierstrassCurve F` are in canonical
bijection with `W.toAffine.Point`:

* `0 : W.toAffine.Point` ↔ `ProjectiveSmoothPoint.infinity`
* `Point.some x y h` ↔ `ProjectiveSmoothPoint.affine ⟨x, y, h⟩`

The bridge `Affine.Point.toProjectiveSmoothPoint` (`Curves/PicZero.lean:136`)
and its inverse `ProjectiveSmoothPoint.toAffinePoint` (`Curves/PicZero.lean:44`)
realise this bijection. The round-trip `toProjectiveSmoothPoint_toAffinePoint`
is shipped in `PicZero.lean:153`; the reverse round-trip is shipped here.

As a corollary, `Fintype W.toAffine.Point` (which the project supplies via
the `pointCount` machinery) transports to `Fintype (ProjectiveSmoothPoint
⟨W.toAffine⟩)`, and the two cardinalities agree:

  `Fintype.card (ProjectiveSmoothPoint ⟨W.toAffine⟩) = pointCount W.toAffine`

(NO `+1`: `W.toAffine.Point` already includes the basepoint `0` corresponding
to the point at infinity.)

## References
* Silverman, *The Arithmetic of Elliptic Curves*, II.3 (projective closure).
-/

open HasseWeil.Curves

namespace HasseWeil

variable {F : Type*} [Field F]
variable (W : WeierstrassCurve F)

/-! ### Reverse round-trip for the projective ↔ affine bridge -/

/-- Round-trip in the other direction: pushing a `ProjectiveSmoothPoint`
to an `Affine.Point` and back recovers the original. Companion to
`Affine.Point.toProjectiveSmoothPoint_toAffinePoint` (`PicZero.lean:153`). -/
@[simp] theorem ProjectiveSmoothPoint.toAffinePoint_toProjectiveSmoothPoint
    (P : ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :
    P.toAffinePoint.toProjectiveSmoothPoint = P := by
  cases P with
  | infinity => rfl
  | affine Q => rfl

/-! ### `Equiv` between `W.toAffine.Point` and `ProjectiveSmoothPoint` -/

/-- The canonical equivalence between `W.toAffine.Point` (mathlib's inductive
type of affine points + basepoint) and `ProjectiveSmoothPoint` (the project's
projective closure with `affine | infinity` constructors). -/
noncomputable def Affine.Point.equivProjectiveSmoothPoint :
    W.toAffine.Point ≃ ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F) where
  toFun := WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint
  invFun := ProjectiveSmoothPoint.toAffinePoint
  left_inv := WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint
  right_inv :=
    ProjectiveSmoothPoint.toAffinePoint_toProjectiveSmoothPoint W

/-! ### `Fintype` instance + cardinality -/

/-- `ProjectiveSmoothPoint (⟨W.toAffine⟩)` inherits a `Fintype` structure
from `W.toAffine.Point` via the bijection above. -/
noncomputable instance instFintypeProjectiveSmoothPoint
    [Fintype W.toAffine.Point] :
    Fintype (ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F)) :=
  Fintype.ofEquiv W.toAffine.Point (Affine.Point.equivProjectiveSmoothPoint W)

/-- The cardinality of `ProjectiveSmoothPoint (⟨W.toAffine⟩)` equals
`pointCount W.toAffine`. NO `+1`: the basepoint `0 : W.toAffine.Point` is
in bijection with `ProjectiveSmoothPoint.infinity`, so both sides count
the point at infinity once. -/
theorem Fintype.card_projectiveSmoothPoint_eq_pointCount
    [Fintype W.toAffine.Point] :
    Fintype.card (ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F)) =
      pointCount W.toAffine := by
  unfold pointCount
  exact Fintype.card_congr (Affine.Point.equivProjectiveSmoothPoint W).symm

end HasseWeil
