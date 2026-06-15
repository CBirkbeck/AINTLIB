import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Smooth plane curves

This file sets up the minimal foundation for Silverman chapter II
(`.mathlib-quality/tickets/` stream A). It provides `SmoothPlaneCurve F` as a
thin wrapper over mathlib's `WeierstrassCurve.Affine F`, together with
associated notions of smooth points, coordinate ring, and function field.

A future refactor (tracked by `T-II-1-001`) will generalize
`SmoothPlaneCurve` to arbitrary irreducible polynomials in `F[X, Y]` and
prove that the local ring at a smooth point is a discrete valuation ring.
For now, the Weierstrass case is enough to state and develop divisors,
differentials, and the other chapter-II concepts that the Hasse–Weil proof
needs downstream.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.1
-/

namespace HasseWeil.Curves

/-- A smooth plane curve over a field `F`. At present this is a thin wrapper
over a mathlib `WeierstrassCurve.Affine F`; the long-term plan (tracked by
ticket `T-II-1-001`) is to generalize this to an arbitrary irreducible
polynomial in `F[X, Y]`. -/
structure SmoothPlaneCurve (F : Type*) [Field F] where
  /-- The underlying affine Weierstrass curve. -/
  toAffine : WeierstrassCurve.Affine F

namespace SmoothPlaneCurve

variable {F : Type*} [Field F]

/-- The coordinate ring `F[C] := F[X, Y] / ⟨p⟩` of a smooth plane curve. -/
noncomputable abbrev CoordinateRing (C : SmoothPlaneCurve F) : Type _ :=
  C.toAffine.CoordinateRing

/-- The function field `F(C) := Frac(F[C])` of a smooth plane curve. -/
noncomputable abbrev FunctionField (C : SmoothPlaneCurve F) : Type _ :=
  C.toAffine.FunctionField

/-- A smooth point on a plane curve: coordinates `(x, y)` satisfying the
defining equation together with the nonsingularity condition (at least one
partial derivative nonvanishing at the point).
Reference: Silverman II.1 (smooth point of a curve). -/
@[ext]
structure SmoothPoint (C : SmoothPlaneCurve F) where
  /-- The `X`-coordinate of the smooth point. -/
  x : F
  /-- The `Y`-coordinate of the smooth point. -/
  y : F
  /-- The point lies on the curve and is nonsingular. -/
  nonsingular : C.toAffine.Nonsingular x y

/-- The maximal ideal `⟨X - x, Y - y⟩` of `F[C]` corresponding to a smooth
point `P = (x, y)`. -/
noncomputable def maximalIdealAt (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    Ideal C.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal C.toAffine P.x (Polynomial.C P.y)

/-- `maximalIdealAt` is a maximal ideal: its quotient is isomorphic (as an
`F`-algebra) to `F`, which is a field. -/
theorem maximalIdealAt_isMaximal (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    (C.maximalIdealAt P).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _
    ((WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv
      P.nonsingular.1).toRingEquiv.isField (Field.toIsField F))

end SmoothPlaneCurve

end HasseWeil.Curves
