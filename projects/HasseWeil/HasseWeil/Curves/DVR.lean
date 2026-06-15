import HasseWeil.Curves.Basic
import HasseWeil.Valuation

/-!
# The local ring at a smooth point of a plane curve is a DVR

This file closes ticket `T-II-1-001` (Silverman II.1.1): for a smooth plane
curve `C` and a smooth point `P ∈ C`, the localization of the coordinate ring
at the maximal ideal of `P` is a discrete valuation ring.

The substantive proof lives in `HasseWeil.Valuation` — it is a general
statement about affine Weierstrass curves over a field (no `IsElliptic`
hypothesis is required, contrary to earlier belief). This file simply
repackages it for the `SmoothPlaneCurve` abstraction of Stream A.

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.1.1
-/

namespace HasseWeil.Curves

variable {F : Type*} [Field F]

/-- The local ring at a smooth point of a smooth plane curve is a discrete
valuation ring.
Reference: Silverman II.1.1. -/
theorem SmoothPlaneCurve.localRing_isDVR_of_smooth
    (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
    letI : (C.maximalIdealAt P).IsPrime := (C.maximalIdealAt_isMaximal P).isPrime
    IsDiscreteValuationRing (Localization.AtPrime (C.maximalIdealAt P)) :=
  HasseWeil.localRing_isDVR C.toAffine P.nonsingular

end HasseWeil.Curves
