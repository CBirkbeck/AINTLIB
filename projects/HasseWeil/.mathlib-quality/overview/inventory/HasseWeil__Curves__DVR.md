# Inventory: ./HasseWeil/Curves/DVR.lean

## File overview

A thin wrapper file (35 lines total, 1 declaration) closing ticket T-II-1-001
(Silverman II.1.1): the local ring at a smooth point of a smooth plane curve is
a DVR. The substantive proof lives in `HasseWeil.Valuation`; this file only
re-packages it for the `SmoothPlaneCurve` abstraction.

---

### `theorem SmoothPlaneCurve.localRing_isDVR_of_smooth`

- **Type**:
  ```
  (C : SmoothPlaneCurve F) (P : C.SmoothPoint) :
      letI : (C.maximalIdealAt P).IsPrime := (C.maximalIdealAt_isMaximal P).isPrime
      IsDiscreteValuationRing (Localization.AtPrime (C.maximalIdealAt P))
  ```
- **What**: For a smooth plane curve `C` and a smooth point `P`, the
  localization of the coordinate ring at the maximal ideal of `P` is a
  discrete valuation ring. This is Silverman II.1.1.
- **How**: One-line proof: directly delegates to `HasseWeil.localRing_isDVR`
  (in `HasseWeil.Valuation`) via `C.toAffine` and `P.nonsingular`. The
  `IsPrime` instance is supplied inline via `maximalIdealAt_isMaximal`.
- **Hypotheses**: `F` a field; `C` a `SmoothPlaneCurve F`; `P` a
  `SmoothPoint` of `C` (smooth affine point, `C.toAffine.Nonsingular P.x P.y`).
- **Uses from project**:
  - `HasseWeil.localRing_isDVR` (from `HasseWeil.Valuation`)
  - `SmoothPlaneCurve.maximalIdealAt` (from `HasseWeil.Curves.Basic`)
  - `SmoothPlaneCurve.maximalIdealAt_isMaximal` (from `HasseWeil.Curves.Basic`)
  - `SmoothPlaneCurve.toAffine` (field of `SmoothPlaneCurve`)
  - `SmoothPoint.nonsingular` (field of `SmoothPoint`)
- **Used by**: unused in file (referenced externally in
  `HasseWeil/Curves/Valuation.lean` and mentioned in `HasseWeil/Ramification.lean`)
- **Visibility**: public
- **Lines**: 28–32, proof length 1 line (single term-mode application)
- **Notes**: No `sorry`, no `set_option maxHeartbeats`, no `TODO`. Proof is
  trivially short. No suspected mathlib duplication. Not experimental/parked.
