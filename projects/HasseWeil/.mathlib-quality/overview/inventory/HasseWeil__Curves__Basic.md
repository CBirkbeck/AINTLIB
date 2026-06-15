# Inventory: ./HasseWeil/Curves/Basic.lean

**File**: `HasseWeil/Curves/Basic.lean`
**Lines**: 1–75
**Module**: `HasseWeil.Curves`

---

## Overview

A thin 75-line foundation file providing `SmoothPlaneCurve F` as a wrapper over mathlib's `WeierstrassCurve.Affine F`, together with `SmoothPoint`, two abbreviations for the coordinate ring and function field, and one definition + one theorem for the maximal ideal at a smooth point. No sorries, no `set_option maxHeartbeats`, no long proofs.

---

## Declarations

---

### `structure SmoothPlaneCurve`

- **Type**: `(F : Type*) [Field F] → Type*`, a structure with one field `toAffine : WeierstrassCurve.Affine F`
- **What**: A thin wrapper around mathlib's affine Weierstrass curve, intended to eventually generalize to arbitrary irreducible polynomials in `F[X, Y]` (tracked by `T-II-1-001`).
- **How**: Pure structure definition; no proof content.
- **Hypotheses**: `F` is a field.
- **Uses from project**: []
- **Used by**: `SmoothPlaneCurve.CoordinateRing`, `SmoothPlaneCurve.FunctionField`, `SmoothPlaneCurve.SmoothPoint`, `SmoothPlaneCurve.maximalIdealAt`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`; also heavily used by downstream files throughout the project.
- **Visibility**: public
- **Lines**: 29–32; body = 1 line (single field)
- **Notes**: Explicitly noted as a short-term wrapper pending `T-II-1-001` generalization.

---

### `noncomputable abbrev CoordinateRing`

- **Type**: `(C : SmoothPlaneCurve F) → Type _`; defined as `C.toAffine.CoordinateRing`
- **What**: The coordinate ring `F[C] := F[X, Y] / ⟨p⟩` of the plane curve, aliasing mathlib's `WeierstrassCurve.Affine.CoordinateRing`.
- **How**: Transparent abbreviation; no proof.
- **Hypotheses**: `F` field, `C : SmoothPlaneCurve F`.
- **Uses from project**: `SmoothPlaneCurve` (via `C.toAffine`)
- **Used by**: `SmoothPlaneCurve.maximalIdealAt`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`; used pervasively in downstream files.
- **Visibility**: public
- **Lines**: 38–39; body = 1 line
- **Notes**: Abbreviation (transparent), so unfolds freely — important for type-class search in downstream files.

---

### `noncomputable abbrev FunctionField`

- **Type**: `(C : SmoothPlaneCurve F) → Type _`; defined as `C.toAffine.FunctionField`
- **What**: The function field `F(C) := Frac(F[C])` of the plane curve, aliasing mathlib's `WeierstrassCurve.Affine.FunctionField`.
- **How**: Transparent abbreviation; no proof.
- **Hypotheses**: `F` field, `C : SmoothPlaneCurve F`.
- **Uses from project**: `SmoothPlaneCurve` (via `C.toAffine`)
- **Used by**: Unused within this file; used extensively in downstream files (Transcendence, OrdAtInftyBridge, etc.).
- **Visibility**: public
- **Lines**: 42–43; body = 1 line
- **Notes**: Abbreviation (transparent).

---

### `@[ext] structure SmoothPoint`

- **Type**: `(C : SmoothPlaneCurve F) → Type*`, a structure with fields `x : F`, `y : F`, `nonsingular : C.toAffine.Nonsingular x y`
- **What**: A smooth (nonsingular) affine point on the plane curve: coordinates `(x, y)` satisfying the curve equation and the nonsingularity condition (at least one partial derivative nonzero), following Silverman II.1.
- **How**: Pure structure definition; the `@[ext]` attribute derives an extensionality lemma from coordinate equality.
- **Hypotheses**: `F` field, `C : SmoothPlaneCurve F`; implicitly `C.toAffine.Nonsingular x y` (point is on curve and nonsingular).
- **Uses from project**: `SmoothPlaneCurve` (via `C.toAffine`)
- **Used by**: `SmoothPlaneCurve.maximalIdealAt`, `SmoothPlaneCurve.maximalIdealAt_isMaximal`; used throughout downstream files.
- **Visibility**: public
- **Lines**: 49–56; body = 3 fields
- **Notes**: `@[ext]` generates `SmoothPoint.ext`.

---

### `noncomputable def maximalIdealAt`

- **Type**: `(C : SmoothPlaneCurve F) → C.SmoothPoint → Ideal C.CoordinateRing`
- **What**: The maximal ideal `⟨X − x, Y − y⟩` of the coordinate ring corresponding to a smooth point `P = (x, y)`, constructed as `WeierstrassCurve.Affine.CoordinateRing.XYIdeal`.
- **How**: Direct application of mathlib's `Affine.CoordinateRing.XYIdeal` to the coordinates `P.x` and `Polynomial.C P.y`.
- **Hypotheses**: `F` field, `C : SmoothPlaneCurve F`, `P : C.SmoothPoint`.
- **Uses from project**: `SmoothPlaneCurve`, `SmoothPoint`, `CoordinateRing`
- **Used by**: `maximalIdealAt_isMaximal`; used in many downstream files (`AdditionPullback/SamePlace.lean`, `EC/TranslateValuation.lean`, `EC/MulByIntSamePlace.lean`, `Hasse/L6Witnesses.lean`, `Curves/Valuation.lean`).
- **Visibility**: public
- **Lines**: 60–62; body = 1 line
- **Notes**: Wraps `Affine.CoordinateRing.XYIdeal` — the coordinate `y` is wrapped in `Polynomial.C` to match the type expected by mathlib.

---

### `theorem maximalIdealAt_isMaximal`

- **Type**: `(C : SmoothPlaneCurve F) → (P : C.SmoothPoint) → (C.maximalIdealAt P).IsMaximal`
- **What**: The ideal `maximalIdealAt P` is a maximal ideal: its residue ring is isomorphic (as an `F`-algebra) to `F` (which is a field), so it is maximal.
- **How**: Uses `Ideal.Quotient.maximal_of_isField`, supplying the field witness via the mathlib ring equivalence `Affine.CoordinateRing.quotientXYIdealEquiv P.nonsingular.1` (which uses the nonsingularity condition `P.nonsingular.1`) transported through `.toRingEquiv.isField (Field.toIsField F)`.
- **Hypotheses**: `F` field, `C : SmoothPlaneCurve F`, `P : C.SmoothPoint` (in particular `P.nonsingular.1` is the on-curve condition needed by `quotientXYIdealEquiv`).
- **Uses from project**: `SmoothPlaneCurve`, `SmoothPoint`, `CoordinateRing`, `maximalIdealAt`
- **Used by**: Unused within this file; used in `AdditionPullback/SamePlace.lean` (4 times), `EC/TranslateValuation.lean`, `EC/MulByIntSamePlace.lean` (2 times), `Hasse/L6Witnesses.lean`, `Curves/Valuation.lean`.
- **Visibility**: public
- **Lines**: 66–70; proof = 3 lines (term-mode, inline)
- **Notes**: Short term-mode proof; the key mathlib lemma is `Affine.CoordinateRing.quotientXYIdealEquiv` applied to `P.nonsingular.1`.
