# Inventory: ./HasseWeil/Pic0/ToClassFunctorial.lean

**File summary:** 181 lines (including a large module-doc comment). Three public theorem
declarations; no `sorry`, no `set_option maxHeartbeats`. All proofs are very short (≤4 lines
each).

---

## Imports

- `HasseWeil.Curves.PointFunctor` — provides `toPointMap`, `toPointMap_id`,
  `maximalIdealAt_toPointMap`, `SmoothPoint.toAffinePoint_def`
- `HasseWeil.Curves.IntegralClosure` — provides `maximalIdealAt_ne_bot`
- `HasseWeil.Pic0.ToClassSurjective` — provides `mk0_eq_mk_XYIdeal'`, `toClass_some`

---

## Declarations

### `theorem WeierstrassCurve.Affine.Point.toClass_toAffinePoint`

- **Type**:
  ```
  {F : Type*} [Field F] [DecidableEq F]
  {C : HasseWeil.Curves.SmoothPlaneCurve F} [C.toAffine.IsElliptic]
  (P : C.SmoothPoint) :
  toClass (P.toAffinePoint) =
    Additive.ofMul (ClassGroup.mk0 ⟨C.maximalIdealAt P,
      mem_nonZeroDivisors_iff_ne_zero.mpr (C.maximalIdealAt_ne_bot P)⟩)
  ```
- **What**: Identifies `toClass` (mathlib's map `E.Point → Additive (ClassGroup R)`) applied
  to a smooth point `P = (x, y)` with the additive wrap of `ClassGroup.mk0` of the project's
  `maximalIdealAt P = ⟨X−x, Y−y⟩`. This is the affine-coordinate-ring incarnation of
  `κ : E → Pic⁰(E)`, `P ↦ [(P) − (O)]`.
- **How**: Rewrites via `SmoothPoint.toAffinePoint_def`, `toClass_some`, then
  `mk0_eq_mk_XYIdeal'` (from `ToClassSurjective`) to bridge the `ClassGroup.mk` and
  `ClassGroup.mk0` constructors; closes with `rfl`.
- **Hypotheses**: `C` is an elliptic curve (smooth plane curve with `IsElliptic`). No
  separability or characteristic conditions.
- **Uses from project**:
  - `HasseWeil.Curves.SmoothPlaneCurve.SmoothPoint.toAffinePoint_def`
    (`HasseWeil.Curves.PointFunctor`)
  - `HasseWeil.Curves.SmoothPlaneCurve.maximalIdealAt_ne_bot`
    (`HasseWeil.Curves.IntegralClosure`)
  - `WeierstrassCurve.Affine.mk0_eq_mk_XYIdeal'` (`HasseWeil.Pic0.ToClassSurjective`)
  - `WeierstrassCurve.Affine.Point.toClass_some` (mathlib / `ToClassSurjective`)
- **Used by**: `toClass_toPointMap` (same file)
- **Visibility**: public
- **Lines**: 115–124, proof 4 lines
- **Notes**: Unconditional. No `sorry`, no `maxHeartbeats`.

---

### `theorem HasseWeil.Curves.CurveMap.toClass_toPointMap`

- **Type**:
  ```
  {F : Type*} [Field F] [DecidableEq F]
  {C₁ C₂ : HasseWeil.Curves.SmoothPlaneCurve F}
  [C₁.toAffine.IsElliptic] [C₂.toAffine.IsElliptic]
  {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom)
  (P : C₁.SmoothPoint)
  (hne : Ideal.comap coordHom.toAlgHom.toRingHom (C₁.maximalIdealAt P) ≠ ⊥) :
  toClass ((toPointMap coordHom P).toAffinePoint) =
    Additive.ofMul (ClassGroup.mk0
      ⟨Ideal.comap coordHom.toAlgHom.toRingHom (C₁.maximalIdealAt P),
        mem_nonZeroDivisors_iff_ne_zero.mpr hne⟩)
  ```
- **What**: The Silverman III.3.4 ideal-level functoriality for a curve map `φ : C₁ → C₂` with
  coordinate-ring comorphism `α* : R₂ → R₁`. The `Pic⁰` class of the image point `φ(P)` equals
  the `mk0` class of the **contraction** `Ideal.comap(α*)(maximalIdealAt P)`. The variance is
  `comap` (not `Ideal.map` nor `Ideal.relNorm`).
- **How**: Applies `toClass_toAffinePoint` to the image point, then uses the project's scheme-
  theoretic identity `maximalIdealAt_toPointMap coordHom P` (from `HasseWeil.Curves.PointFunctor`)
  to rewrite the underlying ideal via `congr 1` and `congrArg ClassGroup.mk0 (Subtype.ext ...)`.
- **Hypotheses**: Both `C₁`, `C₂` are elliptic curves (note: `[C₁.toAffine.IsElliptic]` is
  omitted in the `omit` block, so only `C₂.IsElliptic` is in scope), a comorphism witness
  `coordHom : φ.CoordHom` exists, and `hne` (the contraction of `maximalIdealAt P` along `α*`
  is nonzero — holds for any module-finite/integral comorphism, e.g. a genuine isogeny).
- **Uses from project**:
  - `toClass_toAffinePoint` (same file, applied to the image point)
  - `HasseWeil.Curves.CurveMap.maximalIdealAt_toPointMap`
    (`HasseWeil.Curves.PointFunctor`)
- **Used by**: `toClass_toPointMap_id` (same file, implicitly via `toClass_toAffinePoint` path);
  used heavily in `HasseWeil.Pic0.RouteCGeometric`, `HasseWeil.Pic0.PicDual`,
  `HasseWeil.Pic0.ClassGroupNorm` (all outside this file)
- **Visibility**: public
- **Lines**: 156–168, proof 6 lines
- **Notes**: The `omit [C₁.toAffine.IsElliptic]` attribute on the preceding line removes the
  `C₁.IsElliptic` instance from the variable context for this theorem only. No `sorry`,
  no `maxHeartbeats`. The module doc gives an extensive explanation of why the `classMap`
  (extension) direction is false and why naive `toClass_isogeny_compat` is unprovable.

---

### `theorem HasseWeil.Curves.CurveMap.toClass_toPointMap_id`

- **Type**:
  ```
  {F : Type*} [Field F] [DecidableEq F]
  {C : HasseWeil.Curves.SmoothPlaneCurve F} [C.toAffine.IsElliptic]
  (P : C.SmoothPoint) :
  toClass ((toPointMap (CoordHom.id C) P).toAffinePoint) =
    toClass (P.toAffinePoint)
  ```
- **What**: The identity-isogeny base case for III.3.4 functoriality: applying the point map of
  `CoordHom.id C` (the identity comorphism) and then `toClass` yields the same class as
  `toClass P` directly. Fully unconditional.
- **How**: A single `rw [toPointMap_id]` using the simp lemma `toPointMap_id` from
  `HasseWeil.Curves.PointFunctor` (which says `toPointMap (CoordHom.id C) P = P`).
- **Hypotheses**: `C` is an elliptic curve. No side condition on the contraction (the `comap`
  along `AlgHom.id` is the identity, so it trivially equals the original ideal).
- **Uses from project**:
  - `HasseWeil.Curves.CurveMap.toPointMap_id` (`HasseWeil.Curves.PointFunctor`)
- **Used by**: unused in this file (appears to be a standalone sanity/base-case lemma for
  external consumers)
- **Visibility**: public
- **Lines**: 174–179, proof 1 line
- **Notes**: No `sorry`, no `maxHeartbeats`. Simplest declaration in the file.

---

## Cross-reference summary

| Declaration | Used by (in file) | Used by (outside file, confirmed) |
|---|---|---|
| `toClass_toAffinePoint` | `toClass_toPointMap` | — (indirectly via callers of `toClass_toPointMap`) |
| `toClass_toPointMap` | — | `RouteCGeometric`, `PicDual`, `ClassGroupNorm`, `RouteCTheoremOfSquare` |
| `toClass_toPointMap_id` | — | (not confirmed in grep) |

**Key API** (used by ≥ 3 things in the project overall): `toClass_toPointMap`.
