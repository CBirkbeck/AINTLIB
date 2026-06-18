# Inventory: ./HasseWeil/Curves/FintypeProjectiveSmoothPoint.lean

**File**: `HasseWeil/Curves/FintypeProjectiveSmoothPoint.lean`
**Lines**: 89
**Imports**: `HasseWeil.Curves.PicZero`, `HasseWeil.Frobenius`
**Namespace**: `HasseWeil`

**Summary**: A short glue file establishing the canonical bijection `W.toAffine.Point ≃ ProjectiveSmoothPoint ⟨W.toAffine⟩` by proving the remaining round-trip direction and packaging it into an `Equiv`, a `Fintype` instance, and a cardinality identity. **Substantial overlap with `PicZero.lean`**: that file already contains `WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint` (the same reverse round-trip), `WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint` (the same `Equiv`), `HasseWeil.Curves.ProjectiveSmoothPoint.fintype` (the same instance), and `HasseWeil.Curves.ProjectiveSmoothPoint.card_eq_card_affine_point` (a near-identical cardinality lemma). The declarations here live in the `HasseWeil` namespace rather than `WeierstrassCurve.Affine.Point` / `HasseWeil.Curves.ProjectiveSmoothPoint`, introducing a different qualified name for (essentially) the same facts.

---

## Declarations

### `theorem ProjectiveSmoothPoint.toAffinePoint_toProjectiveSmoothPoint`

- **Type**: `(P : ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F)) → P.toAffinePoint.toProjectiveSmoothPoint = P`
- **What**: The reverse round-trip of the projective ↔ affine bridge: sending a `ProjectiveSmoothPoint` to an `Affine.Point` and back via `toProjectiveSmoothPoint` recovers the original.
- **How**: Case split on the two constructors `infinity` and `affine Q`; both reduce to `rfl`.
- **Hypotheses**: `F` a field, `W : WeierstrassCurve F`.
- **Uses from project**: `ProjectiveSmoothPoint.toAffinePoint` (from `PicZero.lean`), `WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint` (from `PicZero.lean`).
- **Used by**: `Affine.Point.equivProjectiveSmoothPoint` (line 66, as `right_inv`).
- **Visibility**: public (`@[simp]`)
- **Lines**: 48–53, proof length 3 lines
- **Notes**: Near-duplicate of `WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint` in `PicZero.lean` (lines 161–167). The only difference is the namespace: here it is `ProjectiveSmoothPoint.toAffinePoint_toProjectiveSmoothPoint` under `namespace HasseWeil`, while `PicZero.lean` has `WeierstrassCurve.Affine.Point.toAffinePoint_toProjectiveSmoothPoint`. The proof is `rcases … · rfl · rfl` vs `cases … | infinity => rfl | affine Q => rfl` — mathematically identical.

---

### `noncomputable def Affine.Point.equivProjectiveSmoothPoint`

- **Type**: `W.toAffine.Point ≃ ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F)`
- **What**: The canonical equivalence (bijection) between the mathlib inductive type `W.toAffine.Point` (affine points plus basepoint) and the project's `ProjectiveSmoothPoint` type, mapping `0 ↦ infinity` and `some x y h ↦ affine ⟨x, y, h⟩`.
- **How**: Assembled from `WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint` (forward map), `ProjectiveSmoothPoint.toAffinePoint` (inverse), `WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint` (left inverse, from `PicZero.lean`), and `ProjectiveSmoothPoint.toAffinePoint_toProjectiveSmoothPoint` (right inverse, defined above).
- **Hypotheses**: `F` a field, `W : WeierstrassCurve F`.
- **Uses from project**: `WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint` (`PicZero.lean`), `ProjectiveSmoothPoint.toAffinePoint` (`PicZero.lean`), `WeierstrassCurve.Affine.Point.toProjectiveSmoothPoint_toAffinePoint` (`PicZero.lean`), `ProjectiveSmoothPoint.toAffinePoint_toProjectiveSmoothPoint` (line 48, this file).
- **Used by**: `instFintypeProjectiveSmoothPoint` (line 75), `Fintype.card_projectiveSmoothPoint_eq_pointCount` (line 86). Also used heavily by `DivisorTranslate.lean` (many sites) via the qualified name `WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint`.
- **Visibility**: public
- **Lines**: 60–67, proof length 7 lines (structure body)
- **Notes**: Near-duplicate of `WeierstrassCurve.Affine.Point.equivProjectiveSmoothPoint` in `PicZero.lean` (lines 171–178). The `PicZero.lean` version is under the `WeierstrassCurve.Affine.Point` namespace with variable `{W : WeierstrassCurve.Affine F}`; this version is under `HasseWeil` with explicit `(W : WeierstrassCurve F)`, so the qualified names differ. The downstream consumers in `DivisorTranslate.lean` reference the `PicZero.lean` version by its namespace.

---

### `noncomputable instance instFintypeProjectiveSmoothPoint`

- **Type**: `[Fintype W.toAffine.Point] → Fintype (ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F))`
- **What**: Provides a `Fintype` instance for `ProjectiveSmoothPoint ⟨W.toAffine⟩` by transporting the finiteness of `W.toAffine.Point` along the bijection `equivProjectiveSmoothPoint`.
- **How**: One-liner via `Fintype.ofEquiv W.toAffine.Point (Affine.Point.equivProjectiveSmoothPoint W)`.
- **Hypotheses**: `F` a field, `W : WeierstrassCurve F`, `Fintype W.toAffine.Point`.
- **Uses from project**: `Affine.Point.equivProjectiveSmoothPoint` (line 60, this file).
- **Used by**: `Fintype.card_projectiveSmoothPoint_eq_pointCount` (implicit, same file). Not referenced by name in any other file (the overlapping `HasseWeil.Curves.ProjectiveSmoothPoint.fintype` in `PicZero.lean` serves the same purpose for the rest of the codebase).
- **Visibility**: public
- **Lines**: 72–75, proof length 1 line (term)
- **Notes**: Duplicate of `HasseWeil.Curves.ProjectiveSmoothPoint.fintype` in `PicZero.lean` (lines 198–201). The `PicZero.lean` instance variable is `{W : WeierstrassCurve.Affine F}` while this one takes `(W : WeierstrassCurve F)` (then projects to `.toAffine`). Both call `Fintype.ofEquiv` with the same equivalence. The instance name `instFintypeProjectiveSmoothPoint` does not appear to be referenced by name in any other file.

---

### `theorem Fintype.card_projectiveSmoothPoint_eq_pointCount`

- **Type**: `[Fintype W.toAffine.Point] → Fintype.card (ProjectiveSmoothPoint (⟨W.toAffine⟩ : SmoothPlaneCurve F)) = pointCount W.toAffine`
- **What**: The cardinality of `ProjectiveSmoothPoint ⟨W.toAffine⟩` equals `pointCount W.toAffine` (which is `Fintype.card W.toAffine.Point`). There is no `+1` because the bijection already accounts for the point at infinity.
- **How**: Unfolds `pointCount` to `Fintype.card W.toAffine.Point`, then applies `Fintype.card_congr (Affine.Point.equivProjectiveSmoothPoint W).symm`.
- **Hypotheses**: `F` a field, `W : WeierstrassCurve F`, `Fintype W.toAffine.Point`.
- **Uses from project**: `Affine.Point.equivProjectiveSmoothPoint` (line 60, this file), `pointCount` (defined elsewhere in project).
- **Used by**: Referenced by name in a comment in `GapSpines.lean` (line 295); not used as a Lean term in any other file found.
- **Visibility**: public
- **Lines**: 81–86, proof length 3 lines
- **Notes**: Related to `HasseWeil.Curves.ProjectiveSmoothPoint.card_eq_card_affine_point` in `PicZero.lean` (lines 209–214), which proves `Fintype.card (ProjectiveSmoothPoint ...) = Fintype.card W.Point`. The present lemma additionally unfolds `pointCount` and works with `WeierstrassCurve F` rather than `WeierstrassCurve.Affine F`. The `GapSpines.lean` reference is a doc-comment citation, not a Lean term usage.
