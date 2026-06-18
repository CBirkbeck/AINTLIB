# Inventory: ./HasseWeil/EC/GroupLaw.lean

File location: `HasseWeil/EC/GroupLaw.lean`
Total lines: 55
Namespace: `HasseWeil.EC`
Import: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`

This is a thin wrapper file introducing Silverman's notation `E_ns` (nonsingular locus) and transferring the abelian group structure from `WeierstrassCurve.Affine.Point` to the set-typed `E.nonsingularLocus`.

---

## Declaration Inventory

### `def WeierstrassCurve.nonsingularLocus`

- **Type**: `(E : WeierstrassCurve F) : Set E.toAffine.Point`
- **What**: Defines `E.nonsingularLocus` as `Set.univ`, the full set of points of `E.toAffine.Point`. Since Mathlib's `WeierstrassCurve.Affine.Point` is by construction the disjoint union of the point at infinity and the nonsingular affine points, this is exactly the nonsingular locus `E_ns` in Silverman's sense.
- **How**: One-liner: `Set.univ`. The mathematical content (that `Affine.Point` = nonsingular locus) is a definitional observation, not a proof obligation.
- **Hypotheses**: `F` is a field.
- **Uses from project**: None.
- **Used by**: The anonymous `AddCommGroup` instance immediately below in this file (via `E.nonsingularLocus`). No other references found in the project (grep confirms only the defining site).
- **Visibility**: Public (declared in `_root_` scope, extending the `WeierstrassCurve` namespace).
- **Lines**: 42–44, proof length: 1 line (term-mode).
- **Notes**: None.

---

### `instance (E : WeierstrassCurve F) : AddCommGroup E.nonsingularLocus`

- **Type**: `AddCommGroup E.nonsingularLocus` (anonymous instance, with implicit `[Field F]`)
- **What**: Equips the nonsingular locus `E.nonsingularLocus` (= `Set.univ ⊆ E.toAffine.Point`) with the abelian group structure transferred from `E.toAffine.Point` via the canonical set equivalence. This formalises Silverman III.2: `E_ns` is an abelian group under the chord-and-tangent law.
- **How**: Applies `Equiv.Set.univ E.toAffine.Point` (the canonical equivalence between `E.toAffine.Point` and its `Set.univ` subtype) and uses the mathlib lemma `Equiv.addCommGroup` to transport the `AddCommGroup` instance from the point type to the set subtype. The underlying group structure on `E.toAffine.Point` comes from Mathlib's `WeierstrassCurve.Affine.Point.instAddCommGroup`.
- **Hypotheses**: `F` is a field.
- **Uses from project**: `WeierstrassCurve.nonsingularLocus` (the def above).
- **Used by**: Unused within this file (no other declarations); likely intended for import by other files, but grep finds no current importers of this file in the project.
- **Visibility**: Public (noncomputable instance).
- **Lines**: 51–53, proof length: 1 line (term-mode).
- **Notes**: `noncomputable` is required because `AddCommGroup.toAddGroup` etc. are noncomputable in Mathlib. The instance is anonymous, so it is found by typeclass search on `E.nonsingularLocus`.

---

## Summary

| Metric | Value |
|---|---|
| Total declarations | 2 |
| `def`s | 1 |
| `lemma`/`theorem`s | 0 |
| `instance`s | 1 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 0 |
| Unused in file | `nonsingularLocus` (used only by the instance, which itself has no in-file callers) |
| Key API | `nonsingularLocus` (used by the instance) |

**Notes**: This is a pure notation/transfer file — no new mathematics. Both declarations are one-liners. No other project files currently import this module (the `nonsingularLocus` def appears only in this file). The file may be a stub intended for future use of `E_ns` notation across the project.
