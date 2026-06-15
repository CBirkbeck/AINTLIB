# Inventory: ./HasseWeil/EC/GenericPoint.lean

**File**: `HasseWeil/EC/GenericPoint.lean`
**Lines**: 57 (including module doc)
**Import**: `HasseWeil.MulByIntPullback`
**Namespace**: `HasseWeil`

---

## Module summary

A tiny wrapper file that packages the generic point of the elliptic curve `W`
base-changed to its own function field `K(E)`. All three declarations are
one-liners that delegate to infrastructure already established in
`MulByIntPullback`. The file's purpose is to expose `genericPoint` as a clean,
named `(W_KE W).toAffine.Point` for downstream consumers
(e.g. `GapSpines.lean`, `WallA/VSideDual.lean`).

---

### `theorem generic_nonsingular`

- **Type**:
  ```lean
  theorem generic_nonsingular :
      (W_KE W).toAffine.Nonsingular (x_gen W) (y_gen W)
  ```
- **What**: Proves that the coordinate pair `(x_gen W, y_gen W)` is a
  nonsingular point on the base-changed curve `W_KE W`. For an elliptic
  curve, the Weierstrass equation implies nonsingularity.
- **How**: Single call to `Affine.equation_iff_nonsingular.mp (generic_equation W)`.
  `generic_equation W` (from `MulByIntPullback`) asserts the equation holds;
  `Affine.equation_iff_nonsingular` (mathlib) is the key equivalence.
- **Hypotheses**: `W : WeierstrassCurve F`, `W.toAffine.IsElliptic`.
- **Uses from project**: `generic_equation` (from `MulByIntPullback`), `W_KE`, `x_gen`, `y_gen`.
- **Used by**: `genericPoint` (this file).
- **Visibility**: public
- **Lines**: 37–39, proof length 1 line
- **Notes**: `MulByIntPullback` already contains a private version `generic_nonsingular'` (line 95); this is the public re-export with the same body.

---

### `noncomputable def genericPoint`

- **Type**:
  ```lean
  noncomputable def genericPoint : (W_KE W).toAffine.Point
  ```
- **What**: Defines the **generic point** of the elliptic curve `W` as the
  affine `K(E)`-rational point `some (x_gen W) (y_gen W) _` on `W_KE W`,
  i.e. the universal point whose coordinates are the function-field generators.
- **How**: Direct constructor call `Affine.Point.some x y ns` where nonsingularity
  `ns` is supplied by `generic_nonsingular W`.
- **Hypotheses**: `W : WeierstrassCurve F`, `W.toAffine.IsElliptic`.
- **Uses from project**: `W_KE`, `x_gen`, `y_gen`, `generic_nonsingular`.
- **Used by**: `genericPoint_xOf_some` (this file); widely used in `GapSpines.lean`
  and `WallA/VSideDual.lean` in other files.
- **Visibility**: public
- **Lines**: 48–49, definition body 1 line
- **Notes**: `noncomputable` because `x_gen`/`y_gen` live in a fraction field.

---

### `@[simp] theorem genericPoint_xOf_some`

- **Type**:
  ```lean
  @[simp] theorem genericPoint_xOf_some :
      genericPoint W = Affine.Point.some (x_gen W) (y_gen W) (generic_nonsingular W)
  ```
- **What**: Proves `genericPoint W` unfolds to `Affine.Point.some ...`, enabling
  simp and rewrite lemmas that need to see the `some` constructor explicitly.
- **How**: `rfl` — the definition of `genericPoint` is exactly this constructor call.
- **Hypotheses**: `W : WeierstrassCurve F`, `W.toAffine.IsElliptic`.
- **Uses from project**: `genericPoint`, `x_gen`, `y_gen`, `generic_nonsingular`.
- **Used by**: Unused within this file; used externally in `GapSpines.lean` (lines 1062, 1484) and `WallA/VSideDual.lean` (line 80).
- **Visibility**: public (`@[simp]`)
- **Lines**: 52–54, proof length 1 line
- **Notes**: Acts as a definitional unfolding lemma; `@[simp]` tag makes it
  automatically available for tactic proofs that need the `some` form.

---

## Cross-reference summary

| Declaration | Used by (this file) | Used by (other files) |
|---|---|---|
| `generic_nonsingular` | `genericPoint`, `genericPoint_xOf_some` | `GapSpines.lean`, `WallA/VSideDual.lean` |
| `genericPoint` | `genericPoint_xOf_some` | `GapSpines.lean` (many), `WallA/VSideDual.lean` |
| `genericPoint_xOf_some` | — | `GapSpines.lean`, `WallA/VSideDual.lean` |

**Key API** (used by 3+ declarations across files): `generic_nonsingular` is
referenced by both `genericPoint` and `genericPoint_xOf_some` within the file,
and by multiple callers in other files. `genericPoint` itself is the primary
export.

---

## Statistics

- Total declarations: 3
- `def`s: 1 (`genericPoint`)
- `lemma`/`theorem`s: 2 (`generic_nonsingular`, `genericPoint_xOf_some`)
- `instance`s: 0
- Sorries: none
- `set_option maxHeartbeats`: none
- Long proofs (>30 lines): none
- Unused in file: `genericPoint_xOf_some` (not called by anything else in this file)
