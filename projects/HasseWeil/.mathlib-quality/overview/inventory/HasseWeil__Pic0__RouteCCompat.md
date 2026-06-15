# Inventory: ./HasseWeil/Pic0/RouteCCompat.lean

**File purpose:** Discharges (in part) the `hcompat` residual from `degree_eq_N_via_picDual_geometric_v3` in `RouteCGeometric.lean`. Specifically, proves that the stored point map of `frobeniusIsog W` agrees with the geometric comorphism image at any rational point. The `mulByInt` and `addIsog` blocks remain as explicit residuals (noted in the module docstring).

**Namespace:** `HasseWeil.Pic0.RouteCGeometric`

**Imports:** `HasseWeil.Pic0.RouteCGeometric`

---

## Declarations

### `noncomputable def frobeniusCurveMap`
- **Type**: `frobeniusCurveMap : HasseWeil.Curves.CurveMap ⟨W.toAffine⟩ ⟨W.toAffine⟩`
- **What**: Packages the Frobenius algebra homomorphism `f ↦ f^q` on the function field `K(E)` as a `CurveMap` from `W` to itself.
- **How**: Pure structure construction; sets `pullback := FiniteField.frobeniusAlgHom K W.toAffine.FunctionField`. No non-trivial proof term.
- **Hypotheses**: `K` a finite field, `W` a Weierstrass curve with elliptic structure.
- **Uses from project**: `HasseWeil.Curves.CurveMap` (structure), `WeierstrassCurve.Affine.FunctionField`
- **Used by**: `frobeniusCurveMap_pullback`, `frobeniusCurveMapCoordHom`
- **Visibility**: public
- **Lines**: 64–67, proof length ~4 lines (structure body)
- **Notes**: None.

---

### `@[simp] theorem frobeniusCurveMap_pullback`
- **Type**: `(frobeniusCurveMap W).pullback = FiniteField.frobeniusAlgHom K W.toAffine.FunctionField`
- **What**: Simp lemma unfolding the `pullback` field of `frobeniusCurveMap W`; definitional equality.
- **How**: `rfl`.
- **Hypotheses**: Same as `frobeniusCurveMap`.
- **Uses from project**: `frobeniusCurveMap`
- **Used by**: unused in file (simp lemma, used by the simp set or callers in other files)
- **Visibility**: public
- **Lines**: 68–71, proof length 1 line
- **Notes**: None.

---

### `noncomputable def frobeniusCurveMapCoordHom`
- **Type**: `frobeniusCurveMapCoordHom : (frobeniusCurveMap W).CoordHom`
- **What**: Provides the canonical `CoordHom` witness for `frobeniusCurveMap W`: sets `toAlgHom` to be `frobeniusAlgHom K R` on the coordinate ring `R`, and proves the commutativity `frob ∘ algebraMap = algebraMap ∘ frob` (i.e., the `q`-th power commutes with the canonical map `R → K(E)`).
- **How**: The `compat` field is proved by `simp only [FiniteField.coe_frobeniusAlgHom, map_pow]`: the Frobenius acts as `(·^q)` on both sides and `map_pow` equates them.
- **Hypotheses**: Same as `frobeniusCurveMap`.
- **Uses from project**: `frobeniusCurveMap`, `HasseWeil.Curves.CurveMap.CoordHom` (structure); mathlib `FiniteField.frobeniusAlgHom`, `FiniteField.coe_frobeniusAlgHom`
- **Used by**: `frobeniusCurveMapCoordHom_toAlgHom`, `frobeniusCurveMap_toPointMap`, `frobeniusIsog_toPointMap_compat`
- **Visibility**: public
- **Lines**: 75–84, proof length ~7 lines
- **Notes**: None.

---

### `@[simp] theorem frobeniusCurveMapCoordHom_toAlgHom`
- **Type**: `(frobeniusCurveMapCoordHom W).toAlgHom = FiniteField.frobeniusAlgHom K W.toAffine.CoordinateRing`
- **What**: Simp lemma unfolding the `toAlgHom` field of `frobeniusCurveMapCoordHom W`; definitional equality.
- **How**: `rfl`.
- **Hypotheses**: Same as `frobeniusCurveMap`.
- **Uses from project**: `frobeniusCurveMapCoordHom`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 85–88, proof length 1 line
- **Notes**: None.

---

### `theorem frobeniusCurveMap_toPointMap`
- **Type**: `frobeniusCurveMap_toPointMap (x y : K) (h : W.toAffine.Nonsingular x y) : CurveMap.toPointMap (frobeniusCurveMapCoordHom W) ⟨x, y, h⟩ = ⟨x, y, h⟩`
- **What**: The geometric comorphism image of a rational point `(x,y)` under the Frobenius `CurveMap` is the point itself, because the `q`-th power of an element of a finite field `K` of cardinality `q` is the identity (`FiniteField.pow_card`).
- **How**: Two-branch `ext` proof (x-coordinate and y-coordinate). Each branch: unfolds `evalAtPullback`, rewrites `frobeniusAlgHom` as `(·^q)` using `FiniteField.coe_frobeniusAlgHom`, applies `map_pow` to pull the power through `evalAt`, applies `evalAt_x`/`evalAt_y` to get `x` or `y`, and concludes by `FiniteField.pow_card`.
- **Hypotheses**: Same as `frobeniusCurveMap`. The point `(x,y)` must be nonsingular.
- **Uses from project**: `frobeniusCurveMapCoordHom`, `HasseWeil.Curves.CurveMap.toPointMap`, `HasseWeil.Curves.CurveMap.evalAtPullback_apply`, `HasseWeil.Curves.SmoothPlaneCurve.evalAt`, `HasseWeil.Curves.SmoothPlaneCurve.evalAt_x`, `HasseWeil.Curves.SmoothPlaneCurve.evalAt_y`; mathlib `FiniteField.coe_frobeniusAlgHom`, `FiniteField.pow_card`, `map_pow`
- **Used by**: `frobeniusIsog_toPointMap_compat`
- **Visibility**: public
- **Lines**: 94–137, proof length ~44 lines (set_option maxHeartbeats 800000)
- **Notes**: `set_option maxHeartbeats 800000` on line 89, NO justifying comment. Proof >30 lines (44 lines). The proof is verbose due to repeated `change` unfoldings for both coordinates.

---

### `theorem frobeniusIsog_toPointMap_compat`
- **Type**: `frobeniusIsog_toPointMap_compat (x y : K) (h : W.toAffine.Nonsingular x y) : (frobeniusIsog W).toAddMonoidHom (Affine.Point.some x y h) = (CurveMap.toPointMap (frobeniusCurveMapCoordHom W) ⟨x,y,h⟩).toAffinePoint`
- **What**: The `hcompat` identity for the Frobenius building block: the stored additive map of `frobeniusIsog W` (which is the identity on rational points) agrees with the geometric comorphism image at every rational point `(x,y)`.
- **How**: Rewrites by `frobeniusCurveMap_toPointMap` (which shows the RHS equals `⟨x,y,h⟩`), then closes by `rfl` since `frobeniusIsog.toAddMonoidHom = AddMonoidHom.id`.
- **Hypotheses**: Same as above.
- **Uses from project**: `frobeniusCurveMapCoordHom`, `frobeniusCurveMap_toPointMap`, `frobeniusIsog` (from `HasseWeil.Frobenius` or `HasseWeil.FrobeniusIsogeny`), `HasseWeil.Curves.CurveMap.toPointMap`
- **Used by**: unused in file (intended for callers building the `hcompat` chain in `RouteCGeometric`)
- **Visibility**: public
- **Lines**: 147–155, proof length ~7 lines
- **Notes**: The key payoff declaration of the file.

---

## Summary statistics

| Kind | Count |
|------|-------|
| `noncomputable def` | 2 |
| `@[simp] theorem` | 2 |
| `theorem` | 2 |
| **Total** | **6** |

- **Sorries**: none
- **`set_option maxHeartbeats`**: line 89, value 800000, NO justifying comment — applies to `frobeniusCurveMap_toPointMap`
- **Long proofs (>30 lines)**: `frobeniusCurveMap_toPointMap` (~44 lines)
- **Key API** (used by 3+ others in file): `frobeniusCurveMapCoordHom` (used by `frobeniusCurveMapCoordHom_toAlgHom`, `frobeniusCurveMap_toPointMap`, `frobeniusIsog_toPointMap_compat`)
- **Unused in file** (dead-code candidates): `frobeniusCurveMap_pullback`, `frobeniusCurveMapCoordHom_toAlgHom`, `frobeniusIsog_toPointMap_compat` (these are intended for external callers)

## Notes

This is a small, focused file (158 lines, 6 declarations) that ships the Frobenius `hcompat` building block completely and axiom-cleanly. The `mulByInt` and `addIsog` `hcompat` blocks are explicitly tracked as residuals in the module docstring. The `frobeniusCurveMap_toPointMap` proof is verbose due to repeated manual `change` unfoldings; it could potentially be simplified with simp lemmas. The `maxHeartbeats 800000` is set without a comment.
