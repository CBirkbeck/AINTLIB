# Inventory: ./HasseWeil/Curves/OrdAtInftyBaseChange.lean

**File path**: `HasseWeil/Curves/OrdAtInftyBaseChange.lean`
**Namespace**: `HasseWeil.Curves.SmoothPlaneCurve`
**Imports**: `HasseWeil.Curves.Infinity`, `HasseWeil.Curves.CurveMapBaseChange`, `HasseWeil.Curves.IntegralClosure`
**Total lines**: 127
**Total declarations**: 4 (all theorems)
**Sorries**: none
**set_option**: `set_option linter.style.longLine false` (line 48, no maxHeartbeats override)

---

## Summary

A self-contained 127-line file proving that the order at infinity is preserved by function-field base change: `ord_∞^L(functionFieldMap z) = ord_∞^K z` for `z ≠ 0`. The argument has two layers: (1) norm transport for integral elements, using the explicit `norm_smul_basis` polynomial identity from mathlib; (2) lifting to fractions via `ordAtInfty_div_eq_mul_inv`/`ordAtInfty_inv`. No instances, no defs, no sorries.

---

## Declarations

---

### `theorem coordRingMap_smul_basis`

- **Type**:
  ```
  (p q : Polynomial K) →
    C.coordRingMap L (p • 1 + q • CoordinateRing.mk C.toAffine Polynomial.X) =
      (p.map (algebraMap K L)) • 1 +
        (q.map (algebraMap K L)) • CoordinateRing.mk (C.baseChange L).toAffine Polynomial.X
  ```
- **What**: Shows that `coordRingMap` sends a `K[X]`-basis element `p·1 + q·y` to `(p mapped)·1 + (q mapped)·y` over `L`; i.e., it commutes with the basis decomposition and the coefficient map.
- **How**: `change` unfolds `coordRingMap` to `CoordinateRing.map (algebraMap K L)`, then `rw [map_add, map_smul, map_smul, map_one]` reduces to components; `CoordinateRing.map_mk` + `Polynomial.map_X` handle the generator.
- **Hypotheses**: `C : SmoothPlaneCurve K`, `L / K` a field extension.
- **Uses from project**: `SmoothPlaneCurve.coordRingMap` (from `CurveMapBaseChange.lean`), `SmoothPlaneCurve.baseChange` (from `BaseChange.lean`). Uses mathlib `WeierstrassCurve.Affine.CoordinateRing.map`, `CoordinateRing.map_smul`, `CoordinateRing.map_mk`.
- **Used by**: `norm_coordRingMap` (this file).
- **Visibility**: public
- **Lines**: 52–63 (proof lines 58–62, ~5 lines)
- **Notes**: Helper lemma for `norm_coordRingMap`; pure rewrite proof.

---

### `theorem norm_coordRingMap`

- **Type**:
  ```
  (u : C.CoordinateRing) →
    Algebra.norm (Polynomial L) (C.coordRingMap L u) =
      (Algebra.norm (Polynomial K) u).map (algebraMap K L)
  ```
- **What**: The algebra norm `N_{L[X]}` of the base-changed element `coordRingMap u` equals the polynomial `N_{K[X]}(u)` with coefficients mapped via `algebraMap K L`. This is the key "norm transport" identity.
- **How**: Decomposes `u = p·1 + q·y` via `CoordinateRing.exists_smul_basis_eq` (mathlib), applies `coordRingMap_smul_basis` to rewrite both sides, then uses the explicit mathlib formula `CoordinateRing.norm_smul_basis` on both sides; the resulting polynomial identity follows from `simp` with `Polynomial.map_*` and `SmoothPlaneCurve.baseChange_aᵢ` (the base-change of Weierstrass coefficients).
- **Hypotheses**: `C : SmoothPlaneCurve K`, `L / K` a field extension.
- **Uses from project**: `coordRingMap_smul_basis` (this file), `SmoothPlaneCurve.baseChange_a₁`, `SmoothPlaneCurve.baseChange_a₂`, `SmoothPlaneCurve.baseChange_a₃`, `SmoothPlaneCurve.baseChange_a₄`, `SmoothPlaneCurve.baseChange_a₆` (from `BaseChange.lean`). Uses mathlib `CoordinateRing.exists_smul_basis_eq`, `CoordinateRing.norm_smul_basis`.
- **Used by**: `ordAtInfty_algebraMap_coordRingMap` (this file).
- **Visibility**: public
- **Lines**: 68–77 (proof lines 71–77, ~7 lines)
- **Notes**: Core norm-transport step. The `simp` discharges via the explicit Weierstrass polynomial identity after both sides are expanded. No sorry.

---

### `theorem ordAtInfty_algebraMap_coordRingMap`

- **Type**:
  ```
  (u : C.CoordinateRing) →
    (C.baseChange L).ordAtInfty
        (algebraMap (C.baseChange L).CoordinateRing (C.baseChange L).FunctionField
          (C.coordRingMap L u)) =
      C.ordAtInfty (algebraMap C.CoordinateRing C.FunctionField u)
  ```
- **What**: The order at infinity of an integral element is preserved by base change: applying `coordRingMap` then `algebraMap` into the function field gives the same `ord_∞` as over `K`. This is the integral-element version of the main theorem.
- **How**: Handles `u = 0` by `simp`; for `u ≠ 0`, uses `SmoothPlaneCurve.ordAtInfty_algebraMap_coordinateRing` (from `Infinity.lean`) on both sides to reduce to `−natDegree(N(u))`; then applies `norm_coordRingMap` and `Polynomial.natDegree_map_eq_of_injective` (mathlib) with `FaithfulSMul.algebraMap_injective K L`. Also uses `C.coordRingMap_injective L` to establish `coordRingMap u ≠ 0`.
- **Hypotheses**: `C : SmoothPlaneCurve K`, `L / K` a field extension.
- **Uses from project**: `norm_coordRingMap` (this file), `SmoothPlaneCurve.ordAtInfty_algebraMap_coordinateRing` (from `Infinity.lean`), `SmoothPlaneCurve.coordRingMap_injective` (from `CurveMapBaseChange.lean`). Uses mathlib `Polynomial.natDegree_map_eq_of_injective`, `FaithfulSMul.algebraMap_injective`.
- **Used by**: `ordAtInfty_functionFieldMap` (this file).
- **Visibility**: public
- **Lines**: 82–93 (proof lines 87–93, ~7 lines)
- **Notes**: Clean two-case proof. The `u = 0` case uses `simp` (both sides are 0/`ordAtInfty_zero`). No sorry.

---

### `theorem ordAtInfty_functionFieldMap`

- **Type**:
  ```
  (z : C.FunctionField) (hz : z ≠ 0) →
    (C.baseChange L).ordAtInfty (C.functionFieldMap L z) = C.ordAtInfty z
  ```
- **What**: The main theorem: the order at infinity of a nonzero function-field element is preserved by the base-change map `functionFieldMap : K(C) → L(C_L)`.
- **How**: Decomposes `z = algebraMap u / algebraMap v` via `IsFractionRing.div_surjective`; establishes `u ≠ 0`, `v ≠ 0`, and their images are nonzero via `IsFractionRing.injective`; rewrites both sides using `ordAtInfty_div_eq_mul_inv` + `ordAtInfty_inv` (from `Infinity.lean`) to express `ord(z) = ord(u) − ord(v)`; applies `functionFieldMap_algebraMap` (from `CurveMapBaseChange.lean`) + `map_div₀`; then closes each integral term by `ordAtInfty_algebraMap_coordRingMap`.
- **Hypotheses**: `C : SmoothPlaneCurve K`, `L / K` a field extension, `z : C.FunctionField`, `hz : z ≠ 0`.
- **Uses from project**: `ordAtInfty_algebraMap_coordRingMap` (this file), `SmoothPlaneCurve.ordAtInfty_div_eq_mul_inv`, `SmoothPlaneCurve.ordAtInfty_inv` (from `Infinity.lean`), `SmoothPlaneCurve.functionFieldMap_algebraMap` (from `CurveMapBaseChange.lean`), `SmoothPlaneCurve.coordRingMap_injective` (from `CurveMapBaseChange.lean`). Uses mathlib `IsFractionRing.div_surjective`, `IsFractionRing.injective`, `map_ne_zero_iff`, `nonZeroDivisors.ne_zero`, `map_div₀`.
- **Used by**: `HasseWeil.WeilPairing.OneSubInftyResidues.ordAtInftyBaseChange_discharged` (in `WeilPairing/OneSubInftyResidues.lean`). Unused within this file.
- **Visibility**: public
- **Lines**: 101–125 (proof lines 102–124, ~23 lines)
- **Notes**: The capstone theorem of the file. Proof is 23 lines — substantial but under the 30-line threshold. Uses four `have` statements to establish non-vanishing of mapped elements. No sorry.

---

## Cross-reference summary

| Declaration | Uses (project) | Used by (in file) |
|---|---|---|
| `coordRingMap_smul_basis` | `coordRingMap`, `baseChange` | `norm_coordRingMap` |
| `norm_coordRingMap` | `coordRingMap_smul_basis`, `baseChange_aᵢ` | `ordAtInfty_algebraMap_coordRingMap` |
| `ordAtInfty_algebraMap_coordRingMap` | `norm_coordRingMap`, `ordAtInfty_algebraMap_coordinateRing`, `coordRingMap_injective` | `ordAtInfty_functionFieldMap` |
| `ordAtInfty_functionFieldMap` | `ordAtInfty_algebraMap_coordRingMap`, `ordAtInfty_div_eq_mul_inv`, `ordAtInfty_inv`, `functionFieldMap_algebraMap`, `coordRingMap_injective` | (none in this file; used by `OneSubInftyResidues`) |

**Key API** (used by ≥ 3 others in file): none meets the ≥ 3 threshold; `ordAtInfty_algebraMap_coordRingMap` is used by 1 other in-file caller (`ordAtInfty_functionFieldMap`).

**Unused in file** (no in-file callers): `ordAtInfty_functionFieldMap` (exported; consumed by `OneSubInftyResidues.lean`).

## Notes

- No `set_option maxHeartbeats` override; only `set_option linter.style.longLine false`.
- All 4 theorems are axiom-clean (no sorry, no admitted).
- The file is a focused 3-step pipeline: basis transport → norm transport → fraction-field transport. Structurally mirrors `FrobeniusDivisorGalois.lean` which contains explicit comments noting it as the "mirror" of these three theorems for the Frobenius σ setting.
