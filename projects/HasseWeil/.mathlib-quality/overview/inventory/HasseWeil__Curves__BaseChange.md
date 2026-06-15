# Inventory: ./HasseWeil/Curves/BaseChange.lean

**File**: `HasseWeil/Curves/BaseChange.lean`
**Module**: `HasseWeil.Curves.SmoothPlaneCurve`
**Lines**: 1–84
**Purpose**: Defines base change `C.baseChange L : SmoothPlaneCurve L` for a smooth plane curve `C/F` along an `F`-algebra `L`, together with the rational-points abbreviation `pointsOver` and the coercion `includePoint`.

---

## Declaration Inventory

---

### `noncomputable def baseChange`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → SmoothPlaneCurve L`
- **What**: Constructs the base change of a smooth plane curve `C/F` to a field extension `L/F` by applying `WeierstrassCurve.Affine.baseChange L` to the underlying Weierstrass affine data.
- **How**: One-field structure construction; sets `toAffine := C.toAffine.baseChange L` directly via mathlib's `WeierstrassCurve.Affine.baseChange`. The `SmoothPlaneCurve` structure has only a single field `toAffine`, so no smoothness proof is needed separately (it is inherited from the mathlib definition).
- **Hypotheses**: `C : SmoothPlaneCurve F`, `F` a field, `L` a field with an `F`-algebra structure.
- **Uses from project**: `SmoothPlaneCurve` (structure definition, `Curves/Basic.lean`).
- **Used by**: `baseChange_toAffine`, `baseChange_a₁`, `baseChange_a₂`, `baseChange_a₃`, `baseChange_a₄`, `baseChange_a₆`, `pointsOver`, `includePoint`; widely used in other project files (`IsogenyBaseChange.lean`, `GaloisAction.lean`, `OrdAtInftyBaseChange.lean`, etc.).
- **Visibility**: public
- **Lines**: 35–38, proof length ~3 lines (structure body)
- **Notes**: None.

---

### `@[simp] theorem baseChange_toAffine`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (C.baseChange L).toAffine = C.toAffine.baseChange L`
- **What**: States that the `toAffine` field of `C.baseChange L` equals mathlib's `WeierstrassCurve.Affine.baseChange L` applied to `C.toAffine`. A `simp` unfolding lemma.
- **How**: `rfl` — definitionally true by construction.
- **Hypotheses**: Same as `baseChange`.
- **Uses from project**: `baseChange` (implicitly, as the LHS unfolds to it).
- **Used by**: Unused within this file; exported as a `simp` lemma for downstream files.
- **Visibility**: public
- **Lines**: 39–40, proof length 1 line
- **Notes**: None.

---

### `@[simp] theorem baseChange_a₁`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (C.baseChange L).toAffine.a₁ = algebraMap F L C.toAffine.a₁`
- **What**: The `a₁` coefficient of the base-changed curve is `algebraMap F L` applied to the original `a₁`. Simp unfolding.
- **How**: `rfl` — follows from mathlib's definition of `WeierstrassCurve.Affine.baseChange`.
- **Hypotheses**: Same as `baseChange`.
- **Uses from project**: `baseChange`.
- **Used by**: Unused within this file; used in `OrdAtInftyBaseChange.lean`.
- **Visibility**: public
- **Lines**: 42–43, proof length 1 line
- **Notes**: None.

---

### `@[simp] theorem baseChange_a₂`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (C.baseChange L).toAffine.a₂ = algebraMap F L C.toAffine.a₂`
- **What**: The `a₂` coefficient of the base-changed curve is `algebraMap F L` applied to the original `a₂`. Simp unfolding.
- **How**: `rfl`.
- **Hypotheses**: Same as `baseChange`.
- **Uses from project**: `baseChange`.
- **Used by**: Unused within this file; used in `OrdAtInftyBaseChange.lean`.
- **Visibility**: public
- **Lines**: 45–46, proof length 1 line
- **Notes**: None.

---

### `@[simp] theorem baseChange_a₃`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (C.baseChange L).toAffine.a₃ = algebraMap F L C.toAffine.a₃`
- **What**: The `a₃` coefficient of the base-changed curve is `algebraMap F L` applied to the original `a₃`. Simp unfolding.
- **How**: `rfl`.
- **Hypotheses**: Same as `baseChange`.
- **Uses from project**: `baseChange`.
- **Used by**: Unused within this file; used in `OrdAtInftyBaseChange.lean`.
- **Visibility**: public
- **Lines**: 48–49, proof length 1 line
- **Notes**: None.

---

### `@[simp] theorem baseChange_a₄`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (C.baseChange L).toAffine.a₄ = algebraMap F L C.toAffine.a₄`
- **What**: The `a₄` coefficient of the base-changed curve is `algebraMap F L` applied to the original `a₄`. Simp unfolding.
- **How**: `rfl`.
- **Hypotheses**: Same as `baseChange`.
- **Uses from project**: `baseChange`.
- **Used by**: Unused within this file; used in `OrdAtInftyBaseChange.lean`.
- **Visibility**: public
- **Lines**: 51–52, proof length 1 line
- **Notes**: None.

---

### `@[simp] theorem baseChange_a₆`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (C.baseChange L).toAffine.a₆ = algebraMap F L C.toAffine.a₆`
- **What**: The `a₆` coefficient of the base-changed curve is `algebraMap F L` applied to the original `a₆`. Simp unfolding.
- **How**: `rfl`.
- **Hypotheses**: Same as `baseChange`.
- **Uses from project**: `baseChange`.
- **Used by**: Unused within this file; used in `OrdAtInftyBaseChange.lean`.
- **Visibility**: public
- **Lines**: 54–55, proof length 1 line
- **Notes**: None.

---

### `abbrev pointsOver`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → Type _`
- **What**: An abbreviation for `(C.baseChange L).SmoothPoint`, i.e., the smooth `L`-rational points of the base change. Corresponds to the notation `C(L)` or `V(L)` in Silverman I.2.
- **How**: Pure abbreviation; unfolds to `(C.baseChange L).SmoothPoint`.
- **Hypotheses**: Same as `baseChange`.
- **Uses from project**: `baseChange`, `SmoothPoint` (from `Curves/Basic.lean`).
- **Used by**: `includePoint`, `includePoint_x`, `includePoint_y`; used in `Curves/GaloisAction.lean`.
- **Visibility**: public
- **Lines**: 62–63, 2 lines
- **Notes**: Declared as `abbrev` so it is transparent to the elaborator.

---

### `noncomputable def includePoint`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → C.SmoothPoint → C.pointsOver L`
- **What**: Sends an `F`-rational smooth point `P` to its image in `C.pointsOver L` by applying `algebraMap F L` to both coordinates; the nonsingularity condition is transferred using mathlib's `Affine.map_nonsingular`.
- **How**: Builds `x := algebraMap F L P.x`, `y := algebraMap F L P.y`, nonsingularity via `(Affine.map_nonsingular (f := algebraMap F L) (x := P.x) (y := P.y) (FaithfulSMul.algebraMap_injective F L)).mpr P.nonsingular`. The key mathlib lemma is `WeierstrassCurve.Affine.map_nonsingular` which states nonsingularity is preserved by injective ring maps.
- **Hypotheses**: `C : SmoothPlaneCurve F`, fields `F`, `L`, `F`-algebra structure on `L` (must be faithful, i.e., `algebraMap F L` is injective, which follows from `FaithfulSMul`).
- **Uses from project**: `pointsOver`, `SmoothPoint` (from `Curves/Basic.lean`).
- **Used by**: `includePoint_x`, `includePoint_y`; used in `GaloisAction.lean`.
- **Visibility**: public
- **Lines**: 67–73, proof length ~6 lines (structure body with 3 fields)
- **Notes**: Requires `FaithfulSMul F L` to obtain injectivity of `algebraMap F L`. No `sorry`.

---

### `@[simp] theorem includePoint_x`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (P : C.SmoothPoint) → (C.includePoint L P).x = algebraMap F L P.x`
- **What**: The `x`-coordinate of the included point equals `algebraMap F L P.x`. Simp lemma.
- **How**: `rfl`.
- **Hypotheses**: Same as `includePoint`.
- **Uses from project**: `includePoint`.
- **Used by**: Unused within this file; exported for downstream use.
- **Visibility**: public
- **Lines**: 75–76, proof length 1 line
- **Notes**: None.

---

### `@[simp] theorem includePoint_y`

- **Type**: `(C : SmoothPlaneCurve F) → (L : Type*) → [Field L] → [Algebra F L] → (P : C.SmoothPoint) → (C.includePoint L P).y = algebraMap F L P.y`
- **What**: The `y`-coordinate of the included point equals `algebraMap F L P.y`. Simp lemma.
- **How**: `rfl`.
- **Hypotheses**: Same as `includePoint`.
- **Uses from project**: `includePoint`.
- **Used by**: Unused within this file; exported for downstream use.
- **Visibility**: public
- **Lines**: 78–79, proof length 1 line
- **Notes**: None.

---

## Summary statistics

| Category | Count |
|---|---|
| `noncomputable def` | 2 (`baseChange`, `includePoint`) |
| `abbrev` | 1 (`pointsOver`) |
| `theorem` / `@[simp] theorem` | 7 (`baseChange_toAffine`, `baseChange_a₁`, `baseChange_a₂`, `baseChange_a₃`, `baseChange_a₄`, `baseChange_a₆`, `includePoint_x`, `includePoint_y`) — note `includePoint_y` makes 8 total named declarations, with 2 defs, 1 abbrev, 7 simp lemmas |
| Instances | 0 |
| `sorry` | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 0 |

**Key API**: `baseChange` is referenced by every other declaration in the file and is the main export used across many downstream files. `pointsOver` is used by 3 other declarations in this file (`includePoint`, `includePoint_x`, `includePoint_y`) and by `GaloisAction.lean`.

**Unused in file** (not referenced by other declarations within this file): `baseChange_toAffine`, `baseChange_a₁`, `baseChange_a₂`, `baseChange_a₃`, `baseChange_a₄`, `baseChange_a₆`, `includePoint_x`, `includePoint_y` — these are exported simp lemmas consumed by other files.
