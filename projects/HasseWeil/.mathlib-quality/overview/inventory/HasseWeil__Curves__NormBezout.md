# Inventory: ./HasseWeil/Curves/NormBezout.lean

**File purpose.** Defines the algebra norm `N : K(C) → Frac(F[X])` for the finite extension of function fields of a smooth plane curve over a field `F`, and proves its basic properties (multiplicativity, zero-iff-zero, algebraMap formula). Closes infrastructure ticket T-II-INFRA-D-003; foundational for the Bezout-counting argument in T-II-1-004.

**Imports.** `HasseWeil.Curves.FiniteOverKx` (for `FunctionField`, `finrank_functionField_over_fracPolynomialX`), `Mathlib.RingTheory.Norm.Basic`.

**Namespace.** `HasseWeil.Curves.SmoothPlaneCurve`.

---

### `noncomputable def fieldNorm`
- **Type**: `(f : C.FunctionField) → FractionRing (Polynomial F)`
- **What**: The algebra norm `N : K(C) → Frac(F[X])` — sends `f` to the determinant of the `Frac(F[X])`-linear multiplication-by-`f` endomorphism on `K(C)`.
- **How**: Literally `Algebra.norm (FractionRing (Polynomial F)) f`; the finite-extension structure is synthesised from `FiniteOverKx`.
- **Hypotheses**: `C : SmoothPlaneCurve F`, `F` a field.
- **Uses from project**: `C.FunctionField` (via `FiniteOverKx`).
- **Used by**: `fieldNorm_one`, `fieldNorm_mul`, `fieldNorm_pow`, `fieldNorm_eq_zero_iff`, `fieldNorm_ne_zero_iff`, `fieldNorm_zero`, `fieldNorm_algebraMap`, `fieldNorm_ne_zero` (all in this file); `normAsRatFunc` in `Infinity.lean`; also referenced in `NormValuation.lean`.
- **Visibility**: public
- **Lines**: 36–37, proof length: 1 (definitional)
- **Notes**: `noncomputable` as expected (field norm via determinant).

---

### `@[simp] theorem fieldNorm_one`
- **Type**: `C.fieldNorm 1 = 1`
- **What**: The norm of 1 is 1; i.e. `N` preserves the multiplicative identity.
- **How**: `map_one _` — directly from the ring-hom / monoid-hom API of `Algebra.norm`.
- **Hypotheses**: none beyond the variable context.
- **Uses from project**: `fieldNorm`.
- **Used by**: unused in this file (exported).
- **Visibility**: public
- **Lines**: 39, proof length: 1
- **Notes**: `@[simp]` tagged.

---

### `@[simp] theorem fieldNorm_mul`
- **Type**: `C.fieldNorm (f * g) = C.fieldNorm f * C.fieldNorm g`
- **What**: The norm is multiplicative.
- **How**: `map_mul _ f g` — `Algebra.norm` is a `MonoidHom`.
- **Hypotheses**: `f g : C.FunctionField`.
- **Uses from project**: `fieldNorm`.
- **Used by**: unused in this file (exported; used in `Infinity.lean`).
- **Visibility**: public
- **Lines**: 41–43, proof length: 1
- **Notes**: `@[simp]` tagged.

---

### `theorem fieldNorm_pow`
- **Type**: `C.fieldNorm (f ^ n) = C.fieldNorm f ^ n`
- **What**: The norm of a power equals the power of the norm.
- **How**: `map_pow _ f n` — from the monoid-hom API.
- **Hypotheses**: `f : C.FunctionField`, `n : ℕ`.
- **Uses from project**: `fieldNorm`.
- **Used by**: unused in this file (exported).
- **Visibility**: public
- **Lines**: 45–46, proof length: 1
- **Notes**: none.

---

### `theorem fieldNorm_eq_zero_iff`
- **Type**: `C.fieldNorm f = 0 ↔ f = 0`
- **What**: The norm is zero if and only if the input is zero; equivalently `N` is "injective at zero", reflecting that `K(C)` is an integral domain (free module over the base).
- **How**: `Algebra.norm_eq_zero_iff` from mathlib, which requires the extension to be finite and separable / the base to be a field.
- **Hypotheses**: `f : C.FunctionField`.
- **Uses from project**: `fieldNorm`.
- **Used by**: `fieldNorm_ne_zero_iff`, `fieldNorm_zero`, `fieldNorm_ne_zero` (all in this file); `Infinity.lean` line 75.
- **Visibility**: public
- **Lines**: 50–52, proof length: 1
- **Notes**: none.

---

### `theorem fieldNorm_ne_zero_iff`
- **Type**: `C.fieldNorm f ≠ 0 ↔ f ≠ 0`
- **What**: Non-zero iff the input is non-zero; the contrapositive restatement of `fieldNorm_eq_zero_iff`.
- **How**: `not_iff_not.mpr (fieldNorm_eq_zero_iff C f)` — pure logic.
- **Hypotheses**: `f : C.FunctionField`.
- **Uses from project**: `fieldNorm`, `fieldNorm_eq_zero_iff`.
- **Used by**: `fieldNorm_ne_zero` (in this file).
- **Visibility**: public
- **Lines**: 54–55, proof length: 1
- **Notes**: none.

---

### `@[simp] theorem fieldNorm_zero`
- **Type**: `C.fieldNorm 0 = 0`
- **What**: The norm of 0 is 0.
- **How**: Applies `fieldNorm_eq_zero_iff` at `f = 0` and closes with `rfl`.
- **Hypotheses**: none beyond context.
- **Uses from project**: `fieldNorm`, `fieldNorm_eq_zero_iff`.
- **Used by**: unused in this file (exported).
- **Visibility**: public
- **Lines**: 57–58, proof length: 1
- **Notes**: `@[simp]` tagged.

---

### `theorem fieldNorm_algebraMap`
- **Type**: `C.fieldNorm (algebraMap (FractionRing (Polynomial F)) C.FunctionField r) = r ^ 2`
- **What**: The norm of a scalar `r ∈ Frac(F[X])` (embedded via `algebraMap`) equals `r²`, reflecting that `[K(C) : Frac(F[X])] = 2`.
- **How**: Uses `Algebra.norm_algebraMap` (which gives `r ^ finrank`) then rewrites with `finrank_functionField_over_fracPolynomialX` from `FiniteOverKx` to substitute `finrank = 2`.
- **Hypotheses**: `r : FractionRing (Polynomial F)`.
- **Uses from project**: `fieldNorm`, `finrank_functionField_over_fracPolynomialX` (from `FiniteOverKx`).
- **Used by**: unused in this file (exported; used heavily in `Infinity.lean` lines 129, 209, 287, 329, 350).
- **Visibility**: public
- **Lines**: 62–67, proof length: 4 (the `have h` + `rw`)
- **Notes**: The exponent `2` is a project-specific fact about the degree of the function-field extension; mathlib's `Algebra.norm_algebraMap` supplies the generic `r ^ finrank` form.

---

### `theorem fieldNorm_ne_zero`
- **Type**: `{f : C.FunctionField} → (hf : f ≠ 0) → C.fieldNorm f ≠ 0`
- **What**: If `f` is nonzero then its norm is nonzero; the implicit-argument convenience form of `fieldNorm_ne_zero_iff`.
- **How**: Immediate from `fieldNorm_ne_zero_iff` via `mpr`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `fieldNorm`, `fieldNorm_ne_zero_iff`.
- **Used by**: unused in this file (exported).
- **Visibility**: public
- **Lines**: 70–71, proof length: 1
- **Notes**: none.

---

## Summary

| Metric | Value |
|---|---|
| Total declarations | 9 |
| `def` / `noncomputable def` | 1 |
| `theorem` / `@[simp] theorem` | 8 |
| `instance` | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Proofs > 30 lines | 0 |

**Key API** (used by ≥ 3 other declarations in file): `fieldNorm` (used by all 8 theorems), `fieldNorm_eq_zero_iff` (used by `fieldNorm_ne_zero_iff`, `fieldNorm_zero`, `fieldNorm_ne_zero`).

**Unused in file** (potential dead code candidates from this file's perspective — all are used externally): `fieldNorm_one`, `fieldNorm_mul`, `fieldNorm_pow`, `fieldNorm_zero`, `fieldNorm_algebraMap`, `fieldNorm_ne_zero` — all are exported API consumed by `Infinity.lean` and `NormValuation.lean`.

**Notes**: This is a thin wrapper layer; the mathematical content is entirely delegated to `Algebra.norm` from mathlib plus the one project-specific fact `finrank_functionField_over_fracPolynomialX`. No sorry, no heartbeat overrides, no long proofs. Suspected mathlib-complete for the algebraic norm setup; the only project-specific glue is the degree-2 finrank fact.
