# Inventory: ./HasseWeil/HasseBound.lean

**File**: `HasseWeil/HasseBound.lean`  
**Total declarations**: 2  
**Imports**: `HasseWeil.DegreeQuadraticForm`, `HasseWeil.Frobenius`, `Mathlib.Analysis.SpecialFunctions.Pow.Real`  
**Namespace**: `HasseWeil`

---

## Overview

This is a small, self-contained file containing only two pure-algebra lemmas that underpin the Hasse bound proof. The file has been pruned of its former geometric content (the now-deleted `traceOfFrobenius_sq_le`, `hasse_bound`, `hasse_bound_sq` which were built on a placeholder isogeny). What remains is a discriminant inequality and its translation to a real absolute-value bound. Both lemmas are consumed by `HasseWeil/Hasse/BoundOfWitnesses.lean` and `HasseWeil/Hasse/QuadraticForm.lean`.

---

## Declarations

### `theorem trace_sq_le_four_mul_deg`

- **Type**: `(q : ℕ) → (t : ℤ) → 0 < q → (∀ r s : ℤ, 0 ≤ (q : ℤ) * r ^ 2 - t * r * s + s ^ 2) → t ^ 2 ≤ 4 * (q : ℤ)`
- **What**: Given that the quadratic form `q·r² − t·r·s + s²` is non-negative for all integers `r, s`, concludes `t² ≤ 4q`. This is the discriminant-non-positivity step (negative discriminant iff `t² − 4q < 0`).
- **How**: By contradiction (`by_contra`/`push_neg`). Specialises the non-negativity hypothesis at `r = t`, `s = 2q`, producing an integer inequality, then closes by `nlinarith` using `sq_nonneg t`, `sq_nonneg (q : ℤ)`, and `mul_self_nonneg`.
- **Hypotheses**: `q` a positive natural number; for all integers `r, s` the quadratic form is ≥ 0.
- **Uses from project**: none
- **Used by**: `HasseWeil.Hasse.BoundOfWitnesses` (line 62), `HasseWeil.Hasse.QuadraticForm` (line 56) — both outside this file; **unused within this file**.
- **Visibility**: public
- **Lines**: 33–40 (proof body lines 36–40, ~5 lines)
- **Notes**: Clean, short `nlinarith` proof; no `sorry`; no `maxHeartbeats` override.

---

### `theorem abs_le_two_sqrt_of_sq_le`

- **Type**: `(q : ℕ) → (t : ℤ) → t ^ 2 ≤ 4 * (q : ℝ) → |(t : ℝ)| ≤ 2 * Real.sqrt (q : ℝ)`
- **What**: If `t² ≤ 4q` holds over `ℤ`, then the real absolute value `|t| ≤ 2√q`. This bridges the integer discriminant bound to the real-valued Hasse inequality.
- **How**: Casts the integer inequality to `ℝ`, rewrites `(2√q)² = 4q` using `sq_sqrt` + `mul_pow`, and applies the mathlib lemma `abs_le_of_sq_le_sq'` to conclude the absolute-value bound.
- **Hypotheses**: `t² ≤ 4q` as integers (no positivity of `q` required explicitly, though `sqrt` is used on the implicit `q ≥ 0` from `Nat.cast_nonneg'`).
- **Uses from project**: none
- **Used by**: `HasseWeil.Hasse.BoundOfWitnesses` (line 89), `HasseWeil.Hasse.QuadraticForm` (line 73) — both outside this file; **unused within this file**.
- **Visibility**: public
- **Lines**: 43–52 (proof body lines 46–52, ~7 lines)
- **Notes**: Uses `Mathlib.Analysis.SpecialFunctions.Pow.Real` for `Real.sqrt` and `abs_le_of_sq_le_sq'`. No `sorry`; no `maxHeartbeats` override. No intra-file cross-references.

---

## Summary

| Metric | Value |
|--------|-------|
| Total declarations | 2 |
| `def` / `noncomputable def` / `abbrev` | 0 |
| `lemma` / `theorem` | 2 |
| `instance` / `structure` / `class` | 0 |
| `sorry` | 0 |
| `set_option maxHeartbeats` | 0 |
| Proofs > 30 lines | 0 |
| Unused within file | both (both exported to other files) |
| Key API (used by 3+ others in file) | none |
