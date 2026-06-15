# Inventory: ./HasseWeil/HahnSeriesAux.lean

**File summary:** 87 lines, 4 declarations, all theorems, no instances, no sorry, no `set_option maxHeartbeats`. Module-level docstring marks these as mathlib upstream candidates.

---

### `theorem orderTop_inv_eq_neg`

- **Type**: `{s : HahnSeries Γ R} (hs : s ≠ 0) : s⁻¹.orderTop = -s.orderTop`
- **What**: The `orderTop` of the inverse of a nonzero Hahn series over a field is the negation of the original `orderTop`.
- **How**: From `s · s⁻¹ = 1`, apply `HahnSeries.orderTop_mul` to get `s.orderTop + s⁻¹.orderTop = 0`; lift both `orderTop` values from `WithTop Γ` to `Γ` using `orderTop_ne_top`, then solve the additive equation in `Γ` via `eq_neg_of_add_eq_zero_left`.
- **Hypotheses**: `Γ` is an ordered add-comm group with `LinearOrder` and `IsOrderedAddMonoid`; `R` is a field; `s ≠ 0`.
- **Uses from project**: none
- **Used by**: `orderTop_div` (in this file)
- **Visibility**: public
- **Lines**: 33–52, proof ~19 lines
- **Notes**: Marked as mathlib upstream candidate in module docstring.

---

### `theorem orderTop_div`

- **Type**: `{s t : HahnSeries Γ R} (ht : t ≠ 0) : (s / t).orderTop = s.orderTop - t.orderTop`
- **What**: The `orderTop` of a quotient of Hahn series equals the difference of their `orderTop` values.
- **How**: Rewrites `s / t = s · t⁻¹`, applies `HahnSeries.orderTop_mul`, then `orderTop_inv_eq_neg`, and uses `sub_eq_add_neg`. Two-line proof.
- **Hypotheses**: Same ordered-group + field typeclass context; `t ≠ 0`.
- **Uses from project**: `orderTop_inv_eq_neg` (this file)
- **Used by**: Used by `HasseWeil/BridgeMulByInt.lean` and `HasseWeil/AdditionPullback/SilvermanIV14.lean`; unused within this file after its own definition.
- **Visibility**: public
- **Lines**: 58–61, proof 2 lines
- **Notes**: Mathlib upstream candidate.

---

### `theorem leadingCoeff_inv`

- **Type**: `{s : HahnSeries Γ R} (hs : s ≠ 0) : s⁻¹.leadingCoeff = s.leadingCoeff⁻¹`
- **What**: The leading coefficient of the inverse of a nonzero Hahn series equals the multiplicative inverse of the original leading coefficient.
- **How**: From `s · s⁻¹ = 1`, uses `HahnSeries.leadingCoeff_mul` to get `s.leadingCoeff * s⁻¹.leadingCoeff = 1`; concludes by `eq_inv_of_mul_eq_one_left`.
- **Hypotheses**: Same ordered-group + field context; `s ≠ 0`.
- **Uses from project**: none
- **Used by**: `leadingCoeff_div` (in this file)
- **Visibility**: public
- **Lines**: 68–75, proof 7 lines
- **Notes**: Mathlib upstream candidate.

---

### `theorem leadingCoeff_div`

- **Type**: `{s t : HahnSeries Γ R} (ht : t ≠ 0) : (s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff`
- **What**: The leading coefficient of a quotient of Hahn series equals the quotient of the leading coefficients.
- **How**: Rewrites `s / t = s · t⁻¹`, applies `HahnSeries.leadingCoeff_mul` and `leadingCoeff_inv`, then folds `div_eq_mul_inv`. Two-line proof.
- **Hypotheses**: Same ordered-group + field context; `t ≠ 0`.
- **Uses from project**: `leadingCoeff_inv` (this file)
- **Used by**: Used by `HasseWeil/BridgeMulByInt.lean` and `HasseWeil/AdditionPullback/SilvermanIV14.lean`; unused within this file after its own definition.
- **Visibility**: public
- **Lines**: 81–84, proof 2 lines
- **Notes**: Mathlib upstream candidate.
