# Inventory: ./HasseWeil/PowerSeriesHelpers.lean

**File summary**: 49 lines. Auxiliary power-series lemmas not yet in mathlib, intended for use in
formal-group uniqueness arguments. Two theorems, no instances, no defs.

---

### `theorem PowerSeries.eq_zero_of_self_eq_mul_self`

- **Type**: `{R : Type*} [Semiring R] {f g : R⟦X⟧} → constantCoeff g = 0 → f = g * f → f = 0`
- **What**: Self-multiplication cancellation in `R⟦X⟧`: if `f = g * f` and the constant term of
  `g` is zero, then `f = 0`.
- **How**: By contradiction. Uses `one_le_order_iff_constCoeff_eq_zero` to get `1 ≤ order g`, then
  `le_order_mul` to get `order g + order f ≤ order (g * f)`. Substituting `g * f = f` gives
  `order f + 1 ≤ order f`, which contradicts `ENat.add_one_le_iff` together with `order_eq_top`
  (since `f ≠ 0`).
- **Hypotheses**: `R` is a semiring; `constantCoeff R g = 0`.
- **Uses from project**: none.
- **Used by**: `eq_zero_of_self_eq_self_mul` (this file); also referenced by
  `HasseWeil/FormalGroup.lean` (comment at L445 cites this lemma for `formalW_unique`).
- **Visibility**: public
- **Lines**: 31–41, proof length ≈ 9 lines.
- **Notes**: No `sorry`. No `set_option maxHeartbeats`. Short proof. Likely a mathlib-gap lemma
  (not duplicated in mathlib as of filing).

---

### `theorem PowerSeries.eq_zero_of_self_eq_self_mul`

- **Type**: `{R : Type*} [CommSemiring R] {f g : R⟦X⟧} → constantCoeff g = 0 → f = f * g → f = 0`
- **What**: Commutative variant: if `f = f * g` and the constant term of `g` is zero, then `f = 0`.
- **How**: One-liner: applies `eq_zero_of_self_eq_mul_self` after rewriting `f * g` as `g * f` via
  `mul_comm`.
- **Hypotheses**: `R` is a commutative semiring; `constantCoeff R g = 0`.
- **Uses from project**: `eq_zero_of_self_eq_mul_self` (this file).
- **Used by**: unused within this file; intended for downstream callers.
- **Visibility**: public
- **Lines**: 45–47, proof length 1 line (term-mode).
- **Notes**: No `sorry`. No `set_option maxHeartbeats`. Requires `CommSemiring` (not just
  `Semiring`) because it uses `mul_comm`. Suspected mathlib-gap fill.
