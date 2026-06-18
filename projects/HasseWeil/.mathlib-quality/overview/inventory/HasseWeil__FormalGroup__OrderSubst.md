# Inventory: ./HasseWeil/FormalGroup/OrderSubst.lean

**File**: `HasseWeil/FormalGroup/OrderSubst.lean`
**Module**: `PowerSeries` namespace
**Lines**: 1–134
**Purpose**: Proves that the order of a power series substitution equals the product of orders: `order (subst f g) = order g * order f`, strengthening the mathlib inequality `PowerSeries.le_order_subst`.

---

## Declarations

### `private lemma constantCoeff_subst_univariate`

- **Type**: `{f : PowerSeries R} → constantCoeff f = 0 → ∀ g : PowerSeries R, constantCoeff (subst f g) = constantCoeff g`
- **What**: The constant coefficient of a substitution `subst f g` equals the constant coefficient of `g`, when `f` has zero constant coefficient. This is the key lemma that allows case-splitting on whether `g` has zero constant coefficient.
- **How**: Rewrites using `coeff_subst'` (the coefficient formula for substitutions) and `finsum_eq_single` to isolate the `d=0` term; the remaining terms vanish because `coeff 0 (f^d) = 0^d = 0` when `constantCoeff f = 0`.
- **Hypotheses**: `R` is a commutative ring; `constantCoeff f = 0` (needed so `HasSubst f` holds).
- **Uses from project**: none
- **Used by**: `order_subst` (used twice: once in the `constantCoeff g = 0` subcase and once in the `constantCoeff g ≠ 0` subcase)
- **Visibility**: private
- **Lines**: 37–48, proof length ~12 lines
- **Notes**: Private helper; no `maxHeartbeats` setting.

---

### `theorem order_subst`

- **Type**: `[NoZeroDivisors R] → {f g : PowerSeries R} → constantCoeff f = 0 → order (subst f g) = order g * order f`
- **What**: The order of the power series substitution `subst f g` equals `order g * order f` (in `ℕ∞`), under the hypothesis that `f` has vanishing constant coefficient and `R` has no zero divisors. This sharpens the mathlib lemma `PowerSeries.le_order_subst` from `≤` to `=`.
- **How**: Proceeds by three-way case split: (1) trivial ring (both sides `⊤`); (2) `g = 0` (both sides `⊤`, using `ENat.top_mul` and `order_ne_zero_iff_constCoeff_eq_zero`); (3) `g ≠ 0, constantCoeff g = 0` (the main case: decomposes `g = X^n * g'` via `X_pow_order_mul_divXPowOrder`, then uses `subst_mul`/`subst_pow`/`subst_X` to compute `subst f g = f^n * subst f g'`, then `order_mul`, `order_pow`, `coe_toNat_order`); (4) `constantCoeff g ≠ 0` (both sides `0`, via `order_le` at index 0). Key mathlib lemmas used: `X_pow_order_mul_divXPowOrder`, `constantCoeff_divXPowOrder`, `coeff_order`, `order_mul`, `order_pow`, `coe_toNat_order`, `ENat.top_mul`.
- **Hypotheses**: `R` is a commutative ring with no zero divisors (`[NoZeroDivisors R]`); `constantCoeff f = 0` (so `HasSubst f` holds and the substitution is well-defined).
- **Uses from project**: `constantCoeff_subst_univariate` (private lemma in this file)
- **Used by**: `HasseWeil.FormalGroup.Height` (imported via `import HasseWeil.FormalGroup.OrderSubst`; used in `Height.lean` line 141 as `PowerSeries.order_subst f.zero_const`)
- **Visibility**: public
- **Lines**: 57–133, proof length ~77 lines
- **Notes**: Proof is >30 lines. No `set_option maxHeartbeats`. No `sorry`. This strengthens mathlib's `PowerSeries.le_order_subst`; the equality version is likely a mathlib-contribution candidate (the module docstring notes it "complements" that lemma). The `NoZeroDivisors` hypothesis is used implicitly via `order_mul` (which requires it to ensure `order (a * b) = order a + order b`).

---

## Summary Statistics

| Category | Count |
|---|---|
| Total declarations | 2 |
| `def` / `abbrev` / `noncomputable def` | 0 |
| `lemma` / `theorem` | 2 |
| `instance` | 0 |
| `sorry` occurrences | 0 |
| `set_option maxHeartbeats` | 0 |
| Long proofs (>30 lines) | 1 (`order_subst`, ~77 lines) |

## Key API

- `order_subst`: the main public theorem; used by `Height.lean`.

## Unused in file

- `order_subst` is the public export; it is not called by anything within this file (its only consumer is `Height.lean`).
- `constantCoeff_subst_univariate` is private and used only within `order_subst`.

## Notes

This is a focused, self-contained file with exactly two declarations. It is a direct precursor to `Height.lean` (the formal group height additivity theorem). The result is a natural strengthening of mathlib's `le_order_subst`; it may be a mathlib-contribution candidate. No sorries, no heartbeat overrides, clean imports.
