# Inventory: ./HasseWeil/Curves/WithTopArith.lean

**Import**: `HasseWeil.Curves.Infinity`
**Namespace**: `HasseWeil.Curves.SmoothPlaneCurve`
**Variable context**: `{F : Type*} [Field F] (C : SmoothPlaneCurve F)`

This file is a focused helper module providing closed-form one-liners for `WithTop ℤ` arithmetic
that arise in `ordAtInfty` calculations. It consolidates repetitive `WithTop` rewrite chains
and provides six thin wrappers/lemmas. No sorries, no `set_option maxHeartbeats`.

---

## Declarations

---

### `theorem coe_add_coe`

- **Type**: `(a b : ℤ) : ((a : ℤ) : WithTop ℤ) + ((b : ℤ) : WithTop ℤ) = (((a + b : ℤ)) : WithTop ℤ)`
- **What**: States that the sum of two `ℤ`-casts in `WithTop ℤ` equals the cast of their sum; essentially `WithTop.coe_add` in simp-friendly form.
- **How**: One-liner via `rw [← WithTop.coe_add]` (mathlib `WithTop.coe_add`).
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: unused in file; used externally in `FormalIsogenySeries.lean`, `AdditionPullback/Frobenius.lean`, etc. via the `@[simp]` attribute
- **Visibility**: public
- **Lines**: 79–82, proof length 1 line
- **Notes**: Tagged `@[simp]`. Thin wrapper; likely duplicates or is superseded by `WithTop.coe_add` in mathlib (the doc notes it "avoids unification glitches").

---

### `theorem coe_neg_coe`

- **Type**: `(a : ℤ) : -(((a : ℤ)) : WithTop ℤ) = (((-a : ℤ)) : WithTop ℤ)`
- **What**: States that negation of a `ℤ`-cast in `WithTop ℤ` equals the cast of the negation; cast and negation commute.
- **How**: Proved by `rfl` (definitional equality).
- **Hypotheses**: None.
- **Uses from project**: none
- **Used by**: unused in file; no external callers found by grep
- **Visibility**: public
- **Lines**: 84–85, proof length 1 line (term-mode)
- **Notes**: Tagged `@[simp]`. No external callers found in the project — potential dead code candidate.

---

### `theorem ord_div_concrete`

- **Type**: `{a b : C.FunctionField} (hb : b ≠ 0) (m n : ℤ) (h_a : C.ordAtInfty a = ↑m) (h_b : C.ordAtInfty b = ↑n) : C.ordAtInfty (a / b) = ↑(m - n)`
- **What**: Gives a closed-form ord for a quotient `a/b` in the function field: `ord(a/b) = m − n`, given that `ord(a) = m` and `ord(b) = n` are integer-valued.
- **How**: Direct delegation to `Infinity.lean`'s `C.ordAtInfty_div_of_ord_eq` (one-liner).
- **Hypotheses**: `b ≠ 0`; `a` and `b` have integer-valued ords at infinity.
- **Uses from project**: `HasseWeil.Curves.Infinity.ordAtInfty_div_of_ord_eq`
- **Used by**: unused in file; heavily used by `FormalIsogenySeries.lean` and `AdditionPullback/SilvermanIV14.lean`, `AdditionPullback/Frobenius.lean`
- **Visibility**: public
- **Lines**: 91–95, proof length 1 line (term-mode)
- **Notes**: Pure thin wrapper over `ordAtInfty_div_of_ord_eq`.

---

### `theorem ord_pow_concrete`

- **Type**: `{a : C.FunctionField} (hf : a ≠ 0) (m : ℤ) (k : ℕ) (h_a : C.ordAtInfty a = ↑m) : C.ordAtInfty (a ^ k) = ↑((k : ℤ) * m)`
- **What**: Gives a closed-form ord for a power `a^k`: `ord(a^k) = k · m`, given `ord(a) = m` is integer-valued.
- **How**: Direct delegation to `Infinity.lean`'s `C.ordAtInfty_pow_of_ord_eq` (one-liner).
- **Hypotheses**: `a ≠ 0`; `a` has integer-valued ord at infinity.
- **Uses from project**: `HasseWeil.Curves.Infinity.ordAtInfty_pow_of_ord_eq`
- **Used by**: unused in file; heavily used by `FormalIsogenySeries.lean` and `AdditionPullback/Frobenius.lean`
- **Visibility**: public
- **Lines**: 98–101, proof length 1 line (term-mode)
- **Notes**: Pure thin wrapper over `ordAtInfty_pow_of_ord_eq`.

---

### `theorem ord_add_lt_concrete`

- **Type**: `{a b : C.FunctionField} (m n : ℤ) (hmn : m < n) (h_a : C.ordAtInfty a = ↑m) (h_b : C.ordAtInfty b = ↑n) : C.ordAtInfty (a + b) = ↑m`
- **What**: Non-archimedean "minimum wins" for ord at infinity: when `ord(a) = m < n = ord(b)`, then `ord(a + b) = m`.
- **How**: Lifts the integer inequality to `WithTop ℤ` via `exact_mod_cast`, then applies `C.ordAtInfty_add_eq_of_lt` (from `Infinity.lean`) and chains with `h_a`.
- **Hypotheses**: `m < n` (strict inequality on integer-valued ords).
- **Uses from project**: `HasseWeil.Curves.Infinity.ordAtInfty_add_eq_of_lt`
- **Used by**: `ord_add_le_concrete_of_lt` (within this file); also used externally by `AdditionPullback/Frobenius.lean`
- **Visibility**: public
- **Lines**: 105–111, proof length 4 lines
- **Notes**: None.

---

### `theorem ord_sub_lt_concrete`

- **Type**: `{a b : C.FunctionField} (m n : ℤ) (hmn : m < n) (h_a : C.ordAtInfty a = ↑m) (h_b : C.ordAtInfty b = ↑n) : C.ordAtInfty (a - b) = ↑m`
- **What**: Non-archimedean "minimum wins" for subtraction: when `ord(a) = m < n = ord(b)`, then `ord(a − b) = m`.
- **How**: Same pattern as `ord_add_lt_concrete` via `C.ordAtInfty_sub_eq_of_lt` (from `Infinity.lean`).
- **Hypotheses**: `m < n`.
- **Uses from project**: `HasseWeil.Curves.Infinity.ordAtInfty_sub_eq_of_lt`
- **Used by**: unused in file; used externally by `AdditionPullback/Frobenius.lean`
- **Visibility**: public
- **Lines**: 114–120, proof length 4 lines
- **Notes**: None.

---

### `theorem ord_add_le_concrete_of_lt`

- **Type**: `{a b : C.FunctionField} (m n : ℤ) (hmn : m < n) (h_a : C.ordAtInfty a = ↑m) (h_b : C.ordAtInfty b = ↑n) : C.ordAtInfty (a + b) ≤ ↑m`
- **What**: Upper bound for `ord(a + b)` when `ord(a) = m < n = ord(b)`: the ord is at most `m` (deduced from the equality `ord(a+b) = m`).
- **How**: Calls `C.ord_add_lt_concrete m n hmn h_a h_b` (within this file) and takes `.le`.
- **Hypotheses**: `m < n`.
- **Uses from project**: `ord_add_lt_concrete` (within this file)
- **Used by**: unused in file; no external callers found by grep
- **Visibility**: public
- **Lines**: 124–128, proof length 2 lines
- **Notes**: Convenience corollary of `ord_add_lt_concrete`; no external callers found — potential dead code.

---

## Summary statistics

| Kind | Count |
|------|-------|
| theorem | 6 |
| def / noncomputable def | 0 |
| instance | 0 |
| **Total** | **6** |

- **Sorries**: none
- **`set_option maxHeartbeats`**: none
- **Long proofs (>30 lines)**: none
- **Unused in file** (no callers within this file): `coe_add_coe`, `coe_neg_coe`, `ord_div_concrete`, `ord_pow_concrete`, `ord_sub_lt_concrete`; `ord_add_le_concrete_of_lt` uses only `ord_add_lt_concrete` internally
- **Key API** (used by 3+ decls in this file): none
- **Key project API** (used by many external files): `ord_div_concrete`, `ord_pow_concrete`, `ord_add_lt_concrete`, `ord_sub_lt_concrete`

## Notable observations

This file is a pure "lemma façade": all six declarations are thin wrappers or corollaries of
lemmas already in `HasseWeil/Curves/Infinity.lean`. The module header explicitly documents
sharp `WithTop ℤ` rewrite pitfalls encountered during Frobenius pullback ord computations.
`coe_neg_coe` and `ord_add_le_concrete_of_lt` have no callers found anywhere in the project
(beyond this file itself), making them minor dead-code candidates. The module is heavily used
by `AdditionPullback/Frobenius.lean` and `FormalIsogenySeries.lean`.
