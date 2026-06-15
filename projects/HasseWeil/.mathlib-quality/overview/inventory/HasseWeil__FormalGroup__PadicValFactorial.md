# Inventory: ./HasseWeil/FormalGroup/PadicValFactorial.lean

**File**: `HasseWeil/FormalGroup/PadicValFactorial.lean`
**Lines**: 1–88
**Namespace**: `HasseWeil.FormalGroup`
**Imports**: `Mathlib.NumberTheory.Padics.PadicVal.Basic`, `Mathlib.Data.Real.Basic`, `Mathlib.Tactic.Positivity`

**Purpose**: Packages Mathlib's Legendre formula into the real-valued bound `v_p(n!) ≤ (n−1)/(p−1)` needed for formal-logarithm convergence arguments (Silverman IV.6.2).

---

## Declarations

### `theorem padicValNat_factorial_le`

- **Type**: `(p : ℕ) [hp : Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) : (padicValNat p n.factorial : ℝ) ≤ (n - 1 : ℝ) / (p - 1)`
- **What**: For a prime `p` and `n ≥ 1`, the `p`-adic valuation of `n!` satisfies `v_p(n!) ≤ (n−1)/(p−1)` as real numbers.
- **How**: Uses Mathlib's `sub_one_mul_padicValNat_factorial_lt_of_ne_zero` (the strict inequality `(p−1)·v_p(n!) < n` in `ℕ`) to derive `(p−1)·v_p(n!) ≤ n−1` by `omega`, then casts to `ℝ` via `Nat.cast_le` and `Nat.cast_sub`, and divides by `(p−1) > 0` using `le_div_iff₀`.
- **Hypotheses**: `p` is prime (via `Fact p.Prime`); `n ≥ 1`.
- **Uses from project**: none
- **Used by**: `padicValNat_factorial_div_le` (line 82, in this file)
- **Visibility**: public
- **Lines**: 45–70, proof ~24 lines
- **Notes**: No `sorry`. No `set_option maxHeartbeats`. Proof is under 30 lines. The bound is slightly weaker than Legendre's exact formula but sufficient for the application; the docstring correctly identifies the exact Mathlib lemma used.

---

### `theorem padicValNat_factorial_div_le`

- **Type**: `(p : ℕ) [hp : Fact p.Prime] (n : ℕ) : (padicValNat p n.factorial : ℝ) ≤ (n : ℝ) / (p - 1)`
- **What**: For any `n : ℕ` (including `n = 0`), `v_p(n!) ≤ n/(p−1)` as real numbers; this is a slightly looser bound that does not require `n ≥ 1`.
- **How**: Cases on `n = 0` (where `padicValNat p 0! = 0` and `simp` closes the goal) and `n ≥ 1` (where it applies `padicValNat_factorial_le` and uses monotonicity of division `div_le_div_of_nonneg_right` to weaken `(n−1)/(p−1) ≤ n/(p−1)`).
- **Hypotheses**: `p` is prime (via `Fact p.Prime`); `n` arbitrary.
- **Uses from project**: `padicValNat_factorial_le` (line 82)
- **Used by**: unused in file (dead-code candidate; likely intended for use by formal-logarithm convergence lemmas in other files)
- **Visibility**: public
- **Lines**: 73–86, proof ~13 lines
- **Notes**: No `sorry`. No `set_option maxHeartbeats`. Proof is under 30 lines. Both theorems are currently not referenced by any other file in the project (confirmed by grep), making them dead code at the project level — they are presumably prepared for future formal-group/logarithm work.

---

## Summary

| Metric | Value |
|--------|-------|
| Total declarations | 2 |
| Theorems/lemmas | 2 |
| Definitions | 0 |
| Instances | 0 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |
| Proofs > 30 lines | 0 |
| Unused in file | `padicValNat_factorial_div_le` (not called within this file; `padicValNat_factorial_le` is called by it) |
| Key API (used by 3+) | none |

**Notes**: This is a small, self-contained utility file with no project-internal dependencies. Both declarations are also not referenced by any other project file, so the entire file is effectively dead code at the project level. The results closely mirror (and are weaker than) Mathlib's `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`; a mathlib duplication concern is low since the file explicitly repackages the result in ℝ for a specific downstream use.
