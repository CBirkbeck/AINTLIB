# Inventory: ./HasseWeil/WeilPairing/Discriminant.lean

**File summary:** Pure arithmetic leaf file — no elliptic-curve or function-field content. Provides two forms of the discriminant lemma (Silverman V.1.1) used to lift the quadratic-form non-negativity from a `p`-coprime sublattice to all integers, completing the Hasse bound arithmetic. Imported by `Assembly.lean`.

---

## Declarations

### `theorem exists_int_balanced`

- **Type**: `{q : ℤ} → 0 < q → (a : ℤ) → ∃ r : ℤ, |a - 2 * q * r| ≤ q`
- **What**: For any positive integer `q` and any integer `a`, there exists `r` such that the remainder `|a − 2qr|` is at most `q` (nearest-even / balanced-remainder approximation of `a/(2q)`).
- **How**: Takes `r = (a + q) / (2q)` (integer division). Uses `Int.emod_add_mul_ediv` (the division algorithm identity `a = 2q·(a/2q) + a%2q`) plus `Int.emod_nonneg` and `Int.emod_lt_of_pos` to bound the remainder, finishing with `linarith`.
- **Hypotheses**: `q > 0` (as an integer).
- **Uses from project**: none.
- **Used by**: `qf_nonneg_of_nonneg_on_coprime` (Step 1 balanced-remainder argument).
- **Visibility**: public
- **Lines**: 27–35 (proof ~9 lines)
- **Notes**: Clean, self-contained. No `set_option`, no sorry.

---

### `theorem qf_nonneg_of_nonneg_on_coprime`

- **Type**: `{q t : ℤ} → 0 < q → {p : ℕ} → p.Prime → (∀ r s : ℤ, ¬ (p : ℤ) ∣ s → 0 ≤ q * r^2 − t * r * s + s^2) → ∀ r s : ℤ, 0 ≤ q * r^2 − t * r * s + s^2`
- **What**: The discriminant lemma (Silverman V.1.1, weaker hypothesis form): if `Q(r,s) = q·r² − t·rs + s²` is non-negative on all `(r,s)` with `p ∤ s`, then it is non-negative everywhere. Equivalently, the quadratic form is positive semi-definite.
- **How**: Two steps. **Step 1** proves `t² ≤ 4q` by contradiction: assume `t² > 4q`, choose a prime `ℓ ≠ p` via `Nat.exists_infinite_primes`, take `s = ℓⁿ` large enough (`pow_unbounded_of_one_lt`) so `s > q`, apply the balanced remainder `exists_int_balanced` to find `r` with `|2qr − ts| ≤ q`, then use `nlinarith` with the ring identity `4qQ = (2qr−ts)² + (4q−t²)s²` to get `Q < 0`, contradicting the hypothesis. **Step 2** deduces positive semi-definiteness directly: `4qQ = (2qr−ts)² + (4q−t²)s² ≥ 0` (both terms non-negative since `4q ≥ t²`), via `nlinarith`.
- **Hypotheses**: `q > 0`, `p` prime, `Q ≥ 0` on `{(r,s) : p ∤ s}`.
- **Uses from project**: `exists_int_balanced` (balanced-remainder witness in Step 1).
- **Used by**: `Assembly.lean` (called as `qf_nonneg_of_nonneg_on_coprime hq hp`).
- **Visibility**: public
- **Lines**: 43–78 (proof ~36 lines)
- **Notes**: Proof is 36 lines (>30). Uses `Nat.exists_infinite_primes` and `pow_unbounded_of_one_lt` from Mathlib. The ring identity is checked by `ring` inside `nlinarith`. `set_option` absent; no sorry.

---

### `theorem qf_nonneg_of_nonneg_on_coprime_both`

- **Type**: `{q t : ℤ} → 0 < q → {p : ℕ} → p.Prime → (∀ r s : ℤ, ¬ (p : ℤ) ∣ r → ¬ (p : ℤ) ∣ s → 0 ≤ q * r^2 − t * r * s + s^2) → ∀ r s : ℤ, 0 ≤ q * r^2 − t * r * s + s^2`
- **What**: The discriminant lemma with a **weaker** hypothesis (reviewer round-23, Route B): non-negativity only on the smaller set `{p ∤ r AND p ∤ s}` (both coordinates coprime to `p`) still forces `Q ≥ 0` everywhere. This is needed because the Weil-pairing pencil scaling requires both `p ∤ r'` and `p ∤ s'`.
- **How**: **Step 1** proves `t² ≤ 4q` via the reviewer's explicit prime-to-`p` negative witness: set `C = q − t + 1`, `m = p·(|C| + 1)`, `r = mt + 1`, `s = 2mq + 1`. Since `p ∣ m`, both `r ≡ 1` and `s ≡ 1` mod `p`, so neither is divisible by `p` (verified by `dvd_sub` + `Int.isUnit_iff`). The ring identity `Q(mt+1, 2mq+1) = (4q − t²)(qm² + m) + (q−t+1)` (checked by `ring`) then gives `Q < 0` because `|4q−t²| ≥ 1` and `qm²+m ≥ |C|+1 > C` (via `nlinarith`), contradiction. **Step 2** is identical to `qf_nonneg_of_nonneg_on_coprime`: positive semi-definiteness by `nlinarith`.
- **Hypotheses**: `q > 0`, `p` prime, `Q ≥ 0` on `{(r,s) : p ∤ r AND p ∤ s}`.
- **Uses from project**: none (does NOT use `exists_int_balanced`; the explicit witness replaces the balanced-remainder argument).
- **Used by**: `Assembly.lean` (called as `qf_nonneg_of_nonneg_on_coprime_both hq hp`).
- **Visibility**: public
- **Lines**: 95–142 (proof ~48 lines)
- **Notes**: Proof is 48 lines (>30). No `set_option`, no sorry. Strictly stronger version of the previous theorem — weakened hypothesis, same conclusion. The witness construction avoids Mathlib's `Nat.exists_infinite_primes` and `pow_unbounded_of_one_lt`, relying only on `nlinarith`, `ring`, `dvd_sub`, and `Int.isUnit_iff`.

---

## Summary statistics

| Kind | Count |
|------|-------|
| theorem | 3 |
| def/noncomputable def | 0 |
| instance | 0 |
| **Total** | **3** |

## Cross-file usage

All three declarations are used in `HasseWeil/WeilPairing/Assembly.lean`:
- `qf_nonneg_of_nonneg_on_coprime`: applied directly at line 42.
- `qf_nonneg_of_nonneg_on_coprime_both`: applied directly at line 63.
- `exists_int_balanced`: used only within `qf_nonneg_of_nonneg_on_coprime` inside this file; not referenced in Assembly.lean directly.

## Key API

- `qf_nonneg_of_nonneg_on_coprime` — the primary discriminant lemma (used by Assembly.lean).
- `qf_nonneg_of_nonneg_on_coprime_both` — the Route-B strengthening (also used by Assembly.lean).

## Notes

This is a pure arithmetic leaf file: no imports from the HasseWeil project, no elliptic curve content. The only project import is `Mathlib.Tactic` and `Mathlib.Data.Nat.Prime.Infinite`. Both long proofs follow the two-step discriminant pattern (force `t²≤4q`, then PSD). The two theorems are parallel but independent; the second (Route B) weakens the hypothesis and uses a self-contained explicit witness rather than the balanced-remainder helper.
