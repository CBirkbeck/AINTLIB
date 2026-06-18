# Inventory: ./HasseWeil/WeilPairing/IntegerSeparation.lean

**File**: `HasseWeil/WeilPairing/IntegerSeparation.lean`  
**Module**: `HasseWeil.WeilPairing`  
**Purpose**: Step 7 of the Route-2 Weil-pairing proof of the Hasse bound — pure arithmetic integer-separation from per-ℓ congruences (Silverman V.2.3.1).  
**Imports**: `Mathlib.Data.ZMod.Basic`, `Mathlib.Data.Nat.Prime.Infinite`  
**Total declarations**: 2 (both theorems, no defs, no instances)

---

## Declaration inventory

---

### `theorem int_eq_zero_of_dvd_all_primes_ne`

- **Type**: `{D : ℤ} → {p : ℕ} → (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (ℓ : ℤ) ∣ D) → D = 0`
- **What**: An integer `D` that is divisible (as an integer) by every prime `ℓ` distinct from a fixed prime `p` must be zero.
- **How**: By contradiction: assume `D ≠ 0`. Use `Nat.exists_infinite_primes` to find a prime `ℓ ≥ max(|D|+1, p+1)`, which is automatically `≠ p` and satisfies `ℓ ∣ D` by hypothesis. Then `Nat.le_of_dvd` gives `ℓ ≤ |D|`, contradicting `ℓ > |D|`. The divisibility transfer from `ℤ` to `ℕ` uses `Int.natAbs_dvd_natAbs`.
- **Hypotheses**: `h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (ℓ : ℤ) ∣ D`
- **Uses from project**: none
- **Used by**: `int_eq_of_congr_all_primes_ne` (within this file); `int_eq_of_congr_all_primes_ne` is used in `Reduction.lean`
- **Visibility**: public
- **Lines**: 32–46; proof length ≈ 14 lines
- **Notes**: Clean, elementary. Uses `Nat.exists_infinite_primes` (Mathlib), `Int.natAbs_dvd_natAbs`, `Nat.le_of_dvd`, `Int.natAbs_pos`. No sorry, no maxHeartbeats override.

---

### `theorem int_eq_of_congr_all_primes_ne`

- **Type**: `{A B : ℤ} → {p : ℕ} → (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (A : ZMod ℓ) = (B : ZMod ℓ)) → A = B`
- **What**: If `A ≡ B (mod ℓ)` in `ZMod ℓ` for every prime `ℓ ≠ p`, then `A = B` as integers. This is the key endgame lemma: with `A = deg(rπ − s)` and `B = qr² − trs + s²`, the per-ℓ Weil-pairing determinant congruence yields the integer identity closing Leaf 1.
- **How**: Reduces to `int_eq_zero_of_dvd_all_primes_ne` applied to `A − B`. Converts `ZMod ℓ`-equality to divisibility via `ZMod.intCast_zmod_eq_zero_iff_dvd` (after casting `A − B` to `ZMod ℓ` and rewriting). Uses `haveI : NeZero ℓ` from `hℓ.ne_zero` to enable the `ZMod ℓ` cast lemma. Concludes `A = B` from `A - B = 0` by `omega`.
- **Hypotheses**: `h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (A : ZMod ℓ) = (B : ZMod ℓ)`
- **Uses from project**: `int_eq_zero_of_dvd_all_primes_ne` (this file)
- **Used by**: unused within this file; called by `Reduction.lean` (twice, at lines 57 and 108)
- **Visibility**: public
- **Lines**: 53–62; proof length ≈ 9 lines
- **Notes**: Clean, no sorry, no maxHeartbeats override. Uses `ZMod.intCast_zmod_eq_zero_iff_dvd` from Mathlib.

---

## Summary

| Declaration | Kind | Lines | Proof length | Sorry | maxHeartbeats |
|---|---|---|---|---|---|
| `int_eq_zero_of_dvd_all_primes_ne` | theorem | 32–46 | 14 | no | none |
| `int_eq_of_congr_all_primes_ne` | theorem | 53–62 | 9 | no | none |

**Key API**: `int_eq_zero_of_dvd_all_primes_ne` (used by `int_eq_of_congr_all_primes_ne` within this file; `int_eq_of_congr_all_primes_ne` is the external API consumed by `Reduction.lean`).

**Unused within file**: `int_eq_of_congr_all_primes_ne` has no callers within this file (it is the terminal export).

**Notable**: Entirely self-contained arithmetic file (only imports `ZMod.Basic` and `Nat.Prime.Infinite`). No elliptic-curve content. No sorries, no long proofs, no maxHeartbeats overrides. Both declarations are axiom-clean. This is a pure isolation lemma separating the arithmetic endgame from all curve geometry.
