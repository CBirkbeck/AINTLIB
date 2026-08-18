# Inventory: PadicLFunctions/KubotaLeopoldt/ZetaValues.lean

File path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/ZetaValues.lean`

Imports: `Mathlib.NumberTheory.Bernoulli`

Module purpose: defines the rational zeta values `ζ(−k)` used throughout RJW (arXiv:2309.15692) §4, kept as rational numbers (cast into `ℚ_p` later) so the main p-adic chain need not import complex analysis. The bridge to `riemannZeta` lives separately in `ZetaValuesComplex.lean`.

---

### def zetaNeg
- Type: `zetaNeg (k : ℕ) : ℚ := (-1) ^ k * bernoulli (k + 1) / (k + 1)`
- What: The rational number `ζ(−k) = (−1)^k · B_{k+1}/(k+1)`, the value of the Riemann zeta function at the non-positive integer `−k`, expressed via mathlib's `bernoulli` convention (`B₁ = −1/2`). (RJW TeX line 1455.)
- How: Direct definition; no proof. It packages the closed form `(−1)^k B_{k+1}/(k+1)` as a rational function of `k`.
- Hypotheses: none beyond `k : ℕ`.
- Uses from project: []
- Used by: `zetaNeg_zero`, `zetaNeg_eq_zero_of_even`, `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`
- Visibility: public
- Lines: 17–18 (def, no proof)
- Notes: none

### lemma zetaNeg_zero
- Type: `zetaNeg 0 = -(1 / 2)`
- What: The base value `ζ(0) = −1/2`.
- How: Unfolds `zetaNeg` and rewrites with `bernoulli_one` (`B₁ = −1/2`), then `norm_num` discharges the arithmetic.
- Hypotheses: none.
- Uses from project: [`zetaNeg`]
- Used by: unused in file
- Visibility: public (`@[simp]`)
- Lines: 20–22 (proof 1 line)
- Notes: none

### lemma zetaNeg_eq_zero_of_even
- Type: `{k : ℕ} (hk : k ≠ 0) (h : Even k) : zetaNeg k = 0`
- What: The trivial zeros of zeta: `ζ(−k) = 0` for even `k ≥ 2`, since the odd-index Bernoulli numbers `B_{k+1}` vanish.
- How: Unfolds `zetaNeg`, then applies `bernoulli_eq_zero_of_odd` to `B_{k+1}` using that `k+1` is odd (`h.add_one`) and `≥ 3` (the `by omega` side goal); `mul_zero`/`zero_div` finish.
- Hypotheses: `k ≠ 0` and `k` even (so `k ≥ 2`, hence `k+1 ≥ 3` is odd).
- Uses from project: [`zetaNeg`]
- Used by: `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`
- Visibility: public
- Lines: 24–26 (proof 1 line)
- Notes: none

### lemma neg_one_pow_mul_one_sub_pow_mul_zetaNeg
- Type: `(q : ℚ) {k : ℕ} (hk : 0 < k) : (-1) ^ k * ((1 - q ^ (k - 1)) * zetaNeg (k - 1)) = (1 - q ^ (k - 1)) * zetaNeg (k - 1)`
- What: Sign-removal step in the Kubota–Leopoldt interpolation (RJW TeX line 1596): for `k > 0` the factor `(−1)^k` may be dropped from `(1 − q^{k−1}) ζ(1−k)`.
- How: Case split on `k`. If `k = 1`, `1 − q⁰ = 0` so both sides vanish (`simp`). Otherwise split on parity: if `k` even, `(−1)^k = 1` via `Even.neg_one_pow`; if `k` odd (and `≥ 3`), then `k−1` is even and nonzero, so `zetaNeg (k−1) = 0` by `zetaNeg_eq_zero_of_even` (with `Nat.Odd.sub_odd ho odd_one`), and `ring` closes both sides at zero.
- Hypotheses: `0 < k` (any `q : ℚ`).
- Uses from project: [`zetaNeg`, `zetaNeg_eq_zero_of_even`]
- Used by: unused in file
- Visibility: public
- Lines: 28–40 (proof ~6 lines)
- Notes: none

---

## File Summary

- Total declarations: 4 — defs 1 (`zetaNeg`) / lemmas+theorems 3 (`zetaNeg_zero`, `zetaNeg_eq_zero_of_even`, `neg_one_pow_mul_one_sub_pow_mul_zetaNeg`) / instances 0.
- Key API (used by ≥3 in file): `zetaNeg` (referenced by all 3 lemmas).
- Unused in file: `zetaNeg_zero`, `neg_one_pow_mul_one_sub_pow_mul_zetaNeg` (these are the file's exported leaves, consumed by the wider §4 chain / `ZetaValuesComplex.lean`).
- Declarations with `sorry`: none.
- `set_option`: none.
- Proofs > 50 lines (OVER-50): none (0).
- Proofs 30–50 lines: none (0).

All proofs are ≤ 6 lines; no decomposition needed.
