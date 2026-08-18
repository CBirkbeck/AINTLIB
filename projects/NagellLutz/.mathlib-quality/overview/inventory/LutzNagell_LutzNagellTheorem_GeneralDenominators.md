# Inventory: LutzNagell/LutzNagellTheorem/GeneralDenominators.lean

File namespace: `LutzNagell.LutzNagellTheorem`, `variable (W : WeierstrassCurve ℤ)`, `open WeierstrassCurve`.

---

### lemma not_dvd_sum_of_not_dvd_cube
- Type: `{p α : ℤ} (hp : Prime p) (hpa : ¬ p ∣ α) (c₂ c₄ c₆ : ℤ) : ¬ p ∣ (α ^ 3 + c₂ * α ^ 2 * p + c₄ * α * p ^ 2 + c₆ * p ^ 3)`
- What: For a prime `p` not dividing `α`, the integer `α³ + c₂α²p + c₄αp² + c₆p³` is not divisible by `p`.
- How: Assume `p` divides the whole sum; the tail (all terms after `α³`) is visibly divisible by `p` (witness factored out), so `p ∣ α³` by subtraction; then `p ∣ α` via `Prime.dvd_of_dvd_pow`, contradicting `hpa`. Argument: prime divisibility of a cube descends to the base.
- Hypotheses: `p` is prime; `p ∤ α`; `c₂, c₄, c₆` arbitrary integers.
- Uses from project: []
- Used by: `den_ne_prime_of_on_general_curve`
- Visibility: private
- Lines: 33–43 (proof ~10 lines)
- Notes: none

---

### theorem den_ne_prime_of_on_general_curve
- Type: `{x y : ℚ} (heq : y ^ 2 + (W.a₁ : ℚ) * x * y + (W.a₃ : ℚ) * y = x ^ 3 + (W.a₂ : ℚ) * x ^ 2 + (W.a₄ : ℚ) * x + (W.a₆ : ℚ)) {p : ℕ} (hp : p.Prime) (hden : x.den = p) : False` (abbreviated)
- What: If `(x, y)` is a rational point on the general integral Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` and the denominator of `x` equals a prime `p`, then a contradiction follows (so `x` cannot have prime denominator on such a curve).
- How: Write `x = α/p`, `y = γ/δ` in lowest terms. Clear denominators (multiply by `p³·δ²`) over ℚ via `field_simp`/`linarith`, then lift to ℤ with `exact_mod_cast`. A three-fold `p`-adic descent: (Step 2) `p` divides the LHS so `p ∣ δ²·(α³+…)`; since `p ∤ (α³+…)` by `not_dvd_sum_of_not_dvd_cube`, `Prime.dvd_or_dvd` then `Prime.dvd_of_dvd_pow` give `p ∣ δ`; (Step 3) write `δ = pδ₁`, cancel `p²` via `mul_left_cancel₀`, repeat to get `p ∣ δ₁`; (Step 4) write `δ₁ = pδ₂`, cancel `p`, isolate `γ²` to get `p ∣ γ² ` hence `p ∣ γ`. (Step 5) `p ∣ γ` and `p ∣ δ` force `p ∣ gcd(|γ|, δ) = 1` (via `y.reduced`, `Nat.dvd_gcd`), contradicting `p > 1`.
- Hypotheses: `x, y` rational; `(x,y)` satisfies the Weierstrass equation over ℚ with integer coefficients `W.aᵢ`; `p` a natural prime; `x.den = p`.
- Uses from project: [`not_dvd_sum_of_not_dvd_cube`]
- Used by: unused in file
- Visibility: public
- Lines: 57–154 (proof ~94 lines)
- Notes: OVER-50 (needs /decompose-proof pass) — proof body ≈94 lines with explicit Steps 1–5. No `sorry`/`set_option`/TODO. Relies on mathlib: `Rat.num_div_den`, `Rat.reduced`, `Nat.prime_iff_prime_int`, `Prime.dvd_or_dvd`, `Prime.dvd_of_dvd_pow`, `mul_left_cancel₀`, `Nat.dvd_gcd`, `Int.natAbs_dvd_natAbs`.

---

## File Summary

- Total decls: 2 (defs: 0 / lemmas+theorems: 2 / instances: 0)
- Key API (used by ≥3 in-file): none (file has only 2 decls; `not_dvd_sum_of_not_dvd_cube` used once internally)
- Unused decls (within file): `den_ne_prime_of_on_general_curve` (the main exported result; consumed by other files)
- Decls with `sorry`: none
- Decls with `set_option`: none
- Proofs >50 lines: 1 — `den_ne_prime_of_on_general_curve` (~94 lines) [OVER-50]
- Proofs 30–50 lines: 0
