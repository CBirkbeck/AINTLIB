# Inventory: LutzNagell/LutzNagellTheorem/GeneralMain.lean

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralMain.lean`

Namespace: `LutzNagell.LutzNagellTheorem`; `open WeierstrassCurve`; section variable `(W : WeierstrassCurve ℤ)`.

---

### lemma nsmul_eq_zero_affine_to_jac
- Type: `{x y : ℚ} {hns : (curveQ W).toAffine.Nonsingular x y} {n : ℕ} (h : n • (Affine.Point.some _ _ hns) = 0) : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0`
- What: Transfers the vanishing of a natural-number multiple `n • P = 0` of an affine point `P` on the rational curve `curveQ W` into the vanishing of the integer multiple `(n : ℤ) • (·)` of the corresponding Jacobian point obtained via `fromAffine`.
- How: Rewrites `(n : ℤ) • ·` as the `natCast` of the ℕ-scalar action (`natCast_zsmul`), then pushes the hypothesis through the inverse of the additive group isomorphism `Jacobian.Point.toAffineAddEquiv (curveQ W)` using `congrArg` and `map_nsmul`/`map_zero`.
- Hypotheses: `x, y` rational; `(x, y)` a nonsingular point of the affine model of `curveQ W`; `n` a natural number with `n • P = 0` in the affine point group.
- Uses from project: [`curveQ`]
- Used by: `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, `lutz_nagell_integrality_general`, `lutz_nagell_integrality_short`
- Visibility: public
- Lines: 28–35 (proof 4 lines)
- Notes: none

---

### lemma exists_some_of_ne_zero
- Type: `{Q : Affine.Point ((curveQ W).toAffine)} (hQ : Q ≠ 0) : ∃ x y, ∃ hns : (curveQ W).toAffine.Nonsingular x y, Q = .some _ _ hns`
- What: Every nonzero point `Q` of the affine point group of `curveQ W` is an affine point `.some x y hns`, i.e. exhibits explicit coordinates and a nonsingularity proof.
- How: Case split on the `Affine.Point` constructor (`rcases`); the zero/`0` constructor contradicts `hQ` via `absurd rfl hQ`, and the `.some` constructor supplies the witnesses directly.
- Hypotheses: `Q` is a point of the affine model of `curveQ W` and `Q ≠ 0` (not the point at infinity).
- Uses from project: [`curveQ`]
- Used by: `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`
- Visibility: public
- Lines: 40–45 (proof 3 lines)
- Notes: none

---

### lemma integrality_of_odd_prime_factor
- Type: `{x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hpm : p ∣ addOrderOf (Affine.Point.some _ _ hpt)) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`
- What: If a nonzero finite-order affine point `P` on `curveQ W` has an odd prime `p` dividing its order, then its coordinates `x, y` are integers.
- How: Sets `k = addOrderOf P / p`, so `Q := k • P` is a nonzero point of exact order `p` (vanishing of `Q` is ruled out by an order-minimality `calc`/`Nat.le_of_dvd`+`addOrderOf_dvd_of_nsmul_eq_zero` argument, and `p • Q = 0` via `mul_nsmul`+`addOrderOf_nsmul_eq_zero`); writes `Q = .some hns'` via `exists_some_of_ne_zero`, applies the prime-order integrality result `prime_order_integrality_general` to the Jacobian image of `Q` to get integrality of `Q`'s coordinates, then descends to `P` via `integral_of_nsmul_integral_general` (integrality of `k • P` forces integrality of `P`). Hinges on `prime_order_integrality_general` and `integral_of_nsmul_integral_general`.
- Hypotheses: `(x, y)` nonsingular on `curveQ W`; `p` prime, `p ≠ 2`, `p` divides the additive order of `P`; `P` is of finite additive order.
- Uses from project: [`curveQ`, `exists_some_of_ne_zero`, `prime_order_integrality_general`, `nsmul_eq_zero_affine_to_jac`, `integral_of_nsmul_integral_general`]
- Used by: `lutz_nagell_integrality_general`
- Visibility: private
- Lines: 47–77 (proof 30 lines)
- Notes: long(30-50)

---

### lemma integrality_of_four_dvd_order
- Type: `{x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) (h4 : 4 ∣ addOrderOf (Affine.Point.some _ _ hpt)) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`
- What: If a nonzero finite-order affine point `P` on `curveQ W` has order divisible by 4, then its coordinates `x, y` are integers.
- How: Sets `k = addOrderOf P / 4`, so `Q := k • P` satisfies `4 • Q = 0` while `2 • Q ≠ 0` (i.e. `Q` has exact order 4); the non-vanishing facts come from `addOrderOf_dvd_of_nsmul_eq_zero`+`Nat.le_of_dvd` discharged by `omega`, and `4 • Q = 0` from `mul_nsmul`+`addOrderOf_nsmul_eq_zero`. Writes `Q = .some hns'`, applies `integrality_of_order_four_general` to get integrality of `Q`'s coordinates, then descends to `P` via `integral_of_nsmul_integral_general`. Hinges on `integrality_of_order_four_general` and `integral_of_nsmul_integral_general`.
- Hypotheses: `(x, y)` nonsingular on `curveQ W`; `4` divides the additive order of `P`; `P` is of finite additive order.
- Uses from project: [`curveQ`, `exists_some_of_ne_zero`, `integrality_of_order_four_general`, `nsmul_eq_zero_affine_to_jac`, `integral_of_nsmul_integral_general`]
- Used by: `lutz_nagell_integrality_general`
- Visibility: private
- Lines: 79–105 (proof 26 lines)
- Notes: none

---

### theorem lutz_nagell_integrality_general
- Type: `{x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : ((∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y) ∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧ (∃ n : ℤ, (n : ℚ) = 4 * x) ∧ ∃ m : ℤ, (m : ℚ) = 8 * y)`
- What: The generalized Lutz–Nagell integrality theorem: a nonzero finite-order point on a general Weierstrass curve over ℚ with integral coefficients either has integral coordinates, or has order exactly 2 with `4x, 8y ∈ ℤ`.
- How: Case split on whether `addOrderOf P = 2`. If yes, takes the right disjunct and applies `bounded_den_of_order_two_general` to the Jacobian image of `2 • P = 0`. If no, takes the left disjunct and case-splits on whether the order has an odd prime factor: if so, applies `integrality_of_odd_prime_factor`; if not (`push_neg`), every prime factor is 2, so via `Nat.exists_prime_and_dvd` (twice) the order is divisible by 4 (`omega`/`linarith` arithmetic), and `integrality_of_four_dvd_order` finishes. Hinges on `bounded_den_of_order_two_general`, `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, and `Nat.exists_prime_and_dvd`.
- Hypotheses: `(x, y)` nonsingular on `curveQ W` (integral-coefficient Weierstrass curve viewed over ℚ); `P = .some x y hpt` is of finite additive order (and is automatically nonzero).
- Uses from project: [`curveQ`, `nsmul_eq_zero_affine_to_jac`, `bounded_den_of_order_two_general`, `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`]
- Used by: `lutz_nagell_integrality_short`
- Visibility: public
- Lines: 107–142 (proof 27 lines)
- Notes: none

---

### theorem lutz_nagell_integrality_short
- Type: `(A B : ℤ) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`
- What: Short Weierstrass Lutz–Nagell integrality: a nonzero finite-order point on `y² = x³ + Ax + B` (`A, B ∈ ℤ`) has integral coordinates — the order-2 branch of the general theorem collapses to full integrality.
- How: Applies `lutz_nagell_integrality_general` to `shortCurveZ A B`; the integral disjunct is returned directly. In the order-2 disjunct, uses `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` with the 2-division polynomial `ψ₂` (which for a short curve, via `curveQ_a₁`/`curveQ_a₃`/`shortCurveZ_a₁`/`shortCurveZ_a₃`, equals `2y`) to force `y = 0` (`linarith`); then with `shortCurveQ_equation_iff` reduces the curve equation to `x` being a root of the monic `X³ + AX + B ∈ ℤ[X]`, and `isInteger_of_is_root_of_monic` (a rational root of a monic integer polynomial is integral) gives `x ∈ ℤ`. Monicity is established via `Monic.add_of_left`/`monic_X_pow`/`degree_C_mul_X_le`/`degree_C_le`. Hinges on `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `shortCurveQ_equation_iff`, and `isInteger_of_is_root_of_monic`.
- Hypotheses: integers `A, B`; `(x, y)` nonsingular on the short curve `shortCurveQ A B`; the point `.some x y hpt` is of finite additive order.
- Uses from project: [`shortCurveQ`, `lutz_nagell_integrality_general`, `shortCurveZ`, `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `nsmul_eq_zero_affine_to_jac`, `curveQ_a₁`, `curveQ_a₃`, `shortCurveZ_a₁`, `shortCurveZ_a₃`, `shortCurveQ_equation_iff`]
- Used by: unused in file
- Visibility: public
- Lines: 153–187 (proof 32 lines)
- Notes: long(30-50); uses `open Polynomial in` (twice, scoped to the `hroot`/`hmonic` `have`s)

---

## File Summary

- Total decls: 6 — defs 0 / lemmas+theorems 6 (4 lemmas + 2 theorems) / instances 0. (No structures/classes/abbrevs/inductives.)
- Key API (used by ≥3 in-file): `nsmul_eq_zero_affine_to_jac` (used by 4). `exists_some_of_ne_zero` (used by 2). No other decl reaches the ≥3 threshold.
- Unused decls (within this file): `lutz_nagell_integrality_short` (terminal export; no in-file consumer).
- Decls with `sorry`: none.
- Decls with `set_option`: none.
- Proofs >50 lines (OVER-50): none (count 0).
- Proofs 30–50 lines: `integrality_of_odd_prime_factor` (30) and `lutz_nagell_integrality_short` (32) — count 2.
- Other notes: `lutz_nagell_integrality_short` uses `open Polynomial in` locally (twice); no global `open Polynomial`. All decls public except `integrality_of_odd_prime_factor` and `integrality_of_four_dvd_order`, which are `private`. Heavy cross-file dependence on `GeneralPrimeOrder` (`prime_order_integrality_general`, `integrality_of_order_four_general`, `bounded_den_of_order_two_general`), `GeneralIntegralMultiple` (`integral_of_nsmul_integral_general`), `GeneralCurve` (`curveQ`/`shortCurveZ`/`shortCurveQ` family, `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`), and `ShortWeierstrass` (`shortCurveZ_a₁`/`shortCurveZ_a₃`, `shortCurveQ_equation_iff`).
