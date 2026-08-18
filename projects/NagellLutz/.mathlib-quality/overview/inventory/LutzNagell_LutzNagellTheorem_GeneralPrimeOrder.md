# Inventory: LutzNagell/LutzNagellTheorem/GeneralPrimeOrder.lean

File namespace: `LutzNagell.LutzNagellTheorem`. Fixed `variable (W : WeierstrassCurve ℤ)`.
Imports: `DivisionPolynomialDegree`, `ZSMul`, `GeneralDenominators`, `EvalBridge`, `GeneralCurve`,
mathlib `RationalRoot`, `Localization.Rat`.

---

### theorem y_integral_of_x_integral_on_general_curve
- Type: `(W) {x y : ℚ} (hcurve : y^2 + a₁xy + a₃y = x^3 + a₂x^2 + a₄x + a₆) {x₀ : ℤ} (hx : (x₀:ℚ) = x) : ∃ y₀ : ℤ, (y₀:ℚ) = y`
- What: On a Weierstrass curve with integer coefficients, if a rational point's `x`-coordinate is an integer then its `y`-coordinate is an integer.
- How: Exhibits `y` as a root of the monic integer polynomial `Y² + (a₁x₀+a₃)Y − (x₀³+a₂x₀²+a₄x₀+a₆)`; the root claim is closed by `push_cast`/`nlinarith` from the curve equation, monicity by `Polynomial.Monic.add_of_left` + degree bounds (`degree_C_mul_X_le`, `degree_X_pow`), then mathlib's `isInteger_of_is_root_of_monic` (integrally-closed/rational-root) gives the integer preimage.
- Hypotheses: integer Weierstrass coefficients (via `W : WeierstrassCurve ℤ`); `(x,y)` satisfies the affine equation over ℚ; `x` equals an integer `x₀`.
- Uses from project: []
- Used by: `integrality_of_order_four_general`, `prime_order_integrality_general`
- Visibility: public
- Lines: 30–50 (proof 36–50, ~15 lines)
- Notes: none

### theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero_general
- Type: `(W) {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) (n : ℤ) (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) : ((curveQ W).ψ n).evalEval x y = 0`
- What: If `n • P = 0` in the Jacobian point group of the base-changed curve `curveQ W`, then the `n`-th division polynomial `ψ_n` vanishes at `(x,y)`.
- How: Rewrites the scalar multiple via `zsmul_eq_smulEval`, identifies the zero point with `Jacobian.Point.zero_point`, unfolds point equality (`Jacobian.Point.ext_iff`), and concludes the `Z`-coordinate is zero through `Jacobian.Z_eq_zero_of_equiv` (Jacobian equivalence at infinity).
- Hypotheses: `(x,y)` nonsingular on the affine model of `curveQ W`; `n`-torsion of the corresponding Jacobian point.
- Uses from project: []  (relies on `curveQ`/`zsmul_eq_smulEval` from imported files, but no decl from THIS file)
- Used by: `x_integral_of_odd_prime_torsion_general`, `integrality_of_order_four_general`, `bounded_den_of_order_two_general`
- Visibility: public
- Lines: 55–64 (proof 60–64, ~5 lines)
- Notes: none

### theorem two_nsmul_eq_zero_of_ψ₂_eq_zero
- Type: `(W) {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) (hψ : (curveQ W).ψ₂.evalEval x y = 0) : (2:ℕ) • Affine.Point.some _ _ hns = 0`
- What: Converse 2-torsion criterion: if `ψ₂(x,y)=0` (equivalently `2y+a₁x+a₃=0`) then the affine point is 2-torsion.
- How: Rewrites `ψ₂` to its evaluated `polynomialY` form, derives `y = negY x y` by `linarith`, then applies `WeierstrassCurve.Affine.Point.add_of_Y_eq` (the doubling formula when `Y` equals its negation) after `two_nsmul`.
- Hypotheses: `(x,y)` nonsingular; `ψ₂` vanishes at `(x,y)`.
- Uses from project: []
- Used by: `integrality_of_order_four_general`
- Visibility: public
- Lines: 69–77 (proof 73–77, ~5 lines)
- Notes: none

### theorem x_integral_of_odd_prime_torsion_general
- Type: `(W) {x y : ℚ} (hns : … Nonsingular x y) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (htors : (p:ℤ) • Jacobian.Point.fromAffine (…) = 0) : ∃ x₀ : ℤ, (x₀:ℚ) = x`
- What: For an odd prime `p`, if `p • P = 0` on a general integral Weierstrass curve then the `x`-coordinate of `P` is an integer.
- How: From `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` plus `evalEval_ψ_odd` reduces vanishing of `ψ_p` to `aeval x (preΨ p) = 0`; the rational-root bound `den_dvd_of_is_root` together with `leadingCoeff_preΨ` (= `p`) forces `x.den ∣ p`; primality (`hp.eq_one_or_self_of_dvd`) leaves `x.den = 1`, ruling out `x.den = p` via `den_ne_prime_of_on_general_curve`.
- Hypotheses: `(x,y)` nonsingular; `p` an odd prime; `p`-torsion of the Jacobian point.
- Uses from project: `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `den_ne_prime_of_on_general_curve`, `curveQ_equation_iff`  (+ imported `evalEval_ψ_odd`, `den_dvd_of_is_root`, `leadingCoeff_preΨ`, `map_preΨ`, `isFractionRingDen`)
- Used by: `prime_order_integrality_general`
- Visibility: public
- Lines: 83–112 (proof 89–112, ~24 lines)
- Notes: long(30-50) — proof body ~24 lines, total decl 30 lines; none other

### theorem integrality_of_order_four_general
- Type: `(W) {x y : ℚ} (hns : … Nonsingular x y) (h4 : (4:ℤ) • … = 0) (h2ne : (2:ℕ) • Affine.Point.some _ _ hns ≠ 0) : (∃ x₀:ℤ, (x₀:ℚ)=x) ∧ ∃ y₀:ℤ, (y₀:ℚ)=y`
- What: If `P` has exact order 4 (`4•P=0`, `2•P≠0`) on a general integral curve, then `P` has integral affine coordinates.
- How: From `ψ₄(P)=0` and the factorisation `ψ₄ = C(preΨ₄)·ψ₂` (`WeierstrassCurve.ψ_four`), `mul_eq_zero` splits: the `preΨ₄` branch gives `aeval x preΨ₄ = 0`, so `den_dvd_of_is_root` + `leadingCoeff_preΨ₄` (= 2) forces `x.den ∣ 2` and primality of 2 + `den_ne_prime_of_on_general_curve` gives `x.den=1`, then `y_integral_of_x_integral_on_general_curve` finishes; the `ψ₂` branch yields 2-torsion via `two_nsmul_eq_zero_of_ψ₂_eq_zero`, contradicting `h2ne`.
- Hypotheses: `(x,y)` nonsingular; point is 4-torsion but not 2-torsion.
- Uses from project: `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `curveQ_equation_iff`, `den_ne_prime_of_on_general_curve`, `y_integral_of_x_integral_on_general_curve`, `two_nsmul_eq_zero_of_ψ₂_eq_zero`
- Used by: unused in file
- Visibility: public
- Lines: 121–146 (proof 126–146, ~21 lines)
- Notes: long(30-50) — proof body ~21 lines; none other

### theorem prime_order_integrality_general
- Type: `(W) {x y : ℚ} (hns : … Nonsingular x y) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (htors : (p:ℤ) • … = 0) (_hne : … ≠ 0) : (∃ x₀:ℤ, (x₀:ℚ)=x) ∧ ∃ y₀:ℤ, (y₀:ℚ)=y`
- What: If `P` has odd prime order on a general integral curve, then `P` has integral affine coordinates (Nagell–Lutz for odd prime order).
- How: Obtains integral `x` from `x_integral_of_odd_prime_torsion_general`, then integral `y` from `y_integral_of_x_integral_on_general_curve` via the curve equation `curveQ_equation_iff`.
- Hypotheses: `(x,y)` nonsingular; `p` odd prime; `p`-torsion; point nonzero (unused, named `_hne`).
- Uses from project: `x_integral_of_odd_prime_torsion_general`, `y_integral_of_x_integral_on_general_curve`, `curveQ_equation_iff`
- Used by: unused in file
- Visibility: public
- Lines: 152–160 (proof 158–160, ~3 lines)
- Notes: none; hypothesis `_hne` unused

### theorem bounded_den_of_order_two_general
- Type: `(W) {x y : ℚ} (hns : … Nonsingular x y) (h2 : (2:ℤ) • … = 0) : (∃ n:ℤ, (n:ℚ)=4*x) ∧ ∃ m:ℤ, (m:ℚ)=8*y`
- What: If `2•P = 0` on a general integral curve, then `4x ∈ ℤ` and `8y ∈ ℤ` (the weaker 2-torsion denominator bound).
- How: From `ψ₂=0` extracts `2y+a₁x+a₃=0`; uses `mk_ψ₂_sq` + `evalEval_eq_of_mk_eq` to get `Ψ₂Sq.eval x = 0`, i.e. `aeval x Ψ₂Sq = 0`; `den_dvd_of_is_root` with `leadingCoeff_Ψ₂Sq` (= 4) gives `x.den ∣ 4`, hence `4x` is integral (explicit `field_simp`/`push_cast` construction of the witness `α*k`); finally `8y = -(a₁·n₀) - 4a₃` by `push_cast`/`linarith`.
- Hypotheses: `(x,y)` nonsingular; point is 2-torsion.
- Uses from project: `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `curveQ_a₁`, `curveQ_a₃`  (+ imported `mk_ψ₂_sq`, `evalEval_eq_of_mk_eq`, `map_Ψ₂Sq`, `leadingCoeff_Ψ₂Sq`, `den_dvd_of_is_root`, `isFractionRingDen`)
- Used by: unused in file
- Visibility: public
- Lines: 170–206 (proof 174–206, ~33 lines)
- Notes: long(30-50) — proof body ~33 lines; none other

---

## File Summary

- **Total decls: 6** — defs: 0 / lemmas+theorems: 6 / instances: 0. (No structures/classes/abbrevs/inductives.)
- **Key API (used by ≥3 in-file):** `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` (used by 3: x_integral_of_odd_prime_torsion_general, integrality_of_order_four_general, bounded_den_of_order_two_general). `y_integral_of_x_integral_on_general_curve` (used by 2) and `two_nsmul_eq_zero_of_ψ₂_eq_zero` (used by 1) fall below the ≥3 bar.
- **Unused decls (no in-file consumer; these are the project's exported top-level results):** `integrality_of_order_four_general`, `prime_order_integrality_general`, `bounded_den_of_order_two_general`.
- **Decls with sorry:** none.
- **Decls with set_option:** none.
- **Proofs >50 lines (OVER-50):** none (count 0).
- **Proofs 30–50 lines (long):** 1 — `bounded_den_of_order_two_general` (~33). (`x_integral_of_odd_prime_torsion_general` ~24 and `integrality_of_order_four_general` ~21 are under 30 by proof-body line count; total-decl spans land in the 30–50 window but proof bodies are <30.)

Documented: 6 declarations.
Output: /Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/.mathlib-quality/overview/inventory/LutzNagell_LutzNagellTheorem_GeneralPrimeOrder.md
