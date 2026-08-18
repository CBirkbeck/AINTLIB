# Inventory: LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean

File: `projects/NagellLutz/LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean`
Namespace: `LutzNagell.LutzNagellTheorem`
`variable (W : WeierstrassCurve ℤ)`

---

### lemma kappa_sq_eq_Psi2Sq_eval_general
- Type: `{x₀ y₀ : ℤ} (hcurve : y₀^2 + W.a₁*x₀*y₀ + W.a₃*y₀ = x₀^3 + W.a₂*x₀^2 + W.a₄*x₀ + W.a₆) : (2*y₀ + W.a₁*x₀ + W.a₃)^2 = 4*x₀^3 + W.b₂*x₀^2 + 2*W.b₄*x₀ + W.b₆`
- What: Completing the square on the Weierstrass equation shows that `κ₀² = (2y₀+a₁x₀+a₃)²` equals the polynomial `Ψ₂Sq(x₀) = 4x₀³+b₂x₀²+2b₄x₀+b₆`.
- How: Unfold the `bᵢ` invariants to the `aᵢ` via `simp only [b₂, b₄, b₆]`, then `nlinarith` discharges the resulting polynomial identity using the curve hypothesis `hcurve`.
- Hypotheses: `(x₀,y₀)` satisfies the integral Weierstrass curve equation.
- Uses from project: []
- Used by: `lutz_nagell_discriminant_general`
- Visibility: private
- Lines: 34-41 (proof 2 lines)
- Notes: none

### lemma h_sq_add_four_prePsi3_eq_general
- Type: `(x₀ : ℤ) : (6*x₀^2 + W.b₂*x₀ + W.b₄)^2 + 4*(3*x₀^4 + W.b₂*x₀^3 + 3*W.b₄*x₀^2 + 3*W.b₆*x₀ + W.b₈) = (12*x₀ + W.b₂)*(4*x₀^3 + W.b₂*x₀^2 + 2*W.b₄*x₀ + W.b₆)`
- What: The polynomial identity `h(x)² + 4·Ψ₃(x) = (12x + b₂)·Ψ₂Sq(x)` where `h = 6x²+b₂x+b₄`, relating the doubling-numerator polynomials.
- How: Unfold the `bᵢ` invariants (`simp only [b₂,b₄,b₆,b₈]`) so the hidden relation `b₂b₆ − b₄² = 4b₈` becomes visible at the `aᵢ` level, then `ring` closes the identity.
- Hypotheses: none (pure polynomial identity in `x₀`).
- Uses from project: []
- Used by: `kappa_sq_dvd_four_delta_of_coord_identity`
- Visibility: private
- Lines: 45-52 (proof 3 lines)
- Notes: none

### lemma bezout_general
- Type: `(x₀ : ℤ) : (432*x₀^3 + … + (−b₂^3 + 36*b₂*b₄ − 108*b₆))*(4*x₀^3 + b₂*x₀^2 + 2*b₄*x₀ + b₆) + (−48*x₀^2 − 8*b₂*x₀ + (b₂^2 − 32*b₄))*(6*x₀^2 + b₂*x₀ + b₄)^2 = 4*W.Δ` (abbreviated)
- What: A Bézout-style identity `d₁·Ψ₂Sq(x) + d₂·h(x)² = 4Δ` expressing `4·discriminant` as an explicit polynomial combination of `Ψ₂Sq` and `h²`.
- How: Unfold `bᵢ` and `Δ` to the `aᵢ` (`simp only [b₂,b₄,b₆,b₈,Δ]`), then `ring` verifies the polynomial identity.
- Hypotheses: none (pure polynomial identity in `x₀`).
- Uses from project: []
- Used by: `kappa_sq_dvd_four_delta_of_coord_identity`
- Visibility: private
- Lines: 55-63 (proof 3 lines)
- Notes: none

### lemma kappa_sq_dvd_four_delta_of_coord_identity
- Type: `(x₀ κ₀ : ℤ) (hkappa : κ₀^2 = 4*x₀^3 + W.b₂*x₀^2 + 2*W.b₄*x₀ + W.b₆) (hdvd_prePsi : κ₀^2 ∣ 4*(3*x₀^4 + W.b₂*x₀^3 + 3*W.b₄*x₀^2 + 3*W.b₆*x₀ + W.b₈)) : κ₀^2 ∣ 4*W.Δ`
- What: Pure-divisibility step: given `κ₀² = Ψ₂Sq(x₀)` and `κ₀² | 4·Ψ₃(x₀)`, concludes `κ₀² | 4Δ`.
- How: Sets abbreviations for `Ψ₂Sq, h, Ψ₃`; derives `κ₀² | h²` by rewriting `h² = (12x₀+b₂)·Ψ₂Sq − 4·Ψ₃` (via `h_sq_add_four_prePsi3_eq_general`) as a difference of multiples of `κ₀²`; then rewrites the goal with `bezout_general` and closes with `dvd_add` / `dvd_mul_of_dvd_right`, using `hkappa` to exhibit `κ₀² | Ψ₂Sq`.
- Hypotheses: `κ₀²` equals the `Ψ₂Sq` polynomial at `x₀`; `κ₀²` divides `4·Ψ₃(x₀)`.
- Uses from project: [`h_sq_add_four_prePsi3_eq_general`, `bezout_general`]
- Used by: `lutz_nagell_discriminant_general`
- Visibility: private
- Lines: 68-83 (proof 14 lines)
- Notes: none

### lemma curveZ_equation_of_integral
- Type: `{x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) {x₀ y₀ : ℤ} (hx : (x₀:ℚ)=x) (hy : (y₀:ℚ)=y) : y₀^2 + W.a₁*x₀*y₀ + W.a₃*y₀ = x₀^3 + W.a₂*x₀^2 + W.a₄*x₀ + W.a₆`
- What: If a nonsingular rational point has integer coordinates, those integers satisfy the integral Weierstrass equation.
- How: Establishes the equation over `ℚ` from `curveQ_equation_iff` applied to the nonsingularity's `.left` (after substituting `hx`,`hy` and `linarith`), then `exact_mod_cast` transfers the rational identity down to `ℤ`.
- Hypotheses: `(x,y)` is a nonsingular point of `curveQ W`; its coordinates equal the integers `x₀,y₀`.
- Uses from project: [`curveQ_equation_iff`]
- Used by: `lutz_nagell_discriminant_general`
- Visibility: private
- Lines: 88-96 (proof 4 lines)
- Notes: none

### lemma addOrderOf_ne_two_of_kappa_ne_zero
- Type: `{x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) {x₀ y₀ : ℤ} (hx : (x₀:ℚ)=x) (hy : (y₀:ℚ)=y) (hκ : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) : addOrderOf (Affine.Point.some _ _ hns) ≠ 2`
- What: If `κ₀ = 2y₀+a₁x₀+a₃ ≠ 0`, the point cannot have additive order 2.
- How: Assume order 2; then `2•P = 0` (`addOrderOf_nsmul_eq_zero`), transfer to the Jacobian model (`nsmul_eq_zero_affine_to_jac`), and apply `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general` to get `ψ₂` vanishing; unfold `ψ_two`/`ψ₂`/`evalEval_polynomialY` plus `curveQ_a₁`,`curveQ_a₃`, derive `2y₀+a₁x₀+a₃ = 0` over `ℚ` (`linarith`), cast to `ℤ`, contradicting `hκ`.
- Hypotheses: nonsingular point with integer coordinates and nonzero `κ₀`.
- Uses from project: [`nsmul_eq_zero_affine_to_jac`, `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `curveQ_a₁`, `curveQ_a₃`]
- Used by: `kappa_sq_dvd_four_Psi3`
- Visibility: private
- Lines: 99-115 (proof 17 lines)
- Notes: none

### lemma Phi2_eval_eq
- Type: `(x : ℚ) : eval x ((curveQ W).Φ 2) = x * eval x (curveQ W).Ψ₂Sq − eval x (curveQ W).Ψ₃`
- What: Evaluation form of the division-polynomial identity `Φ₂ = X·Ψ₂Sq − Ψ₃`.
- How: Rewrites `(curveQ W).Φ 2` as `X*Ψ₂Sq − Ψ₃` using `WeierstrassCurve.Φ`, `ΨSq_two`, `preΨ_three`, `preΨ_one` (with `even_two`), then distributes the evaluation with `eval_sub`,`eval_mul`,`eval_X`.
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3`
- Visibility: private
- Lines: 121-128 (proof 5 lines)
- Notes: none

### lemma PsiSq_two_eval_eq
- Type: `(x : ℚ) : eval x ((curveQ W).ΨSq 2) = eval x (curveQ W).Ψ₂Sq`
- What: `ΨSq 2` evaluates to the same value as `Ψ₂Sq`.
- How: Single rewrite by `WeierstrassCurve.ΨSq_two`.
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3`
- Visibility: private
- Lines: 131-133 (proof 1 line)
- Notes: none

### lemma Psi2Sq_eval_eq
- Type: `(x : ℚ) : eval x (curveQ W).Ψ₂Sq = 4*x^3 + (W.b₂:ℚ)*x^2 + 2*(W.b₄:ℚ)*x + (W.b₆:ℚ)`
- What: Explicit evaluation of the polynomial `Ψ₂Sq` for `curveQ W` at a rational `x`.
- How: Shows `(curveQ W).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap ℤ ℚ)` via `map_Ψ₂Sq`, rewrites with `eval_map` and the `Ψ₂Sq` definition, simps the `eval₂` of the base-ring polynomial, then `push_cast; ring`.
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3`
- Visibility: private
- Lines: 136-145 (proof 7 lines)
- Notes: none

### lemma Psi3_eval_eq
- Type: `(x : ℚ) : eval x (curveQ W).Ψ₃ = 3*x^4 + (W.b₂:ℚ)*x^3 + 3*(W.b₄:ℚ)*x^2 + 3*(W.b₆:ℚ)*x + (W.b₈:ℚ)`
- What: Explicit evaluation of the polynomial `Ψ₃` for `curveQ W` at a rational `x`.
- How: Shows `(curveQ W).Ψ₃ = W.Ψ₃.map (algebraMap ℤ ℚ)` via `map_Ψ₃`, rewrites with `eval_map` and the `Ψ₃` definition, then simps the `eval₂` over the base-ring polynomial (`eval₂_*`, `algebraMap_int_eq`, `Int.coe_castRingHom`).
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3`
- Visibility: private
- Lines: 148-156 (proof 5 lines)
- Notes: none

### lemma kappa_sq_dvd_four_Psi3
- Type: `{x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) {x₀ y₀ : ℤ} (hx : (x₀:ℚ)=x) (hy : (y₀:ℚ)=y) {κ₀ : ℤ} (hκ₀ : κ₀ = 2*y₀ + W.a₁*x₀ + W.a₃) (hkappa_sq : κ₀^2 = 4*x₀^3 + W.b₂*x₀^2 + 2*W.b₄*x₀ + W.b₆) (hκ : κ₀ ≠ 0) : κ₀^2 ∣ 4*(3*x₀^4 + W.b₂*x₀^3 + 3*W.b₄*x₀^2 + 3*W.b₆*x₀ + W.b₈)`
- What: The core divisibility `κ₀² | 4·Ψ₃(x₀)`, obtained from the `2•P` x-coordinate formula together with integrality of the doubled point.
- How: Shows `addOrderOf P > 2` (excluding orders 1 and 2 via `Point.some_ne_zero`/`AddMonoid.addOrderOf_eq_one_iff` and `addOrderOf_ne_two_of_kappa_ne_zero`), so `2•P ≠ 0`; extracts `(x',y')` for `2•P` (`exists_some_of_ne_zero`), applies the doubling x-coordinate formula `x_coord_nsmul_eq_general` and rewrites it via `PsiSq_two_eval_eq`,`Phi2_eval_eq` to get `Ψ₃(x) = (x−x')·Ψ₂Sq(x)`; converts to the `κ₀²` form over `ℚ`; then case-splits on `lutz_nagell_integrality_general` for `2•P` (integral `x'` giving `Ψ₃(x₀) = κ₀²·(x₀−x'₀)`, vs order-2 giving `4x' = n₀` and `4·Ψ₃(x₀) = κ₀²·(4x₀−n₀)`), each via `exact_mod_cast` and an explicit divisibility witness.
- Hypotheses: nonsingular torsion point with integer coordinates; `κ₀` equals `2y₀+a₁x₀+a₃`, its square equals `Ψ₂Sq(x₀)`, and `κ₀ ≠ 0`.
- Uses from project: [`addOrderOf_ne_two_of_kappa_ne_zero`, `exists_some_of_ne_zero`, `x_coord_nsmul_eq_general`, `PsiSq_two_eval_eq`, `Phi2_eval_eq`, `Psi2Sq_eval_eq`, `Psi3_eval_eq`, `lutz_nagell_integrality_general`]
- Used by: `lutz_nagell_discriminant_general`
- Visibility: private
- Lines: 162-219 (proof 48 lines)
- Notes: long(30-50) — 48-line proof; case split on integrality, may merit `/decompose-proof`

### theorem lutz_nagell_discriminant_general
- Type: `{x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) {x₀ y₀ : ℤ} (hx : (x₀:ℚ)=x) (hy : (y₀:ℚ)=y) : (2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4*W.Δ`
- What: **General discriminant divisibility (Nagell–Lutz).** For a nonzero torsion point with integral coordinates, either `κ₀ = 0` or `κ₀² | 4Δ`.
- How: Sets `κ₀`; case-split on `κ₀ = 0` (left disjunct). Otherwise derives `κ₀² = Ψ₂Sq(x₀)` (`kappa_sq_eq_Psi2Sq_eval_general` ∘ `curveZ_equation_of_integral`), feeds it and `kappa_sq_dvd_four_Psi3` into `kappa_sq_dvd_four_delta_of_coord_identity`.
- Hypotheses: nonsingular rational torsion point whose coordinates are the integers `x₀,y₀`.
- Uses from project: [`kappa_sq_eq_Psi2Sq_eval_general`, `curveZ_equation_of_integral`, `kappa_sq_dvd_four_delta_of_coord_identity`, `kappa_sq_dvd_four_Psi3`]
- Used by: `lutz_nagell_general`
- Visibility: public
- Lines: 226-239 (proof 8 lines)
- Notes: none

### theorem lutz_nagell_general
- Type: `{x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : (∃ x₀ y₀ : ℤ, (x₀:ℚ)=x ∧ (y₀:ℚ)=y ∧ (2*y₀+W.a₁*x₀+W.a₃ = 0 ∨ (2*y₀+W.a₁*x₀+W.a₃)^2 ∣ 4*W.Δ)) ∨ (addOrderOf (Affine.Point.some _ _ hpt) = 2 ∧ (∃ n:ℤ,(n:ℚ)=4*x) ∧ ∃ m:ℤ,(m:ℚ)=8*y)`
- What: **Combined Lutz–Nagell theorem.** A nonzero torsion point either has integer coordinates obeying the `κ₀=0` / `κ₀²|4Δ` dichotomy, or has order exactly 2 with `4x, 8y ∈ ℤ`.
- How: Case-splits on `lutz_nagell_integrality_general`: in the integral case extracts `x₀,y₀` and applies `lutz_nagell_discriminant_general`; in the order-2 case returns the right disjunct directly.
- Hypotheses: nonsingular rational torsion point on `curveQ W`.
- Uses from project: [`lutz_nagell_integrality_general`, `lutz_nagell_discriminant_general`]
- Used by: unused in file
- Visibility: public
- Lines: 248-260 (proof 5 lines)
- Notes: none

---

## File Summary

- **Total decls: 12** — 0 defs / 12 lemmas+theorems (10 `private lemma`, 2 public `theorem`) / 0 instances.
- **Key API (used by ≥3 in-file):** none. The most-referenced in-file decl is `lutz_nagell_discriminant_general` (used by 1). Most helpers are used exactly once; the cluster feeds two public entry points.
- **Unused decls (no in-file consumer):** `lutz_nagell_general` (top-level export, consumed elsewhere in the project).
- **Decls with `sorry`:** none.
- **Decls with `set_option`:** none.
- **Proofs >50 lines (OVER-50):** none (count 0).
- **Proofs 30–50 lines (long):** 1 — `kappa_sq_dvd_four_Psi3` (48 lines).

Documented: 12 declarations.
Output: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/.mathlib-quality/overview/inventory/LutzNagell_LutzNagellTheorem_GeneralDiscriminant.md`
