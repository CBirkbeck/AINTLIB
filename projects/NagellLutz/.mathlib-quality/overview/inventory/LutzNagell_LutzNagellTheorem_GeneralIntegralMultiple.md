# Inventory: `LutzNagell/LutzNagellTheorem/GeneralIntegralMultiple.lean`

File-level role: For a general Weierstrass curve `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
over `ℚ` with integral coefficients (`W : WeierstrassCurve ℤ`, `curveQ W` its base change to `ℚ`),
proves that if `n • P` has integral affine coordinates then so does `P`. This is the general-curve
analogue of the PID development in `PIDIntegralMultiple.lean`.

File-wide context:
- `variable (W : WeierstrassCurve ℤ)` — every declaration is parametrised by an integral Weierstrass curve.
- `open WeierstrassCurve Polynomial`.
- Namespace `LutzNagell.LutzNagellTheorem`.

---

### theorem x_coord_nsmul_eq_general
- Type:
  ```
  {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) {n : ℤ} (_hn : n ≠ 0)
  {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
  (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
  x' * ((curveQ W).ΨSq n).eval x = ((curveQ W).Φ n).eval x
  ```
- What: The x-coordinate `x'` of `n • P` is related to the x-coordinate `x` of `P` by the division-polynomial identity `x' · ΨSq_n(x) = Φ_n(x)` over `ℚ`.
- How: Transports the affine multiplication `hnP` through `Jacobian.Point.toAffineAddEquiv` to a Jacobian-coordinate equality, uses `zsmul_eq_smulEval` to rewrite `n • P` as the explicit `smulEval` triple, extracts the X-coordinate proportionality via `X_eq_of_equiv` (representatives equivalent up to scaling), then converts the Jacobian division-polynomial evaluations `φ`/`ψ` to univariate `Φ`/`ΨSq` evaluations via `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`, `evalEval_ψ_eq_evalEval_Ψ`, closing with `linarith`. Hinges on `X_eq_of_equiv` and `zsmul_eq_smulEval`.
- Hypotheses: `P = (x,y)` and `P' = (x',y')` nonsingular points on the base-changed curve over `ℚ`; `n ≠ 0`; and `n • P = P'` in the affine point group.
- Uses from project: `curveQ`, `zsmul_eq_smulEval`, `smulEval`, `X_eq_of_equiv`, `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`, `evalEval_ψ_eq_evalEval_Ψ`
- Used by: `x_integral_of_nsmul_x_integral_general`
- Visibility: public
- Lines: 27–53 (proof ≈ 21 lines)
- Notes: long(30-50)? No — proof ≈ 21 lines; uses `open Jacobian in` twice and `classical`. none

---

### theorem monic_Φ_sub_smul_ΨSq_general
- Type: `{n : ℤ} (hn : n ≠ 0) (c : ℤ) : (W.Φ n - C c * W.ΨSq n).Monic`
- What: For any integer `c` and nonzero `n`, the integer polynomial `Φ_n − c·ΨSq_n` is monic.
- How: `Φ_n` is monic with leading coefficient 1 (`leadingCoeff_Φ`), so `Monic.sub_of_left` reduces monicity to a strict degree inequality; a `calc` bounds `natDegree (C c * ΨSq_n) ≤ natDegree ΨSq_n = n.natAbs² − 1 < n.natAbs² = natDegree Φ_n` using `natDegree_ΨSq` and `natDegree_Φ`.
- Hypotheses: `n ≠ 0`; `c : ℤ` arbitrary.
- Uses from project: `leadingCoeff_Φ`, `natDegree_ΨSq`, `natDegree_Φ`
- Used by: `x_integral_of_nsmul_x_integral_general`
- Visibility: public
- Lines: 58–67 (proof ≈ 10 lines)
- Notes: none

---

### theorem x_integral_of_nsmul_x_integral_general
- Type:
  ```
  {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) {n : ℤ} (hn : n ≠ 0)
  {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
  (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
  {c : ℤ} (hc : (c : ℚ) = x') : ∃ x₀ : ℤ, (x₀ : ℚ) = x
  ```
- What: If `n • P` has integral x-coordinate `x' = c ∈ ℤ`, then `P` has integral x-coordinate.
- How: From `x_coord_nsmul_eq_general`, substituting `x' = c`, the rational `x` is a root of the integer monic polynomial `Φ_n − C c·ΨSq_n` (built by base-changing `Φ`,`ΨSq` to `ℚ` via `map_Φ`/`map_ΨSq` and reconciling the eval); since `x` is rational and a root of a monic integer polynomial, the rational-root / integrally-closed argument `isInteger_of_is_root_of_monic` (with `monic_Φ_sub_smul_ΨSq_general`) yields an integer preimage `x₀`.
- Hypotheses: `P`, `P'` nonsingular over `ℚ`; `n ≠ 0`; `n • P = P'`; the x-coordinate of `P'` equals the integer `c`.
- Uses from project: `x_coord_nsmul_eq_general`, `curveQ`, `map_Φ`, `map_ΨSq`, `monic_Φ_sub_smul_ΨSq_general`
- Used by: `integral_of_nsmul_integral_general`
- Visibility: public
- Lines: 72–92 (proof ≈ 14 lines)
- Notes: relies on mathlib `isInteger_of_is_root_of_monic` (from `RingTheory.Polynomial.RationalRoot`). none

---

### theorem integral_of_nsmul_integral_general
- Type:
  ```
  {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) {n : ℤ} (hn : n ≠ 0)
  {x' y' : ℚ} (hns' : (curveQ W).toAffine.Nonsingular x' y')
  (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
  (hx' : ∃ x₀ : ℤ, (x₀ : ℚ) = x') (_hy' : ∃ y₀ : ℤ, (y₀ : ℚ) = y') :
  (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y
  ```
- What: Main result — if `n • P` has integral affine coordinates on a general integral Weierstrass curve, then `P` has integral affine coordinates.
- How: Destructure the integral x-coordinate `c` of `P'`; apply `x_integral_of_nsmul_x_integral_general` to get integrality of `x`; then integrality of `y` follows from integrality of `x` via `y_integral_of_x_integral_on_general_curve` applied to the curve equation extracted by `curveQ_equation_iff` from the nonsingularity of `P`.
- Hypotheses: `P`, `P'` nonsingular over `ℚ`; `n ≠ 0`; `n • P = P'`; both coordinates of `P'` are integral (the y-integrality hypothesis `_hy'` is unused — y-integrality of `P` is derived from x).
- Uses from project: `x_integral_of_nsmul_x_integral_general`, `y_integral_of_x_integral_on_general_curve`, `curveQ_equation_iff`, `curveQ`
- Used by: unused in file
- Visibility: public
- Lines: 98–109 (proof ≈ 5 lines)
- Notes: hypothesis `_hy'` is unused (y-integrality re-derived from x via the curve equation). none

---

## File Summary

- Total decls: 4 (0 defs / 4 lemmas+theorems / 0 instances). All four are `theorem`s.
- Key API (used by ≥3 in-file): none — the file is a short linear chain (`x_coord_nsmul_eq_general` → `x_integral_of_nsmul_x_integral_general` → `integral_of_nsmul_integral_general`; `monic_Φ_sub_smul_ΨSq_general` → `x_integral_of_nsmul_x_integral_general`); no declaration is used by ≥3 others.
- Unused decls (in-file): `integral_of_nsmul_integral_general` (the public top-level export; consumed elsewhere in the project, not within this file).
- Decls with `sorry`: none.
- Decls with `set_option`: none.
- Proofs >50 lines (OVER-50): none (count 0).
- Proofs 30–50 lines (long): none (count 0). Longest proof is `x_coord_nsmul_eq_general` at ≈21 lines.

Decls documented: 4
Output path: /Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/.mathlib-quality/overview/inventory/LutzNagell_LutzNagellTheorem_GeneralIntegralMultiple.md
