# Inventory: LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean

File-level context: over a UFD `R` with fraction field `K = Frac(R)`, if `n • P` has integral affine coordinates on a Weierstrass curve, then `P` already has integral affine coordinates. Generalizes `GeneralIntegralMultiple.lean` from `ℤ/ℚ` to a UFD.

Shared section variables: `{R}` `[CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`; `{K}` `[Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]`; `(W : WeierstrassCurve R)`.

---

### theorem monic_Φ_sub_smul_ΨSq
- Type: `{n : ℤ} (hn : (n : R) ≠ 0) (c : R) : (W.Φ n - C c * W.ΨSq n).Monic`
- What: The polynomial `Φ_n - c·ΨSq_n` (the n-th division-polynomial numerator minus a constant `c` times the squared denominator) is monic over `R`, for any `c : R` and any `n` that is nonzero in `R`.
- How: Uses `Polynomial.Monic.sub_of_left` reducing to showing `Φ_n` is monic (its leading coefficient is 1) and that the degree of `C c * ΨSq_n` is strictly less than that of `Φ_n`; the degree bound is a `calc` chain via `natDegree_C_mul_le`, the project facts `natDegree_ΨSq` (= `n.natAbs^2 - 1`) and `natDegree_Φ` (= `n.natAbs^2`), and `Nat.pred_lt`.
- Hypotheses: `n` nonzero as an element of `R`; `c` an arbitrary element of `R`.
- Uses from project: `leadingCoeff_Φ`, `natDegree_ΨSq`, `natDegree_Φ` (plus the structures `W.Φ`, `W.ΨSq`).
- Used by: `x_isInteger_of_nsmul_x_isInteger`
- Visibility: public
- Lines: 24–36 (proof ~7 lines)
- Notes: `omit [UniqueFactorizationMonoid R]`. none

### theorem x_coord_nsmul_eq
- Type: `{x y : K} (hns : (curveK R K W).toAffine.Nonsingular x y) {n : ℤ} (_hn : n ≠ 0) {x' y' : K} (hns' : (curveK R K W).toAffine.Nonsingular x' y') (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') : x' * ((curveK R K W).ΨSq n).eval x = ((curveK R K W).Φ n).eval x`
- What: If `P = (x,y)` is a nonsingular point on the curve over `K` and `n • P = (x', y')`, then the x-coordinate of `n • P` satisfies the division-polynomial identity `x' · ΨSq_n(x) = Φ_n(x)`.
- How: Transports the affine scalar-multiplication hypothesis into Jacobian coordinates via `Jacobian.Point.toAffineAddEquiv` and `map_zsmul`, rewrites the n-fold multiple using the project lemma `zsmul_eq_smulEval`, extracts the X-coordinate equivalence with `X_eq_of_equiv`, then converts the Jacobian `φ`/`ψ` evaluations to `Φ`/`ΨSq` via `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`, and `evalEval_ψ_eq_evalEval_Ψ`.
- Hypotheses: `(x,y)` and `(x',y')` nonsingular points on `curveK R K W`; `n ≠ 0`; `n • (x,y) = (x',y')` as affine points.
- Uses from project: `curveK`, `zsmul_eq_smulEval`, `smulEval`, `X_eq_of_equiv`, `evalEval_φ_eq_eval_Φ`, `evalEval_Ψ_sq_eq_eval_ΨSq`, `evalEval_ψ_eq_evalEval_Ψ`, `WeierstrassCurve.map_φ`, `WeierstrassCurve.map_ψ`.
- Used by: `x_isInteger_of_nsmul_x_isInteger`
- Visibility: public
- Lines: 40–67 (proof ~20 lines)
- Notes: `omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R K]`. Uses `classical` and nested `open Jacobian in`. none

### theorem x_isInteger_of_nsmul_x_isInteger
- Type: `{x y : K} (hns : … Nonsingular x y) {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0) {x' y' : K} (hns' : … Nonsingular x' y') (hnP : n • (some hns) = some hns') {c : R} (hc : algebraMap R K c = x') : IsLocalization.IsInteger R x`
- What: If `n • P = (x', y')` with x-coordinate `x'` integral (equal to `algebraMap R K c`), then the x-coordinate `x` of `P` is itself integral over `R`.
- How: Substitutes `x' = algebraMap R K c` into the coordinate identity from `x_coord_nsmul_eq`, rewrites `(curveK).Φ`/`ΨSq` as base-change maps (`map_Φ`, `map_ΨSq`), shows `x` is a root of the `R`-polynomial `Φ_n - C c * ΨSq_n` (via `aeval`/`eval₂_eq_eval_map` and `linear_combination`), then applies `isInteger_of_is_root_of_monic` together with monicity from `monic_Φ_sub_smul_ΨSq`.
- Hypotheses: `(x,y)`, `(x',y')` nonsingular; `n ≠ 0` in `ℤ` and in `R`; `n • P = (x',y')`; `x'` is the image of some `c : R`.
- Uses from project: `x_coord_nsmul_eq`, `curveK`, `map_Φ`, `map_ΨSq`, `monic_Φ_sub_smul_ΨSq`.
- Used by: `isInteger_of_nsmul_isInteger`
- Visibility: public
- Lines: 72–90 (proof ~11 lines)
- Notes: hinges on mathlib `isInteger_of_is_root_of_monic` (rational-root theorem over UFDs). none

### theorem isInteger_of_nsmul_isInteger
- Type: `{x y : K} (hns : … Nonsingular x y) {n : ℤ} (hn : n ≠ 0) (hn_R : (n : R) ≠ 0) {x' y' : K} (hns' : … Nonsingular x' y') (hnP : n • (some hns) = some hns') (hx' : IsLocalization.IsInteger R x') (_hy' : IsLocalization.IsInteger R y') : (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y`
- What: Main result of the file — if `n • P = (x', y')` has both coordinates integral over `R`, then both coordinates of `P` are integral over `R`.
- How: Destructures the integrality witness `hx'` to get `c`, obtains x-integrality from `x_isInteger_of_nsmul_x_isInteger`, then derives y-integrality from x-integrality on the curve via the project lemma `y_isInteger_of_x_isInteger_on_curve` (using `curveK_equation_iff` to feed the Weierstrass equation).
- Hypotheses: `(x,y)`, `(x',y')` nonsingular; `n ≠ 0` in `ℤ` and in `R`; `n • P = (x',y')`; both `x'` and `y'` integral over `R` (the `y'`-hypothesis is unused, `_hy'`).
- Uses from project: `x_isInteger_of_nsmul_x_isInteger`, `y_isInteger_of_x_isInteger_on_curve`, `curveK_equation_iff`.
- Used by: unused in file
- Visibility: public
- Lines: 93–105 (proof ~6 lines)
- Notes: none

---

## File Summary

- Total decls: 4 (defs: 0 / lemmas+theorems: 4 / instances: 0).
- Key API (used by ≥3 in-file): none. The most-used internal decl is `x_coord_nsmul_eq` (used by 1) and `monic_Φ_sub_smul_ΨSq` (used by 1); the file is a short linear chain culminating in `isInteger_of_nsmul_isInteger`.
- Unused decls (no in-file consumer): `isInteger_of_nsmul_isInteger` (the public top-level result, consumed elsewhere in the project).
- Decls with `sorry`: none.
- Decls with `set_option`: none.
- Proofs >50 lines: none (0).
- Proofs 30–50 lines: none (0). Longest proof is `x_coord_nsmul_eq` at ~20 lines.

Decls documented: 4
Output path: /Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/.mathlib-quality/overview/inventory/LutzNagell_LutzNagellTheorem_PIDIntegralMultiple.md
