# Inventory: `LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean`

Generalization of `GeneralPrimeOrder.lean` from `ℤ/ℚ` to a UFD `R` with fraction field `K`. Prime-order torsion integrality for Weierstrass curves over UFDs.

Module-wide context (`variable`s, lines 29–31):
- `{R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]`
- `{K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]`
- `(W : WeierstrassCurve R)`
- `open WeierstrassCurve Polynomial IsFractionRing`

---

### theorem y_isInteger_of_x_isInteger_on_curve
- Type:
  ```
  (W : WeierstrassCurve R) {x y : K}
    (hcurve : y^2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x^3 + algebraMap R K W.a₂ * x^2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {x₀ : R} (hx : algebraMap R K x₀ = x) :
    IsLocalization.IsInteger R y
  ```
- What: On the Weierstrass curve over the fraction field `K`, if the affine `x`-coordinate is integral (lies in the image of `R`) and `(x,y)` satisfies the Weierstrass equation, then the `y`-coordinate is also integral.
- How: Builds the monic quadratic `X² + C c₁ X + C c₀ ∈ R[X]` with `c₁ = a₁x₀ + a₃`, `c₀ = -(x₀³ + a₂x₀² + a₄x₀ + a₆)`, shows `y` is a root of it (via `aeval` simp + `linear_combination hc`), proves it monic using `Polynomial.Monic.add_of_left`, `monic_X_pow`, `degree_C_mul_X_le`/`degree_C_le`/`degree_add_eq_left_of_degree_lt`, and concludes integrality of `y` via mathlib's `isInteger_of_is_root_of_monic` (root of a monic polynomial over an integrally-closed/fraction-ring setup is integral).
- Hypotheses: `(x,y)` lies on the Weierstrass curve (coefficients mapped from `R`); `x` equals the image `algebraMap R K x₀` of some `x₀ ∈ R`.
- Uses from project: []
- Used by: `integrality_of_order_four_squarefree`, `prime_order_integrality_squarefree`
- Visibility: public
- Lines: 35–56 (proof ~12 lines, body 43–56)
- Notes: `omit [DecidableEq K]` in front; none

---

### theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero
- Type:
  ```
  (W : WeierstrassCurve R) {x y : K}
    (hns : (curveK R K W).toAffine.Nonsingular x y) (n : ℤ)
    (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    ((curveK R K W).ψ n).evalEval x y = 0
  ```
- What: If `n • P = 0` in the Jacobian point group for the affine point `P = (x,y)`, then the `n`-th division polynomial `ψ_n` of the base-changed curve vanishes at `(x,y)`.
- How: Rewrites `n • P` using `zsmul_eq_smulEval` (relating scalar multiplication to the division-polynomial evaluation form), uses `Jacobian.Point.zero_point` for the zero element, transports the torsion equality through `Jacobian.Point.ext_iff`, and finishes via `Jacobian.Z_eq_zero_of_equiv` applied to `Quotient.exact htors` (the Jacobian-coordinate `Z = 0` characterization of the point at infinity).
- Hypotheses: `(x,y)` is a nonsingular affine point of the base-changed curve `curveK R K W`; `n • P = 0` in the Jacobian group.
- Uses from project: [`curveK`]  (note: `curveK` is imported, not defined in this file)
- Used by: `x_isInteger_of_odd_prime_torsion_squarefree`, `integrality_of_order_four_squarefree`, `den_dvd_of_order_two`
- Visibility: public
- Lines: 60–71 (proof ~5 lines, body 67–71)
- Notes: `omit [IsDomain R] [UniqueFactorizationMonoid R] [DecidableEq K] [IsFractionRing R K]`; none

---

### theorem isInteger_of_root_squarefree_leading_coeff
- Type:
  ```
  (W : WeierstrassCurve R) {x y : K}
    (heq : y^2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x^3 + algebraMap R K W.a₂ * x^2 + algebraMap R K W.a₄ * x + algebraMap R K W.a₆)
    {f : R[X]} (hroot : aeval x f = 0) (hsf : Squarefree f.leadingCoeff) :
    IsLocalization.IsInteger R x
  ```
- What: **Key theorem.** If `x ∈ K` is a root of a polynomial `f ∈ R[X]` whose leading coefficient is squarefree, and `(x,y)` lies on the Weierstrass curve, then `x` is integral (lies in `R`).
- How: Combines the rational root theorem with the project's denominator lemma. `den_dvd_of_is_root` gives `den(x) ∣ leadingCoeff f`. To show `den(x)` is a unit, argues by contradiction: a non-unit non-zero element has an irreducible (hence prime, via `UniqueFactorizationMonoid.irreducible_iff_prime`) factor `q` (`WfDvdMonoid.exists_irreducible_factor`); since `leadingCoeff f` is squarefree, `q² ∤ den(x)` (a `q²` divisor would force `q` to be a unit, contradiction); but `den_no_simple_prime_factor_of_on_curve` says a prime dividing `den(x)` exactly once cannot occur on the curve — contradiction. Hence `den(x)` is a unit and `isInteger_of_isUnit_den` concludes.
- Hypotheses: `(x,y)` on the curve; `x` is a root of some `f ∈ R[X]`; `f.leadingCoeff` is squarefree in `R`.
- Uses from project: [`den_dvd_of_is_root`, `den_no_simple_prime_factor_of_on_curve`]
- Used by: `x_isInteger_of_odd_prime_torsion_squarefree`, `integrality_of_order_four_squarefree`
- Visibility: public
- Lines: 75–100 (proof ~12 lines, body 88–100)
- Notes: `omit [DecidableEq K]`; none

---

### theorem x_isInteger_of_odd_prime_torsion_squarefree
- Type:
  ```
  (W : WeierstrassCurve R) {x y : K}
    (hns : (curveK R K W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (p : R)) :
    IsLocalization.IsInteger R x
  ```
- What: For an odd prime `p`, if `p • P = 0` (so `P` is `p`-torsion) and `(p : R)` is squarefree, then the `x`-coordinate of `P` is integral.
- How: From `evalEval_ψ_eq_zero_of_zsmul_eq_zero`, `ψ_p(x,y) = 0`. For odd `p`, `evalEval_ψ_odd` rewrites `ψ_p` to `preΨ_p` (the polynomial-in-`x` part), `Int.even_coe_nat`/`hp.even_iff` supply oddness; `WeierstrassCurve.map_preΨ` + `eval_map` identify `(curveK).preΨ p` with `(W.preΨ p).map (algebraMap R K)`, turning the hypothesis into `aeval x (W.preΨ p) = 0`. The leading coefficient of `preΨ_p` equals `(p : R)` for odd `p` via `W.leadingCoeff_preΨ` (with `Int.cast_natCast`), which is squarefree by hypothesis. Concludes with `isInteger_of_root_squarefree_leading_coeff` and `curveK_equation_iff`.
- Hypotheses: `P=(x,y)` nonsingular on `curveK`; `p` an odd prime; `p • P = 0`; `(p:R)` squarefree.
- Uses from project: [`curveK`, `evalEval_ψ_eq_zero_of_zsmul_eq_zero`, `isInteger_of_root_squarefree_leading_coeff`, `curveK_equation_iff`]
- Used by: `prime_order_integrality_squarefree`
- Visibility: public
- Lines: 111–132 (proof ~13 lines, body 118–132)
- Notes: `omit [DecidableEq K]`; none

---

### theorem two_nsmul_eq_zero_of_ψ₂_eq_zero
- Type:
  ```
  (W : WeierstrassCurve R) {x y : K}
    (hns : (curveK R K W).toAffine.Nonsingular x y)
    (hψ : (curveK R K W).ψ₂.evalEval x y = 0) :
    (2 : ℕ) • (Affine.Point.some _ _ hns) = 0
  ```
- What: If the 2-division polynomial `ψ₂` vanishes at `(x,y)`, then the affine point `P=(x,y)` is 2-torsion (`2 • P = 0` in the affine group).
- How: Unfolds `ψ₂` and `Affine.evalEval_polynomialY` so the hypothesis becomes a relation on `Y`-derivatives; rewrites `2 • P` via `two_nsmul`, then applies `WeierstrassCurve.Affine.Point.add_of_Y_eq` (doubling at a point equal to its own negation gives the identity) with `negY` unfolded and closes with `linear_combination hψ`.
- Hypotheses: `(x,y)` nonsingular on `curveK`; `ψ₂(x,y) = 0`.
- Uses from project: [`curveK`]
- Used by: `integrality_of_order_four_squarefree`
- Visibility: public
- Lines: 136–146 (proof ~5 lines, body 141–146)
- Notes: `omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R K]`; none

---

### theorem integrality_of_order_four_squarefree
- Type:
  ```
  (W : WeierstrassCurve R) {x y : K}
    (hns : (curveK R K W).toAffine.Nonsingular x y)
    (h4 : (4 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (h2ne : (2 : ℕ) • (Affine.Point.some _ _ hns) ≠ 0)
    (hsf : Squarefree (2 : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y
  ```
- What: If `P` is exactly order-4 torsion (`4•P = 0` but `2•P ≠ 0`) and `(2 : R)` is squarefree, then both coordinates of `P` are integral.
- How: From `evalEval_ψ_eq_zero_of_zsmul_eq_zero`, `ψ₄(x,y) = 0`; `WeierstrassCurve.ψ_four` factors `ψ₄ = (C 2) · preΨ₄ · ψ₂` (after `evalEval_mul`/`evalEval_C`), so `mul_eq_zero` splits into `preΨ₄(x)=0` or `ψ₂(x,y)=0`. The `ψ₂` branch contradicts `h2ne` via `two_nsmul_eq_zero_of_ψ₂_eq_zero`. In the `preΨ₄` branch, `map_preΨ₄` + `eval_map` give `aeval x W.preΨ₄ = 0`; `W.leadingCoeff_preΨ₄ hsf.ne_zero` shows the leading coefficient is `(2:R)` (squarefree); `isInteger_of_root_squarefree_leading_coeff` gives `x` integral, and `y_isInteger_of_x_isInteger_on_curve` lifts to `y`.
- Hypotheses: `(x,y)` nonsingular on `curveK`; `4•P = 0`; `2•P ≠ 0`; `(2:R)` squarefree.
- Uses from project: [`curveK`, `evalEval_ψ_eq_zero_of_zsmul_eq_zero`, `curveK_equation_iff`, `isInteger_of_root_squarefree_leading_coeff`, `y_isInteger_of_x_isInteger_on_curve`, `two_nsmul_eq_zero_of_ψ₂_eq_zero`]
- Used by: unused in file
- Visibility: public
- Lines: 150–172 (proof ~14 lines, body 156–172)
- Notes: none

---

### theorem den_dvd_of_order_two
- Type:
  ```
  (W : WeierstrassCurve R) (h4_ne : (4 : R) ≠ 0) {x y : K}
    (hns : (curveK R K W).toAffine.Nonsingular x y)
    (h2 : (2 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (IsFractionRing.den R x : R) ∣ (4 : R)
  ```
- What: If `P=(x,y)` is 2-torsion (`2•P = 0`) and `(4 : R) ≠ 0`, then the denominator of the `x`-coordinate divides `4` in `R` (bounded denominators for 2-torsion).
- How: From `evalEval_ψ_eq_zero_of_zsmul_eq_zero`, `ψ₂(x,y) = 0`; `WeierstrassCurve.ψ_two` plus `Affine.CoordinateRing.mk_ψ₂_sq` and `evalEval_eq_of_mk_eq` give `Ψ₂Sq.eval x = 0` (using `ψ₂² = Ψ₂Sq` on the coordinate ring; `zero_pow two_ne_zero`). `map_Ψ₂Sq` + `eval_map` convert to `aeval x W.Ψ₂Sq = 0`; `den_dvd_of_is_root` gives `den(x) ∣ leadingCoeff (W.Ψ₂Sq)`, and `W.leadingCoeff_Ψ₂Sq h4_ne` identifies that leading coefficient with `4`.
- Hypotheses: `(4:R) ≠ 0` (automatic for `CharZero R`); `(x,y)` nonsingular on `curveK`; `2•P = 0`.
- Uses from project: [`curveK`, `evalEval_ψ_eq_zero_of_zsmul_eq_zero`, `den_dvd_of_is_root`]
- Used by: unused in file
- Visibility: public
- Lines: 176–196 (proof ~13 lines, body 182–196)
- Notes: `omit [DecidableEq K]`; none

---

### theorem prime_order_integrality_squarefree
- Type:
  ```
  (W : WeierstrassCurve R) {x y : K}
    (hns : (curveK R K W).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (htors : (p : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (p : R)) :
    (IsLocalization.IsInteger R x) ∧ IsLocalization.IsInteger R y
  ```
- What: Full integrality (both `x` and `y`) for odd prime-order torsion when `(p : R)` is squarefree.
- How: Combines two project lemmas: `x_isInteger_of_odd_prime_torsion_squarefree` gives `x = algebraMap R K x₀` integral, then `y_isInteger_of_x_isInteger_on_curve` (with `curveK_equation_iff` providing the Weierstrass equation from nonsingularity) lifts to `y`.
- Hypotheses: `(x,y)` nonsingular on `curveK`; `p` an odd prime; `p•P = 0`; `(p:R)` squarefree.
- Uses from project: [`curveK`, `x_isInteger_of_odd_prime_torsion_squarefree`, `curveK_equation_iff`, `y_isInteger_of_x_isInteger_on_curve`]
- Used by: unused in file
- Visibility: public
- Lines: 200–211 (proof ~4 lines, body 208–211)
- Notes: `omit [DecidableEq K]`; none

---

## File Summary

- **Total declarations: 7** — defs 0 / lemmas+theorems 7 / instances 0. (No def/instance/structure/class/abbrev/inductive present.)
- **Key API (used by ≥3 in-file):**
  - `evalEval_ψ_eq_zero_of_zsmul_eq_zero` — used by 3 (`x_isInteger_of_odd_prime_torsion_squarefree`, `integrality_of_order_four_squarefree`, `den_dvd_of_order_two`).
  - `isInteger_of_root_squarefree_leading_coeff` — used by 2 in-file (the "Key theorem"; high-importance but strictly 2 in-file callers).
  - (`curveK`, `curveK_equation_iff`, `den_dvd_of_is_root` are imported, not defined here.)
- **Unused decls (no in-file consumer; these are the project's terminal/export results):** `integrality_of_order_four_squarefree`, `den_dvd_of_order_two`, `prime_order_integrality_squarefree`.
- **Decls with `sorry`: none.**
- **Decls with `set_option`: none.**
- **Proofs >50 lines (OVER-50): none (count 0).**
- **Proofs 30–50 lines long(30-50): none (count 0).** Longest proof body is ~14 lines (`integrality_of_order_four_squarefree`).
- **No TODO markers.** All theorems use `omit` clauses to drop unneeded typeclass assumptions (noted per-decl).
