# Inventory: LutzNagell/LutzNagellTheorem/PIDMain.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean`

Namespaces: `LutzNagell.PID` (lines 35–477), `LutzNagell.NumberField` (lines 481–574).
Ambient variables: PID `R` (`CommRing`, `IsDomain`, `IsPrincipalIdealRing`, `CharZero`), fraction field `K` (`Field`, `DecidableEq`, `Algebra R K`, `IsFractionRing R K`), `W : WeierstrassCurve R`.

---

### lemma nsmul_eq_zero_affine_to_jac
- Type: `{x y : K} {hns : (curveK R K W).toAffine.Nonsingular x y} {n : ℕ} (h : n • (Affine.Point.some _ _ hns) = 0) : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0`
- What: Transports the relation `n • P = 0` from the affine point group to the Jacobian point group, replacing the natural-number scalar by its integer cast.
- How: Rewrites `natCast_zsmul`, then transports `h` through the inverse of the `Jacobian.Point.toAffineAddEquiv` group isomorphism via `congrArg`, simplifying with `map_nsmul`/`map_zero`.
- Hypotheses: `(x,y)` is a nonsingular point on the base-changed curve over `K`; `n • P = 0` for the affine point `P`.
- Uses from project: []
- Used by: `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, `lutz_nagell_integrality_pid`, `addOrderOf_ne_two_of_kappa_ne_zero`
- Visibility: public
- Lines: 46–54 (proof 3 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [IsFractionRing R K]`

### lemma exists_some_of_ne_zero
- Type: `{Q : Affine.Point ((curveK R K W).toAffine)} (hQ : Q ≠ 0) : ∃ x y, ∃ hns : (curveK R K W).toAffine.Nonsingular x y, Q = .some _ _ hns`
- What: A nonzero affine point on the curve over `K` is necessarily of the constructor form `.some` carrying explicit nonsingular coordinates.
- How: Case-splits the affine point with `rcases`; the point-at-infinity case contradicts `hQ` via `absurd rfl`, the `.some` case returns its data.
- Hypotheses: `Q` is a nonzero affine point.
- Uses from project: []
- Used by: `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, `kappa_sq_dvd_four_Psi3_of_torsion`
- Visibility: public
- Lines: 56–64 (proof 3 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K]`

### theorem den_powerful_of_on_curve
- Type: `{x y : K} (heq : <Weierstrass equation over K>) : ∀ q : R, Prime q → q ∣ (IsFractionRing.den R x : R) → q ^ 2 ∣ (IsFractionRing.den R x : R)`
- What: For any point on the curve, every prime dividing the denominator of the `x`-coordinate (in `R`) divides it at least twice — denominators are "powerful", supported only at ramified-like primes; no torsion hypothesis.
- How: For a prime `q` dividing the denominator, applies `by_contra` and feeds the assumed non-square-divisibility to the imported `den_no_simple_prime_factor_of_on_curve` to derive a contradiction.
- Hypotheses: `(x,y)` satisfies the affine Weierstrass equation over `K`.
- Uses from project: [`den_no_simple_prime_factor_of_on_curve`] (imported from PIDPrimeOrder/PIDIntegralMultiple)
- Used by: unused in file (re-exported as `NumberField.den_powerful_number_field`)
- Visibility: public
- Lines: 68–75 (proof 1 line)
- Notes: `omit [CharZero R] [DecidableEq K]`; none

### lemma integrality_of_odd_prime_factor
- Type: `{x y : K} (hpt : Nonsingular x y) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hpm : p ∣ addOrderOf P) (htor : IsOfFinAddOrder P) (hsf : Squarefree (p : R)) : IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`
- What: If a finite-order point has an odd prime `p` (squarefree in `R`) dividing its order, its coordinates are `R`-integral.
- How: Sets `k = addOrderOf P / p`, forms `Q = k • P` which has exact order `p` (nonzero by an order-minimality `calc`, killed by `p`); writes `Q = .some hns'` via `exists_some_of_ne_zero`; applies the imported `prime_order_integrality_squarefree` to get integral coordinates of `Q`, then lifts back to `P` via `isInteger_of_nsmul_isInteger`.
- Hypotheses: nonsingular point; `p` prime, odd, dividing the (finite) additive order; `p` squarefree in `R`.
- Uses from project: [`nsmul_eq_zero_affine_to_jac`, `exists_some_of_ne_zero`, `prime_order_integrality_squarefree`, `isInteger_of_nsmul_isInteger`]
- Used by: `lutz_nagell_integrality_pid`
- Visibility: private
- Lines: 79–102 (proof ~20 lines)
- Notes: none

### lemma integrality_of_four_dvd_order
- Type: `{x y : K} (hpt : Nonsingular x y) (h4 : 4 ∣ addOrderOf P) (htor : IsOfFinAddOrder P) (hsf2 : Squarefree (2 : R)) : IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y`
- What: If `4` divides the order of a finite-order point and `2` is squarefree in `R`, the coordinates are `R`-integral (handles the 2-primary torsion case).
- How: Sets `k = addOrderOf P / 4`, forms `Q = k • P` of order exactly 4 (`4•Q=0` but `2•Q≠0`, both via order-minimality/`omega`); writes `Q = .some hns'`; applies imported `integrality_of_order_four_squarefree`, then lifts to `P` via `isInteger_of_nsmul_isInteger`.
- Hypotheses: nonsingular point; `4 ∣ order`; finite order; `2` squarefree in `R`.
- Uses from project: [`nsmul_eq_zero_affine_to_jac`, `exists_some_of_ne_zero`, `integrality_of_order_four_squarefree`, `isInteger_of_nsmul_isInteger`]
- Used by: `lutz_nagell_integrality_pid`
- Visibility: private
- Lines: 106–130 (proof ~20 lines)
- Notes: none

### theorem lutz_nagell_integrality_pid
- Type: `{x y : K} (hpt : Nonsingular x y) (htor : IsOfFinAddOrder P) (hsf_all : ∀ p, p.Prime → p ∣ addOrderOf P → Squarefree (p : R)) : (IsInteger R x ∧ IsInteger R y) ∨ (addOrderOf P = 2 ∧ (den R x : R) ∣ 4)`
- What: Generalized Lutz–Nagell integrality over a char-0 PID: a nonzero finite-order point with all order-prime-divisors squarefree in `R` has integral coordinates, except possibly order-2 points whose `x`-denominator divides 4.
- How: Case-splits on `addOrderOf P = 2` (uses imported `den_dvd_of_order_two`); otherwise either an odd prime divides the order (→ `integrality_of_odd_prime_factor`) or the order is a pure power of 2, in which case `4 ∣ order` (derived with `Nat.exists_prime_and_dvd` + `omega`) feeding `integrality_of_four_dvd_order`.
- Hypotheses: nonsingular point; finite additive order; every prime dividing the order is squarefree in `R`.
- Uses from project: [`nsmul_eq_zero_affine_to_jac`, `den_dvd_of_order_two`, `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`]
- Used by: `kappa_sq_dvd_four_Psi3_of_torsion`, `NumberField.lutz_nagell_number_field`
- Visibility: public
- Lines: 141–174 (proof ~26 lines)
- Notes: none

### lemma kappa_sq_eq_Psi2Sq
- Type: `{x₀ y₀ : R} (hcurve : <Weierstrass equation over R>) : (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2 = 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆`
- What: Identifies `κ₀² = (2y₀+a₁x₀+a₃)²` with the evaluation of the doubling polynomial `Ψ₂Sq` at `x₀` for an on-curve integral point.
- How: Unfolds `b₂,b₄,b₆` and closes with `linear_combination 4 * hcurve`.
- Hypotheses: `(x₀,y₀)` satisfies the affine Weierstrass equation over `R`.
- Uses from project: []
- Used by: `lutz_nagell_pid_discriminant`, `lutz_nagell_pid_discriminant_of_torsion`, `lutz_nagell_cubicDisc_discriminant`
- Visibility: private
- Lines: 178–185 (proof 2 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`

### lemma bezout_identity
- Type: `(x₀ : R) : (<quartic c₁>) * (4x₀³+b₂x₀²+2b₄x₀+b₆) + (<quadratic c₂>) * (6x₀²+b₂x₀+b₄)² = 4 * W.Δ`
- What: An explicit Bézout/polynomial identity expressing `4Δ` as a combination of `Ψ₂Sq(x₀)` and the square of `h(x₀)=6x₀²+b₂x₀+b₄`, with polynomial cofactors in `x₀`.
- How: Unfolds `b₂,b₄,b₆,b₈,Δ` and closes by `ring`.
- Hypotheses: none (pure polynomial identity in `x₀` over `R`).
- Uses from project: []
- Used by: `kappa_sq_dvd_four_delta`
- Visibility: private
- Lines: 187–195 (proof 2 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`

### lemma kappa_sq_dvd_four_delta
- Type: `(x₀ κ₀ : R) (hkappa : κ₀ ^ 2 = 4x₀³+b₂x₀²+2b₄x₀+b₆) (hdvd_Psi3 : κ₀ ^ 2 ∣ 4 * Ψ₃(x₀)) : κ₀ ^ 2 ∣ 4 * W.Δ`
- What: From `κ₀² = Ψ₂Sq(x₀)` and `κ₀² ∣ 4Ψ₃(x₀)`, deduces `κ₀² ∣ 4Δ`.
- How: First shows `κ₀² ∣ h(x₀)²` via an algebraic identity `h² + 4Ψ₃ = (12x₀+b₂)·Ψ₂Sq` (proved by unfolding `b`'s + `ring`, then `dvd_sub`); then rewrites `4Δ` through `bezout_identity` and concludes with `dvd_add`/`dvd_mul_of_dvd_right`, using `κ₀² ∣ Ψ₂Sq(x₀)` from `hkappa`.
- Hypotheses: `κ₀² = Ψ₂Sq(x₀)`; `κ₀² ∣ 4·Ψ₃(x₀)`.
- Uses from project: [`bezout_identity`]
- Used by: `lutz_nagell_pid_discriminant`, `lutz_nagell_pid_discriminant_of_torsion`
- Visibility: private
- Lines: 197–218 (proof ~17 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`

### theorem lutz_nagell_pid_discriminant
- Type: `{x₀ y₀ : R} (hcurve : <Weierstrass eqn over R>) (hdvd_Psi3 : κ₀² ∣ 4·Ψ₃(x₀)) : κ₀ = 0 ∨ κ₀² ∣ 4 * W.Δ` where `κ₀ = 2y₀+a₁x₀+a₃`
- What: Lutz–Nagell discriminant divisibility over a PID: assuming the `Ψ₃` divisibility, an integral on-curve point has `κ₀ = 0` or `κ₀² ∣ 4Δ`.
- How: Case-splits on `κ₀ = 0`; the nonzero branch applies `kappa_sq_dvd_four_delta` with `kappa_sq_eq_Psi2Sq` supplying `κ₀² = Ψ₂Sq(x₀)`.
- Hypotheses: integral on-curve point; `κ₀² ∣ 4·Ψ₃(x₀)`.
- Uses from project: [`kappa_sq_dvd_four_delta`, `kappa_sq_eq_Psi2Sq`]
- Used by: unused in file
- Visibility: public
- Lines: 220–237 (proof 2 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`

### theorem kappa_sq_dvd_four_Psi3_of_integral
- Type: `{x₀ κ₀ c : R} (hPsi3 : Ψ₃(x₀) = κ₀ ^ 2 * c) : κ₀ ^ 2 ∣ 4 * Ψ₃(x₀)`
- What: Helper converting a factorization `Ψ₃(x₀) = κ₀²·c` into the divisibility `κ₀² ∣ 4·Ψ₃(x₀)`.
- How: Directly `dvd_mul_of_dvd_right ⟨c, hPsi3⟩ 4`.
- Hypotheses: `Ψ₃(x₀)` factors as `κ₀²·c`.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 239–246 (proof 1 line)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R]`

### lemma curveR_equation_of_isInteger
- Type: `{x y : K} (hpt : Nonsingular x y) {x₀ y₀ : R} (hx : algebraMap R K x₀ = x) (hy : algebraMap R K y₀ = y) : <Weierstrass equation over R for x₀,y₀>`
- What: If a nonsingular point over `K` has coordinates that are images of `x₀,y₀ ∈ R`, then `(x₀,y₀)` satisfies the Weierstrass equation over `R`.
- How: Takes the `K`-equation from imported `curveK_equation_iff`, substitutes `hx,hy`, matches both sides under `algebraMap` (via `linear_combination`), then cancels the injective `algebraMap` with `IsFractionRing.injective`.
- Hypotheses: nonsingular point; `x = algebraMap x₀`, `y = algebraMap y₀`.
- Uses from project: [`curveK_equation_iff`] (imported)
- Used by: `lutz_nagell_pid_discriminant_of_torsion`
- Visibility: private
- Lines: 250–261 (proof ~7 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K]`

### lemma addOrderOf_ne_two_of_kappa_ne_zero
- Type: `{x y : K} (hns : Nonsingular x y) {x₀ y₀ : R} (hx : ...= x) (hy : ...= y) (hκ : 2*y₀+a₁x₀+a₃ ≠ 0) : addOrderOf (Affine.Point.some _ _ hns) ≠ 2`
- What: If `κ₀ = 2y₀+a₁x₀+a₃ ≠ 0` for an integral point, then the point does not have additive order exactly 2.
- How: Assuming order 2 gives `2•P = 0`, transports to Jacobian (`nsmul_eq_zero_affine_to_jac`) and feeds imported `evalEval_ψ_eq_zero_of_zsmul_eq_zero` to force `ψ₂` to vanish; unfolding `ψ_two`/`ψ₂`/`evalEval_polynomialY` and the `curveK` coefficient simp lemmas yields `κ₀ = 0` (over `K`, descended by injectivity), contradicting `hκ`.
- Hypotheses: nonsingular point with integral coordinate images; `κ₀ ≠ 0` in `R`.
- Uses from project: [`nsmul_eq_zero_affine_to_jac`, `evalEval_ψ_eq_zero_of_zsmul_eq_zero`, `curveK_a₁`, `curveK_a₃`] (latter three imported)
- Used by: `kappa_sq_dvd_four_Psi3_of_torsion`
- Visibility: private
- Lines: 263–281 (proof ~17 lines)
- Notes: `omit [CharZero R]`

### lemma Phi2_eval_eq
- Type: `(x : K) : eval x ((curveK R K W).Φ 2) = x * eval x (curveK R K W).Ψ₂Sq - eval x (curveK R K W).Ψ₃`
- What: Evaluation formula for the doubling numerator polynomial `Φ 2` at `x`: `x·Ψ₂Sq(x) − Ψ₃(x)`.
- How: Rewrites `Φ 2 = X·Ψ₂Sq − Ψ₃` (from `WeierstrassCurve.Φ`, `ΨSq_two`, `preΨ_three`, `preΨ_one`), then `eval_sub`/`eval_mul`/`eval_X`.
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3_of_torsion`
- Visibility: private
- Lines: 285–293 (proof ~5 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K]`

### lemma PsiSq_two_eval_eq
- Type: `(x : K) : eval x ((curveK R K W).ΨSq 2) = eval x (curveK R K W).Ψ₂Sq`
- What: The polynomial `ΨSq 2` evaluates to the same as `Ψ₂Sq` at any `x`.
- How: Rewrites by `WeierstrassCurve.ΨSq_two`.
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3_of_torsion`
- Visibility: private
- Lines: 295–298 (proof 1 line)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K]`

### lemma Psi2Sq_eval_eq
- Type: `(x : K) : eval x (curveK R K W).Ψ₂Sq = 4*x³ + algebraMap R K W.b₂ * x² + 2*algebraMap R K W.b₄ * x + algebraMap R K W.b₆`
- What: Explicit polynomial-evaluation formula for `Ψ₂Sq` of the base-changed curve over `K`.
- How: Shows `(curveK).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap R K)` via `map_Ψ₂Sq`, then `eval_map` + unfolding `Ψ₂Sq` and simp with the `eval₂_*` lemmas.
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3_of_torsion`
- Visibility: private
- Lines: 300–309 (proof ~6 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K]`

### lemma Psi3_eval_eq
- Type: `(x : K) : eval x (curveK R K W).Ψ₃ = 3*x⁴ + algebraMap R K W.b₂ * x³ + 3*algebraMap R K W.b₄ * x² + 3*algebraMap R K W.b₆ * x + algebraMap R K W.b₈`
- What: Explicit polynomial-evaluation formula for `Ψ₃` of the base-changed curve over `K`.
- How: Shows `(curveK).Ψ₃ = W.Ψ₃.map (algebraMap R K)` via `map_Ψ₃`, then `eval_map` + unfolding `Ψ₃` and simp with `eval₂_*` lemmas.
- Hypotheses: none.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3_of_torsion`
- Visibility: private
- Lines: 311–320 (proof ~6 lines)
- Notes: `omit [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [DecidableEq K] [IsFractionRing R K]`

### lemma isInteger_mul_of_den_dvd
- Type: `{x : K} {n : R} (h : (IsFractionRing.den R x : R) ∣ n) : IsLocalization.IsInteger R (algebraMap R K n * x)`
- What: If the denominator of `x` divides `n ∈ R`, then `n·x` is an `R`-integer (clearing the denominator).
- How: Writes `n = den·q`, proposes witness `q · num R x`; uses `IsFractionRing.mk'_num_den'` (rearranged by `div_eq_iff`) to replace `den·x` by `num`, then a `calc` with `map_mul`/`ring`.
- Hypotheses: `den R x ∣ n`.
- Uses from project: []
- Used by: `kappa_sq_dvd_four_Psi3_of_torsion`
- Visibility: private
- Lines: 322–337 (proof ~14 lines)
- Notes: `omit [DecidableEq K]`

### lemma kappa_sq_dvd_four_Psi3_of_torsion
- Type: `{x y : K} (hpt : Nonsingular x y) (htor : IsOfFinAddOrder P) (hsf_all : ∀ p, ...→ Squarefree (p:R)) {x₀ y₀ : R} (hx ...) (hy ...) (hkappa_sq : κ₀² = Ψ₂Sq(x₀)) (hκ : κ₀ ≠ 0) : κ₀² ∣ 4 * Ψ₃(x₀)`
- What: Derives the key `Ψ₃` divisibility `κ₀² ∣ 4·Ψ₃(x₀)` from the torsion hypothesis, using the `x`-coordinate doubling formula for `2•P`.
- How: Since `κ₀≠0`, order ≠ 2 (`addOrderOf_ne_two_of_kappa_ne_zero`), so order > 2 and `2•P ≠ 0`; writes `2•P = .some hns'` and notes its order divides that of `P` (so `hsf_all` transfers). Uses imported `x_coord_nsmul_eq` (the doubling `x`-coordinate identity) rewritten through `PsiSq_two_eval_eq`/`Phi2_eval_eq` to get `Ψ₃(x) = (x−x')·κ₀²` over `K`; then applies `lutz_nagell_integrality_pid` to `2•P`. In the integral branch `x' = image of x'₀`, giving `κ₀² ∣ Ψ₃` directly (descended by `IsFractionRing.injective`); in the order-2/`den ∣ 4` branch, clears the denominator via `isInteger_mul_of_den_dvd` (`4x'` integral) and proves `κ₀² ∣ 4·Ψ₃` by `linear_combination`.
- Hypotheses: nonsingular point; finite order; all order-primes squarefree in `R`; integral coordinate images; `κ₀² = Ψ₂Sq(x₀)`; `κ₀ ≠ 0`.
- Uses from project: [`addOrderOf_ne_two_of_kappa_ne_zero`, `exists_some_of_ne_zero`, `x_coord_nsmul_eq`, `PsiSq_two_eval_eq`, `Phi2_eval_eq`, `Psi2Sq_eval_eq`, `Psi3_eval_eq`, `lutz_nagell_integrality_pid`, `isInteger_mul_of_den_dvd`] (`x_coord_nsmul_eq` imported)
- Used by: `lutz_nagell_pid_discriminant_of_torsion`, `lutz_nagell_cubicDisc_discriminant`
- Visibility: private
- Lines: 341–389 (proof ~37 lines)
- Notes: long(30-50)

### theorem lutz_nagell_pid_discriminant_of_torsion
- Type: `{x y : K} (hpt : Nonsingular x y) (htor : IsOfFinAddOrder P) (hsf_all : ...) {x₀ y₀ : R} (hx ...) (hy ...) : κ₀ = 0 ∨ κ₀² ∣ 4 * W.Δ`
- What: Lutz–Nagell discriminant divisibility from torsion over a PID: a nonzero torsion point with integral coordinates has `κ₀ = 0` or `κ₀² ∣ 4Δ`, deriving the `Ψ₃` divisibility automatically.
- How: Case-splits on `κ₀ = 0`; otherwise combines `curveR_equation_of_isInteger`, `kappa_sq_eq_Psi2Sq`, and `kappa_sq_dvd_four_Psi3_of_torsion` to supply the hypotheses of `kappa_sq_dvd_four_delta`.
- Hypotheses: nonsingular point; finite order; all order-primes squarefree in `R`; integral coordinate images.
- Uses from project: [`curveR_equation_of_isInteger`, `kappa_sq_dvd_four_delta`, `kappa_sq_eq_Psi2Sq`, `kappa_sq_dvd_four_Psi3_of_torsion`]
- Used by: `lutz_nagell_cubicDisc_discriminant`, `NumberField.lutz_nagell_number_field_discriminant`
- Visibility: public
- Lines: 400–415 (proof ~8 lines)
- Notes: none

### theorem lutz_nagell_cubicDisc_discriminant
- Type: `(ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x y : K} (hpt : Nonsingular x y) (htor : ...) (hsf_all : ...) {x₀ y₀ : R} (hx ...) (hy ...) (hcurve : y₀² = x₀³+a₂x₀²+a₄x₀+a₆) : y₀ = 0 ∨ y₀² ∣ 4a₄³+27a₆²+4a₂³a₆−a₂²a₄²−18a₂a₄a₆`
- What: For a curve with `a₁=a₃=0` (i.e. `y²=x³+a₂x²+a₄x+a₆`), an integral torsion point satisfies `y₀=0` or `y₀²` divides the cubic discriminant (recovers `y₀² ∣ 4a₄³+27a₆²` when `a₂=0`).
- How: From `lutz_nagell_pid_discriminant_of_torsion`, the `κ₀=0` branch forces `y₀=0` (cancel 2). In the nonzero branch: re-derives `κ₀≠0`, runs `kappa_sq_dvd_four_Psi3_of_torsion` to get `(2y₀)² ∣ 4Ψ₃`, cancels the `4` to `y₀² ∣ Ψ₃(x₀)`; an algebraic identity gives `y₀² ∣ (f'(x₀))²` (with `f' = 3x₀²+2a₂x₀+a₄`); a final explicit Bézout rewrite (proved by `ring` after substituting `hcurve`) expresses the cubic discriminant as `c₁·y₀² + c₂·(f')²`, closed by `dvd_add`.
- Hypotheses: `a₁=a₃=0`; nonsingular point; finite order; order-primes squarefree; integral coordinate images; the simplified curve equation for `(x₀,y₀)`.
- Uses from project: [`lutz_nagell_pid_discriminant_of_torsion`, `kappa_sq_eq_Psi2Sq`, `kappa_sq_dvd_four_Psi3_of_torsion`]
- Used by: `NumberField.lutz_nagell_number_field_cubicDisc_discriminant`
- Visibility: public
- Lines: 423–475 (proof ~43 lines)
- Notes: long(30-50)

### theorem NumberField.lutz_nagell_number_field
- Type: `(K) [Field K] [NumberField K] [DecidableEq K] [IsPrincipalIdealRing (𝓞 K)] (W : WeierstrassCurve (𝓞 K)) {x y : K} (hpt : (W.map (algebraMap (𝓞 K) K)).toAffine.Nonsingular x y) (htor ...) (hsf_all : ∀ p, ...→ Squarefree (p : 𝓞 K)) : (IsInteger (𝓞 K) x ∧ IsInteger (𝓞 K) y) ∨ (addOrderOf P = 2 ∧ den (𝓞 K) x ∣ 4)`
- What: Lutz–Nagell integrality for a number field of class number 1: a nonzero torsion point with all order-primes squarefree in `𝓞 K` has integral coordinates (or order 2 with `den(x) ∣ 4`).
- How: Direct application of `PID.lutz_nagell_integrality_pid` with `R = 𝓞 K`.
- Hypotheses: `K` number field, `𝓞 K` a PID; nonsingular point; finite order; order-primes squarefree in `𝓞 K`.
- Uses from project: [`PID.lutz_nagell_integrality_pid`]
- Used by: unused in file
- Visibility: public
- Lines: 499–511 (proof 1 line)
- Notes: none

### theorem NumberField.den_powerful_number_field
- Type: `(K) [Field K] [NumberField K] [DecidableEq K] [IsPrincipalIdealRing (𝓞 K)] (W : WeierstrassCurve (𝓞 K)) {x y : K} (heq : <Weierstrass eqn over K>) {q : 𝓞 K} (hq : Prime q) (hqd : q ∣ den (𝓞 K) x) : q ^ 2 ∣ den (𝓞 K) x`
- What: Powerful-denominator theorem for class-number-1 number fields: every prime factor of `den(x)` in `𝓞 K` divides it at least twice (denominators supported only at ramified primes).
- How: Direct application of `PID.den_powerful_of_on_curve` with `R = 𝓞 K`.
- Hypotheses: `𝓞 K` a PID; `(x,y)` on the curve over `K`; `q` prime dividing `den(x)`.
- Uses from project: [`PID.den_powerful_of_on_curve`]
- Used by: unused in file
- Visibility: public
- Lines: 519–529 (proof 1 line)
- Notes: none

### theorem NumberField.lutz_nagell_number_field_discriminant
- Type: `(K) [...] [IsPrincipalIdealRing (𝓞 K)] (W : WeierstrassCurve (𝓞 K)) {x y : K} (hpt ...) (htor ...) (hsf_all ...) {x₀ y₀ : 𝓞 K} (hx ...) (hy ...) : κ₀ = 0 ∨ κ₀² ∣ 4 * W.Δ`
- What: Lutz–Nagell discriminant divisibility for class-number-1 number fields: an integral torsion point has `κ₀ = 2y₀+a₁x₀+a₃ = 0` or `κ₀² ∣ 4Δ`.
- How: Direct application of `PID.lutz_nagell_pid_discriminant_of_torsion` with `R = 𝓞 K`.
- Hypotheses: `𝓞 K` a PID; nonsingular torsion point with integral coordinate images; order-primes squarefree in `𝓞 K`.
- Uses from project: [`PID.lutz_nagell_pid_discriminant_of_torsion`]
- Used by: unused in file
- Visibility: public
- Lines: 535–548 (proof 1 line)
- Notes: none

### theorem NumberField.lutz_nagell_number_field_cubicDisc_discriminant
- Type: `(K) [...] [IsPrincipalIdealRing (𝓞 K)] (W : WeierstrassCurve (𝓞 K)) (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) {x y : K} (hpt ...) (htor ...) (hsf_all ...) {x₀ y₀ : 𝓞 K} (hx ...) (hy ...) (hcurve : y₀² = x₀³+a₂x₀²+a₄x₀+a₆) : y₀ = 0 ∨ y₀² ∣ 4a₄³+27a₆²+4a₂³a₆−a₂²a₄²−18a₂a₄a₆`
- What: Short/`a₁=a₃=0` Lutz–Nagell discriminant divisibility for class-number-1 number fields: an integral torsion point has `y₀ = 0` or `y₀²` divides the cubic discriminant.
- How: Direct application of `PID.lutz_nagell_cubicDisc_discriminant` with `R = 𝓞 K`.
- Hypotheses: `𝓞 K` a PID; `a₁=a₃=0`; nonsingular torsion point with integral coordinate images; order-primes squarefree; simplified curve equation.
- Uses from project: [`PID.lutz_nagell_cubicDisc_discriminant`]
- Used by: unused in file
- Visibility: public
- Lines: 556–571 (proof 1 line)
- Notes: none

---

## File Summary

- **Total declarations: 22** — defs: 0 / lemmas+theorems: 22 / instances: 0.
  (Breakdown by `lemma`/`theorem` keyword: 13 `lemma`, 9 `theorem`. Private: 10; public: 12. No defs, instances, structures, classes, abbrevs, or inductives.)

- **Key API (used by ≥3 in-file):**
  - `nsmul_eq_zero_affine_to_jac` — used by 4 (`integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, `lutz_nagell_integrality_pid`, `addOrderOf_ne_two_of_kappa_ne_zero`).
  - `exists_some_of_ne_zero` — used by 3 (`integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, `kappa_sq_dvd_four_Psi3_of_torsion`).
  - `kappa_sq_eq_Psi2Sq` — used by 3 (`lutz_nagell_pid_discriminant`, `lutz_nagell_pid_discriminant_of_torsion`, `lutz_nagell_cubicDisc_discriminant`).

- **Unused decls (no in-file consumer):** `den_powerful_of_on_curve`, `lutz_nagell_pid_discriminant`, `kappa_sq_dvd_four_Psi3_of_integral`, and all four `NumberField.*` theorems (`lutz_nagell_number_field`, `den_powerful_number_field`, `lutz_nagell_number_field_discriminant`, `lutz_nagell_number_field_cubicDisc_discriminant`). These are the file's public entry points / re-exports (consumed downstream, not in-file).

- **Decls with `sorry`:** none.

- **Decls with `set_option`:** none.

- **Proofs >50 lines (OVER-50):** none (count: 0).

- **Proofs 30–50 lines (long):** 2 —
  - `kappa_sq_dvd_four_Psi3_of_torsion` (~37 lines, 341–389).
  - `lutz_nagell_cubicDisc_discriminant` (~43 lines, 423–475).
