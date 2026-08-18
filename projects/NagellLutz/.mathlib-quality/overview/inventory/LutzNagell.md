# Inventory: LutzNagell.lean (root aggregator)

`LutzNagell.lean` itself is a **4-line import aggregator** with **zero own declarations**:

```lean
import LutzNagell.Basic
import LutzNagell.LutzNagellTheorem.Main
import LutzNagell.LutzNagellTheorem.GeneralMain
import LutzNagell.LutzNagellTheorem.GeneralDiscriminant
```

Below are the declarations of the modules this root directly stitches together: `Basic.lean`,
`LutzNagellTheorem/Main.lean`, `LutzNagellTheorem/GeneralMain.lean`,
`LutzNagellTheorem/GeneralDiscriminant.lean`. (Their own transitive imports — `ShortWeierstrass`,
`GeneralCurve`, `GeneralPrimeOrder`, `GeneralIntegralMultiple`, etc. — are separate inventory files.)
Names below are written unqualified but live in `namespace LutzNagell.LutzNagellTheorem` unless noted.

---

## Module: LutzNagell/Basic.lean

### def hello
- Type: `def hello := "world"`
- What: Placeholder string definition (Lean project template stub), value `"world"`.
- How: Trivial literal; no proof.
- Hypotheses: none.
- Uses from project: []
- Used by: unused in file
- Visibility: public
- Lines: 1 (proof length 0)
- Notes: none (template placeholder; no namespace)

---

## Module: LutzNagell/LutzNagellTheorem/Main.lean

### theorem lutz_nagell_integrality
- Type: `(A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y`
- What: Lutz–Nagell part 1 — a nonzero torsion point on the short Weierstrass curve `y² = x³ + Ax + B` over ℚ (nonzero discriminant) has integer coordinates.
- How: One-line delegation; directly `exact lutz_nagell_integrality_short A B hpt htor`.
- Hypotheses: A,B integers; discriminant of the integral short curve nonzero; (x,y) a nonsingular affine point; that point has finite additive order.
- Uses from project: [lutz_nagell_integrality_short]
- Used by: lutz_nagell
- Visibility: public
- Lines: 35–39 (proof length 1)
- Notes: none

### theorem lutz_nagell_discriminant
- Type: `(A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) {x₀ y₀ : ℤ} (hx : (x₀ : ℚ) = x) (hy : (y₀ : ℚ) = y) : y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurveZ A B).Δ`
- What: Lutz–Nagell part 2 — for an integral nonzero torsion point on `y² = x³ + Ax + B`, either `y₀ = 0` or `y₀² ∣ Δ`.
- How: Specializes the general discriminant theorem with `κ₀ = 2y₀` (since `a₁ = a₃ = 0`); rewrites `(2y₀)² = 4y₀²` and cancels the factor 4 via `mul_dvd_mul_iff_left` to pass from `4y₀² ∣ 4Δ` to `y₀² ∣ Δ`; the κ₀=0 branch gives `y₀=0` by `omega`.
- Hypotheses: integral short curve with nonzero discriminant; nonsingular affine point of finite order; `x₀,y₀` integers casting to `x,y`.
- Uses from project: [lutz_nagell_discriminant_general, shortCurveZ_a₁, shortCurveZ_a₃]
- Used by: lutz_nagell
- Visibility: public
- Lines: 48–59 (proof length 7)
- Notes: none

### theorem lutz_nagell
- Type: `(A B : ℤ) (hΔ : (shortCurveZ A B).Δ ≠ 0) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) : ∃ (x₀ y₀ : ℤ), (x₀ : ℚ) = x ∧ (y₀ : ℚ) = y ∧ (y₀ = 0 ∨ y₀ ^ 2 ∣ (shortCurveZ A B).Δ)`
- What: The full Lutz–Nagell theorem (Thm 1.1) — a nonidentity finite-order rational point on `y² = x³ + Ax + B` has integer coordinates `x₀,y₀` with `y₀ = 0` or `y₀² ∣ Δ`.
- How: Combines the two parts: obtains integrality witnesses from `lutz_nagell_integrality`, then packages them with the divisibility conclusion from `lutz_nagell_discriminant`.
- Hypotheses: integral short curve with nonzero discriminant; nonsingular affine point of finite additive order.
- Uses from project: [lutz_nagell_integrality, lutz_nagell_discriminant]
- Used by: unused in file (headline result)
- Visibility: public
- Lines: 66–72 (proof length 2)
- Notes: none

---

## Module: LutzNagell/LutzNagellTheorem/GeneralMain.lean

### lemma nsmul_eq_zero_affine_to_jac
- Type: `(W : WeierstrassCurve ℤ) {x y : ℚ} {hns : (curveQ W).toAffine.Nonsingular x y} {n : ℕ} (h : n • (Affine.Point.some _ _ hns) = 0) : (n : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0`
- What: Transports `n • P = 0` from the affine point group to `(n:ℤ) • (Jacobian image of P) = 0`.
- How: Rewrites `natCast_zsmul`, then applies the inverse of the affine↔Jacobian additive equivalence `Jacobian.Point.toAffineAddEquiv` to the hypothesis, using `map_nsmul`/`map_zero`.
- Hypotheses: W integral Weierstrass curve; nonsingular affine point P; `n • P = 0` in ℕ-scalar form.
- Uses from project: [curveQ]
- Used by: integrality_of_odd_prime_factor, integrality_of_four_dvd_order, lutz_nagell_integrality_general, lutz_nagell_integrality_short, addOrderOf_ne_two_of_kappa_ne_zero (in GeneralDiscriminant)
- Visibility: public
- Lines: 28–35 (proof length 4)
- Notes: none

### lemma exists_some_of_ne_zero
- Type: `(W : WeierstrassCurve ℤ) {Q : Affine.Point ((curveQ W).toAffine)} (hQ : Q ≠ 0) : ∃ x y, ∃ hns : (curveQ W).toAffine.Nonsingular x y, Q = .some _ _ hns`
- What: A nonzero affine point is necessarily of constructor form `.some hns` (it is not the point at infinity).
- How: Case-splits the `Affine.Point` inductive; the zero/infinity case contradicts `hQ` via `absurd rfl hQ`, the `.some` case is `rfl`.
- Hypotheses: W integral curve; affine point Q nonzero.
- Uses from project: [curveQ]
- Used by: integrality_of_odd_prime_factor, integrality_of_four_dvd_order, kappa_sq_dvd_four_Psi3 (in GeneralDiscriminant)
- Visibility: public
- Lines: 40–45 (proof length 4)
- Notes: none

### lemma integrality_of_odd_prime_factor
- Type: `(W) {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (hpm : p ∣ addOrderOf (...some hpt)) (htor : IsOfFinAddOrder (...)) : (∃ x₀ : ℤ, (x₀:ℚ)=x) ∧ ∃ y₀ : ℤ, (y₀:ℚ)=y`
- What: If the order of a finite-order point is divisible by an odd prime p, the point's coordinates are integral.
- How: Sets `k = order/p`, shows `k•P ≠ 0` (since `k < k·p = order`, via `Nat.mul_lt_mul_of_pos_left`) but `p•(k•P) = 0`; expresses `k•P = .some hns'`; lifts to Jacobian, applies `prime_order_integrality_general` to get integrality of the p-multiple's coordinates, then descends via `integral_of_nsmul_integral_general` (since gcd(k,p)-type denominators argument: a nonzero integer multiple `k•P` integral forces P integral). >10 lines: hinges on `prime_order_integrality_general` and `integral_of_nsmul_integral_general`.
- Hypotheses: nonsingular point of finite order; an odd prime p dividing its additive order.
- Uses from project: [curveQ, exists_some_of_ne_zero, nsmul_eq_zero_affine_to_jac, prime_order_integrality_general, integral_of_nsmul_integral_general]
- Used by: lutz_nagell_integrality_general
- Visibility: private
- Lines: 47–77 (proof length ~31)
- Notes: long(30-50)

### lemma integrality_of_four_dvd_order
- Type: `(W) {x y : ℚ} (hpt : ...Nonsingular x y) (h4 : 4 ∣ addOrderOf (...some hpt)) (htor : IsOfFinAddOrder (...)) : (∃ x₀ : ℤ, (x₀:ℚ)=x) ∧ ∃ y₀ : ℤ, (y₀:ℚ)=y`
- What: If 4 divides the order of a finite-order point, the coordinates are integral.
- How: Sets `k = order/4`; shows `k•P ≠ 0`, `4•(k•P) = 0`, and crucially `2•(k•P) ≠ 0` (so `k•P` has order exactly 4) via `addOrderOf_dvd_of_nsmul_eq_zero` + `omega` bounds; writes `k•P = .some hns'`, applies `integrality_of_order_four_general` for integrality of the quadruple point, then descends with `integral_of_nsmul_integral_general`. >10 lines: hinges on `integrality_of_order_four_general` and `integral_of_nsmul_integral_general`.
- Hypotheses: nonsingular point of finite order; 4 divides its additive order.
- Uses from project: [curveQ, exists_some_of_ne_zero, nsmul_eq_zero_affine_to_jac, integrality_of_order_four_general, integral_of_nsmul_integral_general]
- Used by: lutz_nagell_integrality_general
- Visibility: private
- Lines: 79–105 (proof length ~27)
- Notes: none

### theorem lutz_nagell_integrality_general
- Type: `(W) {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (...)) : ((∃ x₀:ℤ,(x₀:ℚ)=x) ∧ ∃ y₀:ℤ,(y₀:ℚ)=y) ∨ (addOrderOf (...)=2 ∧ (∃ n:ℤ,(n:ℚ)=4*x) ∧ ∃ m:ℤ,(m:ℚ)=8*y)`
- What: Generalized Lutz–Nagell integrality — a nonzero finite-order point on a general integral Weierstrass curve either has integer coordinates, or has order 2 with `4x, 8y ∈ ℤ`.
- How: Case-splits on `addOrderOf P`. If order = 2: right branch via `bounded_den_of_order_two_general`. Otherwise (order ≥ 3, since order ≠ 1 from `AddMonoid.addOrderOf_eq_one_iff`): if some odd prime divides the order, apply `integrality_of_odd_prime_factor`; else all prime factors are 2, so (using `Nat.exists_prime_and_dvd` twice) `4 ∣ order`, and apply `integrality_of_four_dvd_order`. >10 lines: hinges on `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, `bounded_den_of_order_two_general`.
- Hypotheses: W integral curve; nonsingular affine point of finite additive order.
- Uses from project: [curveQ, integrality_of_odd_prime_factor, integrality_of_four_dvd_order, bounded_den_of_order_two_general, nsmul_eq_zero_affine_to_jac]
- Used by: lutz_nagell_integrality_short, lutz_nagell_general (GeneralDiscriminant), kappa_sq_dvd_four_Psi3 (GeneralDiscriminant)
- Visibility: public
- Lines: 110–142 (proof length ~27)
- Notes: none

### theorem lutz_nagell_integrality_short
- Type: `(A B : ℤ) {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y) (htor : IsOfFinAddOrder (...)) : (∃ x₀:ℤ,(x₀:ℚ)=x) ∧ ∃ y₀:ℤ,(y₀:ℚ)=y`
- What: Short-Weierstrass integrality — a nonzero finite-order point on `y² = x³ + Ax + B` (integral A,B) has integer coordinates (the order-2 escape hatch collapses here).
- How: Applies `lutz_nagell_integrality_general` to `shortCurveZ A B`. Integral branch is immediate. In the order-2 branch: `ψ₂ = 2y` (since `a₁=a₃=0`, via `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `WeierstrassCurve.ψ_two`, `ψ₂`, `evalEval_polynomialY`) forces `y = 0`; then `x` is a root of the monic `X³ + C A·X + C B ∈ ℤ[X]` (monicity built from `monic_X_pow`/`Monic.add_of_left`/`degree_*` lemmas), so `isInteger_of_is_root_of_monic` gives `x ∈ ℤ`. >10 lines: hinges on `lutz_nagell_integrality_general`, `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, mathlib `isInteger_of_is_root_of_monic`.
- Hypotheses: A,B integers; nonsingular affine point of finite order on the short curve.
- Uses from project: [lutz_nagell_integrality_general, nsmul_eq_zero_affine_to_jac, evalEval_ψ_eq_zero_of_zsmul_eq_zero_general, shortCurveZ_a₁, shortCurveZ_a₃, curveQ_a₁, curveQ_a₃, shortCurveQ_equation_iff]
- Used by: lutz_nagell_integrality (Main)
- Visibility: public
- Lines: 153–187 (proof length ~32)
- Notes: long(30-50); uses `open Polynomial in` (two occurrences)

---

## Module: LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean

### lemma kappa_sq_eq_Psi2Sq_eval_general
- Type: `(W) {x₀ y₀ : ℤ} (hcurve : y₀^2 + W.a₁*x₀*y₀ + W.a₃*y₀ = x₀^3 + W.a₂*x₀^2 + W.a₄*x₀ + W.a₆) : (2*y₀ + W.a₁*x₀ + W.a₃)^2 = 4*x₀^3 + W.b₂*x₀^2 + 2*W.b₄*x₀ + W.b₆`
- What: The square-completed curve equation: `κ₀² = Ψ₂Sq(x₀)`, expressing `(2y₀+a₁x₀+a₃)²` via the `bᵢ` invariants.
- How: Unfolds `b₂,b₄,b₆` to `aᵢ` then `nlinarith` against the curve equation.
- Hypotheses: integer point `(x₀,y₀)` satisfies the general curve equation.
- Uses from project: []
- Used by: lutz_nagell_discriminant_general
- Visibility: private
- Lines: 34–41 (proof length 2)
- Notes: none

### lemma h_sq_add_four_prePsi3_eq_general
- Type: `(W) (x₀ : ℤ) : (6*x₀^2 + W.b₂*x₀ + W.b₄)^2 + 4*(3*x₀^4 + W.b₂*x₀^3 + 3*W.b₄*x₀^2 + 3*W.b₆*x₀ + W.b₈) = (12*x₀ + W.b₂)*(4*x₀^3 + W.b₂*x₀^2 + 2*W.b₄*x₀ + W.b₆)`
- What: Polynomial identity `h(x)² + 4·Ψ₃(x) = (12x + b₂)·Ψ₂Sq(x)` (uses `b₂b₆ − b₄² = 4b₈` after unfolding to aᵢ).
- How: Unfolds `b₂,b₄,b₆,b₈` then `ring`.
- Hypotheses: none beyond W and the integer x₀.
- Uses from project: []
- Used by: kappa_sq_dvd_four_delta_of_coord_identity
- Visibility: private
- Lines: 45–52 (proof length 2)
- Notes: none

### lemma bezout_general
- Type: `(W) (x₀ : ℤ) : (432*x₀^3 + 108*b₂*x₀^2 + 216*b₄*x₀ + (-b₂^3 + 36*b₂*b₄ - 108*b₆))·Ψ₂Sq(x₀) + (-48*x₀^2 - 8*b₂*x₀ + (b₂^2 - 32*b₄))·h(x₀)² = 4·Δ`
- What: Bézout identity `d₁·Ψ₂Sq(x) + d₂·h(x)² = 4Δ` certifying that the ideal `(Ψ₂Sq, h²)` contains `4Δ`.
- How: Unfolds `b₂,b₄,b₆,b₈,Δ` then `ring`.
- Hypotheses: none beyond W and integer x₀.
- Uses from project: []
- Used by: kappa_sq_dvd_four_delta_of_coord_identity
- Visibility: private
- Lines: 55–63 (proof length 2)
- Notes: none

### lemma kappa_sq_dvd_four_delta_of_coord_identity
- Type: `(W) (x₀ κ₀ : ℤ) (hkappa : κ₀^2 = 4*x₀^3 + b₂*x₀^2 + 2*b₄*x₀ + b₆) (hdvd_prePsi : κ₀^2 ∣ 4*(3*x₀^4 + b₂*x₀^3 + 3*b₄*x₀^2 + 3*b₆*x₀ + b₈)) : κ₀^2 ∣ 4*W.Δ`
- What: Pure-algebra step: from `κ₀² = Ψ₂Sq(x₀)` and `κ₀² ∣ 4·Ψ₃(x₀)`, deduce `κ₀² ∣ 4Δ`.
- How: First shows `κ₀² ∣ h(x₀)²` by rewriting `h² = (12x+b₂)·Ψ₂Sq − 4·Ψ₃` (from `h_sq_add_four_prePsi3_eq_general`) and `dvd_sub`; then rewrites `4Δ` via `bezout_general` and concludes by `dvd_add`/`dvd_mul_of_dvd_right` (κ₀² divides Ψ₂Sq since κ₀²=Ψ₂Sq, and divides h²). Hinges on `h_sq_add_four_prePsi3_eq_general`, `bezout_general`.
- Hypotheses: κ₀² equals Ψ₂Sq(x₀); κ₀² divides `4·Ψ₃(x₀)`.
- Uses from project: [h_sq_add_four_prePsi3_eq_general, bezout_general]
- Used by: lutz_nagell_discriminant_general
- Visibility: private
- Lines: 68–83 (proof length ~16)
- Notes: none

### lemma curveZ_equation_of_integral
- Type: `(W) {x y : ℚ} (hpt : (curveQ W).toAffine.Nonsingular x y) {x₀ y₀ : ℤ} (hx : (x₀:ℚ)=x) (hy : (y₀:ℚ)=y) : y₀^2 + W.a₁*x₀*y₀ + W.a₃*y₀ = x₀^3 + W.a₂*x₀^2 + W.a₄*x₀ + W.a₆`
- What: Derives the integer curve equation from a nonsingular rational point whose coordinates happen to be integers.
- How: Proves the equation over ℚ from `curveQ_equation_iff` (substituting the integer casts) via `linarith`, then `exact_mod_cast` back to ℤ.
- Hypotheses: nonsingular point; integers `x₀,y₀` cast to `x,y`.
- Uses from project: [curveQ, curveQ_equation_iff]
- Used by: lutz_nagell_discriminant_general
- Visibility: private
- Lines: 88–96 (proof length ~9)
- Notes: none

### lemma addOrderOf_ne_two_of_kappa_ne_zero
- Type: `(W) {x y : ℚ} (hns : (curveQ W).toAffine.Nonsingular x y) {x₀ y₀ : ℤ} (hx : (x₀:ℚ)=x) (hy : (y₀:ℚ)=y) (hκ : 2*y₀ + W.a₁*x₀ + W.a₃ ≠ 0) : addOrderOf (Affine.Point.some _ _ hns) ≠ 2`
- What: If `κ₀ ≠ 0`, the point cannot have order 2 (κ₀ is exactly `ψ₂` at the point, which vanishes on 2-torsion).
- How: By contradiction: order 2 ⇒ `2•P = 0` ⇒ (via Jacobian transport and `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `ψ_two`, `ψ₂`, `evalEval_polynomialY`) `2y + a₁x + a₃ = 0` over ℚ, contradicting `hκ` after `exact_mod_cast`. Hinges on `evalEval_ψ_eq_zero_of_zsmul_eq_zero_general`, `nsmul_eq_zero_affine_to_jac`.
- Hypotheses: nonsingular point; integer coords; `κ₀ ≠ 0`.
- Uses from project: [curveQ, nsmul_eq_zero_affine_to_jac, evalEval_ψ_eq_zero_of_zsmul_eq_zero_general, curveQ_a₁, curveQ_a₃]
- Used by: kappa_sq_dvd_four_Psi3
- Visibility: private
- Lines: 99–115 (proof length ~17)
- Notes: none

### lemma Phi2_eval_eq
- Type: `(W) (x : ℚ) : eval x ((curveQ W).Φ 2) = x * eval x (curveQ W).Ψ₂Sq - eval x (curveQ W).Ψ₃`
- What: Coordinate-formula evaluation `Φ₂(x) = x·Ψ₂Sq(x) − Ψ₃(x)`.
- How: Rewrites `Φ 2 = X·Ψ₂Sq − Ψ₃` (via `WeierstrassCurve.Φ`, `ΨSq_two`, `preΨ_three`, `preΨ_one`, `even_two`) then distributes `eval_sub`/`eval_mul`/`eval_X`.
- Hypotheses: none beyond W and x.
- Uses from project: [curveQ]
- Used by: kappa_sq_dvd_four_Psi3
- Visibility: private
- Lines: 121–128 (proof length ~7)
- Notes: none

### lemma PsiSq_two_eval_eq
- Type: `(W) (x : ℚ) : eval x ((curveQ W).ΨSq 2) = eval x (curveQ W).Ψ₂Sq`
- What: `ΨSq 2` evaluates to `Ψ₂Sq` at x.
- How: Single rewrite by `WeierstrassCurve.ΨSq_two`.
- Hypotheses: none.
- Uses from project: [curveQ]
- Used by: kappa_sq_dvd_four_Psi3
- Visibility: private
- Lines: 131–133 (proof length 1)
- Notes: none

### lemma Psi2Sq_eval_eq
- Type: `(W) (x : ℚ) : eval x (curveQ W).Ψ₂Sq = 4*x^3 + (W.b₂:ℚ)*x^2 + 2*(W.b₄:ℚ)*x + (W.b₆:ℚ)`
- What: Closed-form evaluation of `Ψ₂Sq` over ℚ in terms of the integer `bᵢ` invariants.
- How: Identifies `(curveQ W).Ψ₂Sq` with `W.Ψ₂Sq.map (algebraMap ℤ ℚ)` (via `WeierstrassCurve.map_Ψ₂Sq`), `eval_map`, unfolds `Ψ₂Sq`, then `eval₂_*` simp + `push_cast` + `ring`.
- Hypotheses: none.
- Uses from project: [curveQ]
- Used by: kappa_sq_dvd_four_Psi3
- Visibility: private
- Lines: 136–145 (proof length ~9)
- Notes: none

### lemma Psi3_eval_eq
- Type: `(W) (x : ℚ) : eval x (curveQ W).Ψ₃ = 3*x^4 + (W.b₂:ℚ)*x^3 + 3*(W.b₄:ℚ)*x^2 + 3*(W.b₆:ℚ)*x + (W.b₈:ℚ)`
- What: Closed-form evaluation of `Ψ₃` over ℚ in terms of integer `bᵢ`.
- How: Identifies `(curveQ W).Ψ₃` with `W.Ψ₃.map (algebraMap ℤ ℚ)` (via `WeierstrassCurve.map_Ψ₃`), `eval_map`, unfolds `Ψ₃`, then `eval₂_*` simp.
- Hypotheses: none.
- Uses from project: [curveQ]
- Used by: kappa_sq_dvd_four_Psi3
- Visibility: private
- Lines: 148–156 (proof length ~7)
- Notes: none

### lemma kappa_sq_dvd_four_Psi3
- Type: `(W) {x y : ℚ} (hpt : ...Nonsingular x y) (htor : IsOfFinAddOrder (...)) {x₀ y₀ : ℤ} (hx) (hy) {κ₀ : ℤ} (hκ₀ : κ₀ = 2*y₀ + W.a₁*x₀ + W.a₃) (hkappa_sq : κ₀^2 = 4*x₀^3 + b₂*x₀^2 + 2*b₄*x₀ + b₆) (hκ : κ₀ ≠ 0) : κ₀^2 ∣ 4*(3*x₀^4 + b₂*x₀^3 + 3*b₄*x₀^2 + 3*b₆*x₀ + b₈)`
- What: Core divisibility `κ₀² ∣ 4·Ψ₃(x₀)`, obtained from the x-coordinate doubling formula together with integrality of the doubled point.
- How: Since κ₀≠0 the order is >2 (`addOrderOf_ne_two_of_kappa_ne_zero`) and ≠1, so `2•P ≠ 0`; write `2•P = .some hns'` and use the x-coordinate doubling formula `x_coord_nsmul_eq_general` (rewritten via `PsiSq_two_eval_eq`, `Phi2_eval_eq`) to get `Ψ₃(x) = (x − x')·Ψ₂Sq(x)`. Convert to ℚ-equalities (`Psi2Sq_eval_eq`, `Psi3_eval_eq`, with `κ₀² = Ψ₂Sq(x₀)`), then case on integrality of the doubled point (`lutz_nagell_integrality_general`): integral x' gives `4·Ψ₃(x₀) = κ₀²·4(x₀−x'₀)`; order-2 / `4x'∈ℤ` branch gives `4·Ψ₃(x₀) = κ₀²·(4x₀ − n₀)`. Either way κ₀² divides. >10 lines: hinges on `x_coord_nsmul_eq_general`, `lutz_nagell_integrality_general`, `addOrderOf_ne_two_of_kappa_ne_zero`.
- Hypotheses: nonsingular point of finite order; integer coords; κ₀ defined as `2y₀+a₁x₀+a₃`; `κ₀² = Ψ₂Sq(x₀)`; `κ₀ ≠ 0`.
- Uses from project: [curveQ, addOrderOf_ne_two_of_kappa_ne_zero, exists_some_of_ne_zero, x_coord_nsmul_eq_general, PsiSq_two_eval_eq, Phi2_eval_eq, Psi2Sq_eval_eq, Psi3_eval_eq, lutz_nagell_integrality_general]
- Used by: lutz_nagell_discriminant_general
- Visibility: private
- Lines: 162–219 (proof length ~58)
- Notes: OVER-50 (needs /decompose-proof pass)

### theorem lutz_nagell_discriminant_general
- Type: `(W) {x y : ℚ} (hpt : ...Nonsingular x y) (htor : IsOfFinAddOrder (...)) {x₀ y₀ : ℤ} (hx : (x₀:ℚ)=x) (hy : (y₀:ℚ)=y) : (2*y₀ + W.a₁*x₀ + W.a₃) = 0 ∨ (2*y₀ + W.a₁*x₀ + W.a₃)^2 ∣ 4*W.Δ`
- What: General discriminant divisibility — for an integral nonzero torsion point, either `κ₀ = 0` or `κ₀² ∣ 4Δ`, with `κ₀ = 2y₀+a₁x₀+a₃`.
- How: Case on `κ₀ = 0` (left). Else combine `kappa_sq_eq_Psi2Sq_eval_general` (from `curveZ_equation_of_integral`) with `kappa_sq_dvd_four_Psi3`, fed into the pure-algebra `kappa_sq_dvd_four_delta_of_coord_identity`.
- Hypotheses: nonsingular point of finite order; integer coords.
- Uses from project: [kappa_sq_eq_Psi2Sq_eval_general, curveZ_equation_of_integral, kappa_sq_dvd_four_delta_of_coord_identity, kappa_sq_dvd_four_Psi3]
- Used by: lutz_nagell_discriminant (Main), lutz_nagell_general
- Visibility: public
- Lines: 226–239 (proof length ~9)
- Notes: none

### theorem lutz_nagell_general
- Type: `(W) {x y : ℚ} (hpt : ...Nonsingular x y) (htor : IsOfFinAddOrder (...)) : (∃ (x₀ y₀ : ℤ), (x₀:ℚ)=x ∧ (y₀:ℚ)=y ∧ (2*y₀+a₁x₀+a₃ = 0 ∨ (2*y₀+a₁x₀+a₃)^2 ∣ 4*W.Δ)) ∨ (addOrderOf (...) = 2 ∧ (∃ n:ℤ,(n:ℚ)=4*x) ∧ ∃ m:ℤ,(m:ℚ)=8*y)`
- What: Combined general Lutz–Nagell — a nonzero torsion point on a general integral Weierstrass curve either has integer coords with the κ₀ divisibility dichotomy, or has order 2 with `4x, 8y ∈ ℤ`.
- How: Case-splits `lutz_nagell_integrality_general`; integral branch packages `lutz_nagell_discriminant_general`, order-2 branch passes through directly.
- Hypotheses: W integral curve; nonsingular point of finite order.
- Uses from project: [lutz_nagell_integrality_general, lutz_nagell_discriminant_general]
- Used by: unused in file (headline general result)
- Visibility: public
- Lines: 248–260 (proof length ~5)
- Notes: none

---

## File Summary

**Scope note:** the root `LutzNagell.lean` is a 4-line import aggregator with **0 declarations of its
own**; the inventory above covers the directly-imported modules `Basic`, `Main`, `GeneralMain`,
`GeneralDiscriminant`. Transitively-imported modules (ShortWeierstrass, GeneralCurve,
GeneralPrimeOrder, GeneralIntegralMultiple, etc.) are separate inventory files.

- **Total decls documented: 19** — defs **1** (`hello`, a template stub) / lemmas+theorems **18** (9 lemmas + 9 theorems) / instances **0**. Of the math content: 8 are `private`, 10 `public`.
- **Key API (used by ≥3 in-file consumers):**
  - `nsmul_eq_zero_affine_to_jac` (GeneralMain) — used by ≥5 decls across both general modules.
  - `lutz_nagell_integrality_general` (GeneralMain) — used by `lutz_nagell_integrality_short`, `lutz_nagell_general`, `kappa_sq_dvd_four_Psi3`.
  - `exists_some_of_ne_zero` (GeneralMain) — used by `integrality_of_odd_prime_factor`, `integrality_of_four_dvd_order`, `kappa_sq_dvd_four_Psi3`.
  - `curveQ` (helper from a transitively-imported module) is pervasive but external to this set.
- **Unused decls (within this 4-module set):** `hello` (template stub); `lutz_nagell` (Main, headline export); `lutz_nagell_general` (GeneralDiscriminant, headline export). The latter two are intended public API, not dead code.
- **Decls with `sorry`: none.**
- **Decls with `set_option`: none.**
- **Proofs > 50 lines (OVER-50), count = 1:** `kappa_sq_dvd_four_Psi3` (GeneralDiscriminant, ~58 lines) — flagged for `/decompose-proof`.
- **Proofs 30–50 lines, count = 2:** `lutz_nagell_integrality_short` (Main, ~32), `integrality_of_odd_prime_factor` (GeneralMain, ~31). (`lutz_nagell_integrality_general` ~27, `integrality_of_four_dvd_order` ~27 are just under the band.)
