# Inventory: PadicLFunctions/PadicExp.lean

File realises RJW Lemma 5.14: the p-adic exponential `exp(x) = ∑ x^n/n!` and logarithm `log(1+y) = ∑(-1)^{n+1}y^n/n`, their convergence on the open ball `‖x‖ < p^{-1/(p-1)}`, isometry, functional equations, mutual inversion (via formal power series + ultrametric Fubini), and the integral versions on `pℤ_p` / `1 + pℤ_p` for odd `p`, ending with `x^s := exp(s·log x)` agreeing with `PadicInt.onePAdicPow`.

Global setup: `variable (p : ℕ) [hp : Fact p.Prime]`; `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`. Section `LogBall` rebinds `L` to a `NormSMulClass ℚ_[p] L` module (weaker than algebra). Section `Inversion` and `pZp` restore the algebra binder.

---

### instance NonarchimedeanRing L
- Type: `instance : NonarchimedeanRing L`
- What: Upgrades an ultrametric normed field to a nonarchimedean (topological) ring.
- How: Bundles `inferInstance` for the topological-ring part with `NonarchimedeanAddGroup.is_nonarchimedean` for the nonarchimedean axiom.
- Hypotheses: `L` is a normed field with ultrametric distance (the ambient `NormedField`/`IsUltrametricDist`).
- Uses from project: []
- Used by: `hasSum_pow_fin` (as `[NonarchimedeanRing R]` hypothesis is satisfied by this instance for `L`); implicitly the summability lemmas relying on nonarchimedean structure.
- Visibility: public
- Lines: 35-40 (proof 2 lines)
- Notes: none. Marked MATHLIB-PR candidate in docstring.

### theorem summable_iff_tendsto_cofinite_zero
- Type: `theorem summable_iff_tendsto_cofinite_zero {ι : Type*} (f : ι → L) : Summable f ↔ Tendsto f Filter.cofinite (𝓝 0)`
- What: E1 — in a complete ultrametric normed field, a family is summable iff it tends to 0 along the cofinite filter.
- How: Direct delegation to `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`.
- Hypotheses: `L` complete ultrametric normed field (the `NormedAlgebra` instance is omitted via `omit`).
- Uses from project: []
- Used by: `summable_padicExp_terms`, `summable_padicLog_terms`, `summable_prod_family`.
- Visibility: public
- Lines: 42-47 (proof 1 line)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L]`.

### theorem norm_factorial_le
- Type: `theorem norm_factorial_le {n : ℕ} (hn : 1 ≤ n) : (p : ℝ) ^ (-((n : ℤ) - 1)) ≤ ‖(n.factorial : ℚ_[p])‖ ^ (p - 1)`
- What: E2 — Legendre's formula `v_p(n!) ≤ (n-1)/(p-1)` stated rpow-free as `p^{-(n-1)} ≤ ‖n!‖^{p-1}`.
- How: Rewrites the p-adic norm of `n!` as a power of `p` via `Padic.norm_eq_zpow_neg_valuation` and `Padic.valuation_natCast`, then reduces to the integer inequality `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`, closing with `linarith`.
- Hypotheses: `n ≥ 1`; `p` prime.
- Uses from project: []
- Used by: `norm_factorial_inv_pow_le`.
- Visibility: public
- Lines: 49-61 (proof 9 lines)
- Notes: none.

### def InExpBall
- Type: `def InExpBall (p : ℕ) {L : Type*} [Norm L] (x : L) : Prop := ‖x‖ ^ (p - 1) < (p : ℝ)⁻¹`
- What: Membership in the open convergence ball `‖x‖ < p^{-1/(p-1)}`, stated rpow-free as `‖x‖^{p-1} < p⁻¹`; needs only a `Norm`.
- How: Definition (a real inequality on `‖x‖`).
- Hypotheses: only a `Norm L` instance.
- Uses from project: []
- Used by: `norm_factorial_inv_smul_pow_le` (no), `summable_padicExp_terms`, `norm_factorial_inv_smul_pow_sub_lt`, `norm_padicExp_sub_padicExp`, `norm_padicExp_sub_one`, `padicExp_add`, `summable_padicLog_terms`, `norm_succ_inv_smul_pow_lt`, `norm_padicLog`, `summable_prod_family`, `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul`, `inExpBall_of_mem_span`, `padicExp_converges_on_pZp`, `pZpExp_coe`, `pZpExp_sub_one_mem`, `pZpLog_coe`, `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`, `padicLog_eq_tsum_coeff`, `tsum_coeff_exp_sub_one`.
- Visibility: public
- Lines: 63-68 (def, no proof)
- Notes: none. Core predicate of the whole file (used by many).

### theorem norm_factorial_inv_pow_le
- Type: `theorem norm_factorial_inv_pow_le {n : ℕ} (hn : 1 ≤ n) : (‖(n.factorial : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1)`
- What: The inverted Legendre bound `‖n!‖^{-(p-1)} ≤ p^{n-1}` for `n ≥ 1`.
- How: Rewrites `p^{n-1}` as `(p^{-(n-1)})⁻¹` and applies `inv_anti₀` to `norm_factorial_le`.
- Hypotheses: `n ≥ 1`; `p` prime.
- Uses from project: [norm_factorial_le]
- Used by: `norm_factorial_inv_smul_pow_le`, `norm_factorial_inv_smul_pow_sub_lt`, `norm_coeff_exp_le`.
- Visibility: public
- Lines: 70-77 (proof 5 lines)
- Notes: none.

### theorem norm_factorial_inv_smul_pow_le
- Type: `theorem norm_factorial_inv_smul_pow_le (x : L) {n : ℕ} (hn : 1 ≤ n) : ‖(n.factorial : ℚ_[p])⁻¹ • x ^ n‖ ^ (p - 1) ≤ ‖x‖ ^ (p - 1) * ((p : ℝ) * ‖x‖ ^ (p - 1)) ^ (n - 1)`
- What: The exponential terms decay geometrically at the `(p-1)`-th power level.
- How: Expands the norm of the scalar product (`norm_smul`, `norm_inv`, `norm_pow`), bounds `‖n!‖^{-(p-1)}` by `norm_factorial_inv_pow_le`, then an exponent-arithmetic `calc`/`ring` rearrangement.
- Hypotheses: `n ≥ 1`; `p` prime. (`IsUltrametricDist`/`CompleteSpace` omitted.)
- Uses from project: [norm_factorial_inv_pow_le]
- Used by: `summable_padicExp_terms`.
- Visibility: public
- Lines: 79-98 (proof 13 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem summable_padicExp_terms
- Type: `theorem summable_padicExp_terms {x : L} (hx : InExpBall p x) : Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • x ^ n`
- What: On the open ball, the exponential series terms are summable.
- How: Via `summable_iff_tendsto_cofinite_zero` reduces to norm → 0; the geometric bound `norm_factorial_inv_smul_pow_le` is dominated by `tendsto_pow_atTop_nhds_zero_of_lt_one` since `p‖x‖^{p-1} < 1`; ε-N chase with `lt_of_pow_lt_pow_left₀`.
- Hypotheses: `x ∈ InExpBall p`; `p` prime; `L` complete ultrametric.
- Uses from project: [summable_iff_tendsto_cofinite_zero, InExpBall, norm_factorial_inv_smul_pow_le]
- Used by: `norm_padicExp_sub_padicExp`, `padicExp_add`, `padicExp_converges_on_pZp`, `tsum_coeff_exp_sub_one`, `padicLog_padicExp`.
- Visibility: public
- Lines: 100-128 (proof 27 lines)
- Notes: none.

### def padicExp
- Type: `noncomputable def padicExp (x : L) : L := ∑' n : ℕ, (n.factorial : ℚ_[p])⁻¹ • x ^ n`
- What: E3 — the p-adic exponential as a junk-total tsum of `∑ x^n/n!`.
- How: Definition (tsum).
- Hypotheses: ambient `L`.
- Uses from project: []
- Used by: `padicExp_zero`, `norm_padicExp_sub_padicExp`, `norm_padicExp_sub_one`, `padicExp_add`, `padicExp_eq_tsum_coeff`, `tsum_coeff_exp_sub_one`, `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul`, `pZpExp`, `pZpExp_coe`, `padicExp_smul_padicLog_eq_onePAdicPow`, and `pZpExp_sub_one_mem` (transitively).
- Visibility: public
- Lines: 130-132 (def)
- Notes: none.

### theorem padicExp_zero
- Type: `@[simp] theorem padicExp_zero : padicExp p (0 : L) = 1`
- What: `exp(0) = 1`.
- How: `tsum_eq_single 0` collapses the series using `zero_pow` for `n ≥ 1`, then `simp`.
- Hypotheses: `p` prime.
- Uses from project: [padicExp]
- Used by: `padicExp_smul_padicLog_eq_onePAdicPow` (via the `AddChar` construction).
- Visibility: public (simp)
- Lines: 134-137 (proof 2 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem norm_factorial_inv_smul_pow_sub_lt
- Type: `theorem norm_factorial_inv_smul_pow_sub_lt {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) (hxy : x ≠ y) {m : ℕ} (hm : 2 ≤ m) : ‖(m.factorial : ℚ_[p])⁻¹ • x ^ m - (m.factorial : ℚ_[p])⁻¹ • y ^ m‖ < ‖x - y‖`
- What: For `m ≥ 2` the tail terms of the difference series are STRICTLY dominated by the linear term (strictness needs the open ball).
- How: Sets `r = max ‖x‖ ‖y‖`; the geometric factorisation `geom_sum₂_mul` with ultrametric `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` gives `‖x^m - y^m‖ ≤ ‖x-y‖·r^{m-1}`; raises to `(p-1)`-th power, bounds via `norm_factorial_inv_pow_le` and `pr^{p-1} < 1`, descends with `lt_of_pow_lt_pow_left₀`.
- Hypotheses: `x, y` in ball; `x ≠ y`; `m ≥ 2`; `p` prime. (`CompleteSpace` omitted.)
- Uses from project: [InExpBall, norm_factorial_inv_pow_le]
- Used by: `norm_padicExp_sub_padicExp`.
- Visibility: public
- Lines: 139-199 (proof ~56 lines)
- Notes: OVER-50 (needs /decompose-proof). `omit [CompleteSpace L]`.

### theorem norm_padicExp_sub_padicExp
- Type: `theorem norm_padicExp_sub_padicExp {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) : ‖padicExp p x - padicExp p y‖ = ‖x - y‖`
- What: E3 — `exp` is an isometry on the open ball.
- How: Subtracts the two summable series (`Summable.sub`, `tsum_sub`), peels two leading terms (`tsum_eq_zero_add`, `summable_nat_add_iff`); the order-≥2 tail is strictly smaller than `‖x-y‖` via `norm_factorial_inv_smul_pow_sub_lt` bounded by an ultrametric `IsUltrametricDist.norm_tsum_le_of_forall_le` (split at index N); concludes by `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`.
- Hypotheses: `x, y` in ball; `p` prime; `L` complete ultrametric.
- Uses from project: [InExpBall, padicExp, summable_padicExp_terms, norm_factorial_inv_smul_pow_sub_lt]
- Used by: `norm_padicExp_sub_one`, `padicExp_smul_padicLog_eq_onePAdicPow` (Lipschitz step).
- Visibility: public
- Lines: 201-259 (proof ~55 lines)
- Notes: OVER-50 (needs /decompose-proof).

### theorem norm_padicExp_sub_one
- Type: `theorem norm_padicExp_sub_one {x : L} (hx : InExpBall p x) : ‖padicExp p x - 1‖ = ‖x‖`
- What: `‖exp(x) - 1‖ = ‖x‖` on the ball.
- How: Specialises `norm_padicExp_sub_padicExp` at `y = 0` (showing `0 ∈ InExpBall`), then `simpa`.
- Hypotheses: `x` in ball; `p` prime.
- Uses from project: [InExpBall, padicExp, norm_padicExp_sub_padicExp]
- Used by: `padicLog_padicExp`, `pZpExp_coe`, `pZpExp_sub_one_mem`.
- Visibility: public
- Lines: 261-266 (proof 5 lines)
- Notes: none.

### theorem padicExp_add
- Type: `theorem padicExp_add {x y : L} (hx : InExpBall p x) (hy : InExpBall p y) : padicExp p (x + y) = padicExp p x * padicExp p y`
- What: E3 — the functional equation `exp(x+y) = exp(x)·exp(y)` on the ball.
- How: Double-series rearrangement: nonarchimedean product summability via `HasSum.mul_of_nonarchimedean`, then `tsum_mul_tsum_eq_tsum_sum_antidiagonal`; matches coefficients through `add_pow` (binomial), the choice identity `Nat.choose_mul_factorial_mul_factorial`, and `Algebra.smul_def`.
- Hypotheses: `x, y` in ball; `p` prime; `L` complete ultrametric NormedAlgebra.
- Uses from project: [InExpBall, summable_padicExp_terms, padicExp]
- Used by: `padicLog_mul`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public
- Lines: 268-307 (proof ~35 lines)
- Notes: long(30-50).

### theorem sub_one_mul_padicValNat_succ_le
- Type: `theorem sub_one_mul_padicValNat_succ_le (n : ℕ) : (p - 1) * padicValNat p (n + 1) ≤ n`
- What: `(p-1)·v_p(n+1) ≤ n` — the valuation growth of the logarithm denominators, for ANY `p : ℕ` (no primality).
- How: Case `p ≤ 1` trivial; for `p ≥ 2` uses `pow_padicValNat_dvd` (so `p^v ≤ n+1`) and the Bernoulli inequality `one_add_mul_le_pow`, combined with `linarith`.
- Hypotheses: none beyond `n : ℕ` (no `Fact p.Prime` — `omit hp`).
- Uses from project: []
- Used by: `norm_succ_inv_smul_pow_le`, `norm_natCast_inv_pow_le`.
- Visibility: public
- Lines: 309-329 (proof ~15 lines)
- Notes: none. `omit hp`.

### theorem norm_succ_inv_smul_pow_le
- Type: `theorem norm_succ_inv_smul_pow_le (y : L) (n : ℕ) : ‖(-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1))‖ ^ (p - 1) ≤ ‖y‖ ^ (p - 1) * ((p : ℝ) * ‖y‖ ^ (p - 1)) ^ n`
- What: The logarithm terms decay geometrically at the `(p-1)`-th power level.
- How: Expands the norm (`norm_mul`, `norm_smul`, `norm_inv`), computes `‖n+1‖` as `p^{-v_p(n+1)}` (`Padic.norm_eq_zpow_neg_valuation`), bounds via `sub_one_mul_padicValNat_succ_le` with `nlinarith`/`zpow_le_zpow_right₀`, then exponent arithmetic.
- Hypotheses: `p` prime. In `LogBall`: `L` a `NormSMulClass ℚ_[p]` module. (`IsUltrametricDist`/`CompleteSpace` omitted.)
- Uses from project: [sub_one_mul_padicValNat_succ_le]
- Used by: `summable_padicLog_terms`, `norm_succ_inv_smul_pow_lt`.
- Visibility: public (in `LogBall`)
- Lines: 341-368 (proof ~22 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem summable_padicLog_terms
- Type: `theorem summable_padicLog_terms {y : L} (hy : InExpBall p y) : Summable fun n : ℕ => (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • y ^ (n + 1))`
- What: On the open exponential ball, the logarithm series terms are summable.
- How: Same scheme as `summable_padicExp_terms`: `summable_iff_tendsto_cofinite_zero` + geometric bound `norm_succ_inv_smul_pow_le` dominated by `tendsto_pow_atTop_nhds_zero_of_lt_one`; ε-N chase.
- Hypotheses: `y` in ball; `p` prime; `L` complete ultrametric `NormSMulClass` module.
- Uses from project: [summable_iff_tendsto_cofinite_zero, InExpBall, norm_succ_inv_smul_pow_le]
- Used by: `norm_padicLog`, `padicLog_eq_tsum_coeff`, `padicExp_padicLog`.
- Visibility: public (in `LogBall`)
- Lines: 370-398 (proof 27 lines)
- Notes: none.

### def padicLog
- Type: `noncomputable def padicLog (x : L) : L := ∑' n : ℕ, (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1))`
- What: E4 — the p-adic logarithm `log(x) = ∑(-1)^{n+1}(x-1)^n/n`, junk-total.
- How: Definition (tsum at `x - 1`).
- Hypotheses: `L` a `NormSMulClass ℚ_[p]` module.
- Uses from project: []
- Used by: `padicLog_one`, `norm_padicLog`, `padicLog_eq_tsum_coeff`, `padicExp_padicLog`, `padicLog_padicExp`, `padicLog_mul`, `pZpLog`, `pZpLog_coe`, and transitively `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `LogBall`)
- Lines: 400-403 (def)
- Notes: none.

### theorem padicLog_one
- Type: `@[simp] theorem padicLog_one : padicLog p (1 : L) = 0`
- What: `log(1) = 0`.
- How: Unfolds `padicLog`; `simp` (every term has factor `(1-1)^{n+1} = 0`).
- Hypotheses: `p` prime.
- Uses from project: [padicLog]
- Used by: unused in file
- Visibility: public (simp, in `LogBall`)
- Lines: 405-408 (proof 2 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem norm_succ_inv_smul_pow_lt
- Type: `theorem norm_succ_inv_smul_pow_lt {y : L} (hy : InExpBall p y) (hy0 : y ≠ 0) {m : ℕ} (hm : 1 ≤ m) : ‖(-1 : L) ^ m * (((m : ℚ_[p]) + 1)⁻¹ • y ^ (m + 1))‖ < ‖y‖`
- What: For `m ≥ 1` the tail terms of the log series are strictly dominated by the linear term on the open ball.
- How: Bounds the `(p-1)`-th power via `norm_succ_inv_smul_pow_le`, uses `pow_le_pow_of_le_one` and `pr^{p-1} < 1` to get strict `< ‖y‖^{p-1}`, descends with `lt_of_pow_lt_pow_left₀`.
- Hypotheses: `y` in ball, `y ≠ 0`, `m ≥ 1`; `p` prime.
- Uses from project: [InExpBall, norm_succ_inv_smul_pow_le]
- Used by: `norm_padicLog`.
- Visibility: public (in `LogBall`)
- Lines: 410-433 (proof ~18 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem norm_padicLog
- Type: `theorem norm_padicLog {x : L} (hx : InExpBall p (x - 1)) : ‖padicLog p x‖ = ‖x - 1‖`
- What: `‖log(x)‖ = ‖x - 1‖` on the ball (logarithm is an isometry of `1+𝔪` onto `𝔪`).
- How: Peels the leading term (`tsum_eq_zero_add`), shows the tail (orders ≥1) is strictly smaller via `norm_succ_inv_smul_pow_lt` and ultrametric `IsUltrametricDist.norm_tsum_le_of_forall_le` (split at N), concludes with `norm_add_eq_max_of_norm_ne_norm`.
- Hypotheses: `x - 1` in ball; `p` prime; `L` complete ultrametric `NormSMulClass` module.
- Uses from project: [InExpBall, padicLog, summable_padicLog_terms, norm_succ_inv_smul_pow_lt]
- Used by: `padicLog_mul`, `pZpLog_coe`, `pZpLog_mem`.
- Visibility: public (in `LogBall`)
- Lines: 435-477 (proof ~42 lines)
- Notes: long(30-50).

### theorem oneAddX_mul_derivative_log
- Type: `theorem oneAddX_mul_derivative_log (A : Type*) [CommRing A] [Algebra ℚ A] : (1 + PowerSeries.X) * (d⁄dX A (PowerSeries.log A)) = 1`
- What: The formal geometric identity `(1+X)·D(log) = 1` (i.e. `D(log(1+X)) = 1/(1+X)`) over any ℚ-algebra.
- How: Rewrites `deriv_log`, then coefficient-by-coefficient (`ext n`) match against `coeff_one` via `coeff_succ_X_mul` and `ring`.
- Hypotheses: `A` a commutative ℚ-algebra.
- Uses from project: []
- Used by: `exp_subst_log`, `log_subst_exp_sub_one`.
- Visibility: public (in `Inversion`)
- Lines: 488-502 (proof ~12 lines)
- Notes: none.

### theorem exp_subst_log
- Type: `theorem exp_subst_log (A : Type*) [CommRing A] [Algebra ℚ A] : (exp A).subst (PowerSeries.log A) = 1 + PowerSeries.X`
- What: Formal identity (i) — `exp(log(1+X)) = 1 + X` as formal power series over any ℚ-algebra.
- How: From `(1+X)·D F = F` (using `derivative_subst`, `derivative_exp`, `oneAddX_mul_derivative_log`) plus `constantCoeff F = 1` (`constantCoeff_subst`), derives the recursion `coeff(m+2)·(m+2) = -m·coeff(m+1)`; an induction shows all coeffs ≥2 vanish (unit-ness of natCasts via `hunit`), then matches `1 + X` coefficientwise.
- Hypotheses: `A` a commutative ℚ-algebra.
- Uses from project: [oneAddX_mul_derivative_log]
- Used by: `padicExp_padicLog`.
- Visibility: public (in `Inversion`)
- Lines: 504-561 (proof ~54 lines)
- Notes: OVER-50 (needs /decompose-proof).

### theorem log_subst_exp_sub_one
- Type: `theorem log_subst_exp_sub_one (A : Type*) [CommRing A] [Algebra ℚ A] : (PowerSeries.log A).subst (exp A - 1) = PowerSeries.X`
- What: Formal identity (ii) — `log(1 + (exp - 1)) = X` as formal power series over any ℚ-algebra.
- How: `PowerSeries.derivative.ext`: shows `D(log.subst(exp-1)) = 1` (via `oneAddX_mul_derivative_log` substituted, `subst_mul`/`subst_add`, `1+(exp-1)=exp`) and constant coefficients match (`constantCoeff_subst_eq_zero`, `constantCoeff_log`); needs `IsAddTorsionFree A`.
- Hypotheses: `A` a commutative ℚ-algebra.
- Uses from project: [oneAddX_mul_derivative_log]
- Used by: `padicLog_padicExp`.
- Visibility: public (in `Inversion`)
- Lines: 563-586 (proof ~21 lines)
- Notes: none.

### theorem hasSum_pow_fin
- Type: `theorem hasSum_pow_fin {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R] {f : ℕ → R} {a : R} (hf : HasSum f a) (n : ℕ) : HasSum (fun φ : Fin n → ℕ => ∏ i, f (φ i)) (a ^ n)`
- What: The `n`-th power of an (unconditionally) summable family as a `HasSum` over tuples `Fin n → ℕ` — the iterated nonarchimedean Cauchy product.
- How: Induction on `n`; the successor step uses `HasSum.mul_of_nonarchimedean` and reindexes via `Fin.consEquiv.hasSum_iff` with `Fin.prod_univ_succ`.
- Hypotheses: `R` a nonarchimedean uniform comm ring; `HasSum f a`.
- Uses from project: [] (uses the `NonarchimedeanRing` typeclass which the file's instance provides for `L`, but no project decl by name)
- Used by: unused in file
- Visibility: public (in `Inversion`)
- Lines: 588-608 (proof ~20 lines)
- Notes: none.

### theorem summable_eval_pow
- Type: `theorem summable_eval_pow [Algebra ℚ_[p] L] (G : PowerSeries ℚ_[p]) (y : L) (hG : Summable fun m : ℕ => (coeff m G : ℚ_[p]) • y ^ m) (n : ℕ) : Summable fun k : ℕ => (coeff k (G ^ n) : ℚ_[p]) • y ^ k`
- What: Summability half — evaluating `G^n` at `y` is summable when the `G`-evaluation is (the iterated nonarchimedean Cauchy product).
- How: Induction on `n`; successor uses `summable_sum_mul_antidiagonal_of_summable_mul` on `HasSum.mul_of_nonarchimedean`, matched via `coeff_mul` / `smul_mul_smul_comm`.
- Hypotheses: `G`-evaluation summable; `p` prime; `L` complete ultrametric algebra (only `Algebra` actually needed; `NormedAlgebra`/`CompleteSpace` omitted).
- Uses from project: []
- Used by: `tsum_eval_pow`, `master_bridge`.
- Visibility: public (in `Inversion`)
- Lines: 610-634 (proof ~24 lines)
- Notes: none. `omit [CompleteSpace L] [NormedAlgebra ℚ_[p] L]`.

### theorem tsum_eval_pow
- Type: `theorem tsum_eval_pow [Algebra ℚ_[p] L] (G : PowerSeries ℚ_[p]) (y : L) (hG : Summable …) (n : ℕ) : (∑' m, (coeff m G) • y^m)^n = ∑' k, (coeff k (G^n)) • y^k`
- What: Value identity — `(eval G)^n = eval(G^n)` (the iterated nonarchimedean Cauchy product).
- How: Induction on `n`; successor uses `summable_eval_pow`, `tsum_mul_tsum_eq_tsum_sum_antidiagonal`, then `coeff_mul`/`smul_mul_smul_comm`.
- Hypotheses: `G`-evaluation summable; `p` prime; `L` algebra (NormedAlgebra/CompleteSpace omitted).
- Uses from project: [summable_eval_pow]
- Used by: `master_bridge`.
- Visibility: public (in `Inversion`)
- Lines: 636-660 (proof ~24 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`.

### theorem summable_coeff_pow_scalar
- Type: `theorem summable_coeff_pow_scalar (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) : Summable fun n : ℕ => (coeff n F : ℚ_[p]) * (coeff k (G ^ n) : ℚ_[p])`
- What: The scalar family `n ↦ [Xⁿ]F·[Xᵏ](Gⁿ)` has finite support (for `HasSubst G`), hence is summable.
- How: `HasSubst.eventually_coeff_pow_eq_zero` gives an `N` past which `[Xᵏ](Gⁿ)=0`; concludes via `summable_of_ne_finset_zero` on `Finset.range N`.
- Hypotheses: `HasSubst G`; `p` prime (algebra/ultrametric/complete all omitted).
- Uses from project: []
- Used by: `master_bridge`.
- Visibility: public (in `Inversion`)
- Lines: 662-670 (proof ~6 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem tsum_coeff_pow_eq_coeff_subst
- Type: `theorem tsum_coeff_pow_eq_coeff_subst (F G : PowerSeries ℚ_[p]) (hG : HasSubst G) (k : ℕ) : (∑' n, (coeff n F) * (coeff k (G^n))) = (coeff k (F.subst G))`
- What: The inner identity matching `PowerSeries.coeff_subst`: `∑ₙ [Xⁿ]F·[Xᵏ](Gⁿ) = [Xᵏ](F∘G)` (a finite sum since `[Xᵏ](Gⁿ)=0` for `n>k`).
- How: Truncates the tsum to `Finset.range N` (`tsum_eq_sum` using `eventually_coeff_pow_eq_zero`), rewrites the RHS via `coeff_subst'` and `finsum_eq_finsetSum_of_support_subset`, matches.
- Hypotheses: `HasSubst G`; `p` prime (algebra/ultrametric/complete omitted).
- Uses from project: []
- Used by: `master_bridge`.
- Visibility: public (in `Inversion`)
- Lines: 672-689 (proof ~17 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem master_bridge
- Type: `theorem master_bridge [Algebra ℚ_[p] L] [ContinuousSMul ℚ_[p] L] (F G : PowerSeries ℚ_[p]) (y : L) (hG : HasSubst G) (hGsum : …) (hprod : …) : (∑' n, (coeff n F) • (∑' m, (coeff m G) • y^m)^n) = ∑' k, (coeff k (F.subst G)) • y^k`
- What: Evaluation bridge — the value at `y` of a formal substitution `F.subst G` equals the composed convergent sum, given total-product summability.
- How: Rewrites LHS as a double tsum (via `tsum_eval_pow` + `tsum_const_smul`) and RHS likewise (via `tsum_coeff_pow_eq_coeff_subst` + `tsum_smul_const`), then swaps order by ultrametric Fubini `Summable.tsum_comm`.
- Hypotheses: `HasSubst G`; `G`-evaluation summable; total product family summable; `p` prime; `L` algebra with `ContinuousSMul` (NormedAlgebra omitted).
- Uses from project: [summable_eval_pow, tsum_eval_pow, summable_coeff_pow_scalar, tsum_coeff_pow_eq_coeff_subst]
- Used by: `padicExp_padicLog`, `padicLog_padicExp`.
- Visibility: public (in `Inversion`)
- Lines: 691-717 (proof ~21 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L]`.

### theorem pow_norm_sum_le
- Type: `theorem pow_norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → L) {m : ℕ} (hm : 1 ≤ m) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i ∈ s, ‖f i‖ ^ m ≤ C) : ‖∑ i ∈ s, f i‖ ^ m ≤ C`
- What: Ultrametric power bound: `‖∑ f i‖^m ≤ C` whenever every term satisfies `‖f i‖^m ≤ C`.
- How: Empty case trivial; otherwise `Finset.exists_mem_eq_sup'` picks the max-norm index and `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` bounds the sum norm by it, then `pow_le_pow_left₀`.
- Hypotheses: `m ≥ 1`, `0 ≤ C`, termwise bound; `L` ultrametric.
- Uses from project: []
- Used by: `norm_coeff_pow_le`.
- Visibility: public (in `Inversion`)
- Lines: 719-735 (proof ~15 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [CompleteSpace L]`.

### theorem norm_coeff_prod_le
- Type: `theorem norm_coeff_prod_le (G : PowerSeries ℚ_[p]) (hcoeff : ∀ j, 1 ≤ j → ‖(coeff j G)‖^{p-1} ≤ p^{j-1}) (hc0 : (coeff 0 G) = 0) (n k : ℕ) (l : ℕ →₀ ℕ) (hl : l ∈ Finset.finsuppAntidiag (Finset.range n) k) : ‖∏ i ∈ range n, (coeff (l i) G)‖^{p-1} ≤ p^{k-n}`
- What: Legendre-type bound on a single multinomial term of `[Xᵏ](Gⁿ)`, bounded by `p^{k-n}`.
- How: If some `l i = 0` the product vanishes (`Finset.prod_eq_zero` + `hc0`); else all `l i ≥ 1`, so `norm_prod`/`Finset.prod_le_prod` with `hcoeff` and `Finset.prod_pow_eq_pow_sum`; the telescoping `∑(l i - 1) = k - n` via `Finset.sum_tsub_distrib`.
- Hypotheses: per-coeff Legendre bound, `[X⁰]G = 0`, `l` an antidiagonal partition; `p` prime.
- Uses from project: []
- Used by: `norm_coeff_pow_le`.
- Visibility: public (in `Inversion`)
- Lines: 737-766 (proof ~30 lines)
- Notes: long(30-50).

### theorem norm_coeff_pow_le
- Type: `theorem norm_coeff_pow_le (G : PowerSeries ℚ_[p]) (hcoeff : ∀ j, 1 ≤ j → ‖(coeff j G)‖^{p-1} ≤ p^{j-1}) (hc0 : (coeff 0 G) = 0) (n k : ℕ) : ‖(coeff k (G ^ n))‖^{p-1} ≤ p^{k-n}`
- What: Legendre-type bound on the substituted-power coefficients `‖[Xᵏ](Gⁿ)‖^{p-1} ≤ p^{k-n}`.
- How: Expands `coeff_pow` (multinomial sum) and applies `pow_norm_sum_le` with the per-term bound `norm_coeff_prod_le`.
- Hypotheses: per-coeff Legendre bound, `[X⁰]G = 0`; `p` prime.
- Uses from project: [pow_norm_sum_le, norm_coeff_prod_le]
- Used by: `summable_prod_family`.
- Visibility: public (in `Inversion`)
- Lines: 768-777 (proof ~6 lines)
- Notes: none.

### theorem coeff_pow_eq_zero_of_lt
- Type: `theorem coeff_pow_eq_zero_of_lt (G : PowerSeries ℚ_[p]) (hc0 : constantCoeff G = 0) {n k : ℕ} (hkn : k < n) : (coeff k (G ^ n) : ℚ_[p]) = 0`
- What: `[Xᵏ](Gⁿ) = 0` for `k < n` when `[X⁰]G = 0` (order of `Gⁿ` is ≥ n).
- How: `coeff_of_lt_order` with `le_order_pow_of_constantCoeff_eq_zero`.
- Hypotheses: `constantCoeff G = 0`, `k < n`.
- Uses from project: []
- Used by: `summable_prod_family`.
- Visibility: public (in `Inversion`)
- Lines: 779-784 (proof 3 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem summable_prod_family
- Type: `theorem summable_prod_family (F G : PowerSeries ℚ_[p]) (y : L) (hy : InExpBall p y) (hF : ∀ n, 1 ≤ n → ‖coeff n F‖^{p-1} ≤ p^{n-1}) (hGc : ∀ j, 1 ≤ j → ‖coeff j G‖^{p-1} ≤ p^{j-1}) (hG0 : constantCoeff G = 0) : Summable fun nk : ℕ × ℕ => ((coeff nk.1 F) * (coeff nk.2 (G ^ nk.1))) • y ^ nk.2`
- What: The product family of the evaluation bridge is summable, by a uniform geometric bound `≤ p⁻¹·(p‖y‖^{p-1})ᵏ` plus the support condition `n ≤ k`.
- How: `summable_iff_tendsto_cofinite_zero` → bound the set where the norm `≥ ε` finite; case-splits on `n=0` (forces `k=0`) and `n≥1`; the key estimate combines `hF`, `norm_coeff_pow_le` and `coeff_pow_eq_zero_of_lt` (so `n ≤ k`), and `tendsto_pow_atTop_nhds_zero_of_lt_one` for the geometric decay (`hK`).
- Hypotheses: `y` in ball; Legendre bounds on `F`,`G`; `[X⁰]G = 0`; `p` prime; `L` complete ultrametric NormedAlgebra.
- Uses from project: [InExpBall, summable_iff_tendsto_cofinite_zero, coeff_pow_eq_zero_of_lt, norm_coeff_pow_le]
- Used by: `padicExp_padicLog`, `padicLog_padicExp`.
- Visibility: public (in `Inversion`)
- Lines: 786-853 (proof ~63 lines)
- Notes: OVER-50 (needs /decompose-proof).

### theorem norm_natCast_inv_pow_le
- Type: `theorem norm_natCast_inv_pow_le (n : ℕ) : (‖(n : ℚ_[p])‖ ^ (p - 1))⁻¹ ≤ (p : ℝ) ^ (n - 1)`
- What: The inverted Legendre bound for a plain integer `n`: `‖n‖^{-(p-1)} ≤ p^{n-1}` (for `n=0` both sides reduce to `0 ≤ 1`).
- How: `n=0` case explicit; else `‖n‖ = p^{-v_p(n)}` (`Padic.norm_eq_zpow_neg_valuation`) and `sub_one_mul_padicValNat_succ_le` (rewritten to `n`), closed by `zpow_le_zpow_right₀`/`linarith`.
- Hypotheses: `p` prime.
- Uses from project: [sub_one_mul_padicValNat_succ_le]
- Used by: `norm_coeff_log_le`.
- Visibility: public (in `Inversion`)
- Lines: 855-878 (proof ~18 lines)
- Notes: none.

### theorem norm_coeff_exp_le
- Type: `theorem norm_coeff_exp_le (n : ℕ) (hn : 1 ≤ n) : ‖(coeff n (exp ℚ_[p]) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (n - 1)`
- What: The `exp` coefficients obey the Legendre bound.
- How: Rewrites `coeff_exp` (= `1/n!`) and applies `norm_factorial_inv_pow_le`.
- Hypotheses: `n ≥ 1`; `p` prime.
- Uses from project: [norm_factorial_inv_pow_le]
- Used by: `padicExp_padicLog`, `padicLog_padicExp` (via `hGc`).
- Visibility: public (in `Inversion`)
- Lines: 880-884 (proof 2 lines)
- Notes: none.

### theorem norm_coeff_log_le
- Type: `theorem norm_coeff_log_le (n : ℕ) (hn : 1 ≤ n) : ‖(coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p])‖ ^ (p - 1) ≤ (p : ℝ) ^ (n - 1)`
- What: The `log` coefficients obey the Legendre bound.
- How: Rewrites `coeff_log` (= `(-1)^{n+1}/n`) and applies `norm_natCast_inv_pow_le`.
- Hypotheses: `n ≥ 1`; `p` prime.
- Uses from project: [norm_natCast_inv_pow_le]
- Used by: `padicExp_padicLog`, `padicLog_padicExp`.
- Visibility: public (in `Inversion`)
- Lines: 886-892 (proof ~4 lines)
- Notes: none.

### theorem padicExp_eq_tsum_coeff
- Type: `theorem padicExp_eq_tsum_coeff (z : L) : padicExp p z = ∑' n : ℕ, (coeff n (exp ℚ_[p]) : ℚ_[p]) • z ^ n`
- What: `padicExp z = ∑ₙ [Xⁿ]exp · zⁿ` — the exponential as the evaluation of `PowerSeries.exp`.
- How: Unfolds `padicExp`, `tsum_congr` matching `coeff_exp = 1/n!`.
- Hypotheses: `p` prime (ultrametric/complete omitted).
- Uses from project: [padicExp]
- Used by: `tsum_coeff_exp_sub_one`, `padicExp_padicLog`, `padicLog_padicExp`.
- Visibility: public (in `Inversion`)
- Lines: 894-899 (proof 2 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem padicLog_term_eq
- Type: `theorem padicLog_term_eq (x : L) (n : ℕ) : (-1 : L) ^ n * (((n : ℚ_[p]) + 1)⁻¹ • (x - 1) ^ (n + 1)) = (coeff (n + 1) (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ (n + 1)`
- What: Termwise match of the `padicLog` series with the `PowerSeries.log` coefficients.
- How: Rewrites `(-1)^n` through `algebraMap`, uses `Algebra.smul_def` and `coeff_log` (= `(-1)^{n+1}/(n+1)`), `ring`.
- Hypotheses: `p` prime; `L` NormedAlgebra.
- Uses from project: []
- Used by: `padicLog_eq_tsum_coeff`, `padicExp_padicLog`, `padicLog_padicExp` (via summability congruences).
- Visibility: public (in `Inversion`)
- Lines: 901-914 (proof ~11 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem padicLog_eq_tsum_coeff
- Type: `theorem padicLog_eq_tsum_coeff {x : L} (hx : InExpBall p (x - 1)) : padicLog p x = ∑' n : ℕ, (coeff n (PowerSeries.log ℚ_[p]) : ℚ_[p]) • (x - 1) ^ n`
- What: `padicLog x = ∑ₙ [Xⁿ]log · (x-1)ⁿ` — the logarithm as the evaluation of `PowerSeries.log` at `x-1`.
- How: Reindexes `summable_padicLog_terms` via `padicLog_term_eq` and `summable_nat_add_iff`, peels the zero coefficient (`coeff_log` at 0), `tsum_congr` with `padicLog_term_eq`.
- Hypotheses: `x - 1` in ball; `p` prime; `L` NormedAlgebra.
- Uses from project: [InExpBall, padicLog, summable_padicLog_terms, padicLog_term_eq]
- Used by: `padicExp_padicLog`, `padicLog_padicExp`.
- Visibility: public (in `Inversion`)
- Lines: 916-927 (proof ~9 lines)
- Notes: none.

### theorem tsum_coeff_exp_sub_one
- Type: `theorem tsum_coeff_exp_sub_one (y : L) (hy : InExpBall p y) : (∑' m : ℕ, (coeff m (exp ℚ_[p] - 1) : ℚ_[p]) • y ^ m) = padicExp p y - 1`
- What: `∑ₘ [Xᵐ](exp-1)·yᵐ = padicExp y - 1` — peeling the vanishing constant term.
- How: Builds summability of `exp` and `(exp-1)` evaluations (`summable_padicExp_terms`, `summable_nat_add_iff`), peels leading terms via `tsum_eq_zero_add`, kills the constant via `constantCoeff_exp`, `tsum_congr`.
- Hypotheses: `y` in ball; `p` prime; `L` NormedAlgebra.
- Uses from project: [InExpBall, summable_padicExp_terms, padicExp_eq_tsum_coeff, padicExp]
- Used by: `padicLog_padicExp`.
- Visibility: public (in `Inversion`)
- Lines: 929-945 (proof ~16 lines)
- Notes: none.

### theorem eval_oneAddX (private)
- Type: `private theorem eval_oneAddX (y : L) : (∑' k : ℕ, (coeff k (1 + PowerSeries.X : PowerSeries ℚ_[p]) : ℚ_[p]) • y ^ k) = 1 + y`
- What: Evaluating the formal series `1 + X` at `y` gives `1 + y`.
- How: Terms of degree ≥2 vanish (`coeff_one`, `coeff_X`); `tsum_eq_sum` over `{0,1}` then explicit coefficient computation.
- Hypotheses: `p` prime; `L` NormedAlgebra (ultrametric/complete omitted).
- Uses from project: []
- Used by: `padicExp_padicLog`.
- Visibility: private
- Lines: 947-959 (proof ~10 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem eval_X (private)
- Type: `private theorem eval_X (y : L) : (∑' k : ℕ, (coeff k (PowerSeries.X : PowerSeries ℚ_[p]) : ℚ_[p]) • y ^ k) = y`
- What: Evaluating the formal series `X` at `y` gives `y`.
- How: `tsum_eq_single 1` with `coeff_X`, then `one_smul`.
- Hypotheses: `p` prime; `L` NormedAlgebra (ultrametric/complete omitted).
- Uses from project: []
- Used by: `padicLog_padicExp`.
- Visibility: private
- Lines: 961-965 (proof ~2 lines)
- Notes: none. `omit [IsUltrametricDist L] [CompleteSpace L]`.

### theorem padicExp_padicLog
- Type: `theorem padicExp_padicLog {x : L} (hx : InExpBall p (x - 1)) : padicExp p (padicLog p x) = x`
- What: E4 — `exp` inverts `log` on the matched balls (`exp(log x) = x`).
- How: Rewrites both sides as power-series evaluations (`padicExp_eq_tsum_coeff`, `padicLog_eq_tsum_coeff`), then the `master_bridge` with `summable_prod_family`, the formal identity `exp_subst_log`, and `eval_oneAddX`; `ring`.
- Hypotheses: `x - 1` in ball; `p` prime; `L` complete ultrametric NormedAlgebra.
- Uses from project: [InExpBall, padicExp_eq_tsum_coeff, padicLog_eq_tsum_coeff, master_bridge, summable_prod_family, norm_coeff_exp_le, norm_coeff_log_le, exp_subst_log, eval_oneAddX, padicLog_term_eq, summable_padicLog_terms]
- Used by: `padicLog_mul`, `padicExp_smul_padicLog_eq_onePAdicPow` (via `hκone`).
- Visibility: public (in `Inversion`)
- Lines: 967-980 (proof ~11 lines)
- Notes: none.

### theorem padicLog_padicExp
- Type: `theorem padicLog_padicExp {x : L} (hx : InExpBall p x) : padicLog p (padicExp p x) = x`
- What: E4 — `log` inverts `exp` on the matched balls (`log(exp x) = x`).
- How: Shows `exp x - 1 ∈ ball` (via `norm_padicExp_sub_one`), assembles summability and Legendre bounds for `exp - 1`, then `padicLog_eq_tsum_coeff`, `tsum_coeff_exp_sub_one`, `master_bridge`, the formal `log_subst_exp_sub_one`, `eval_X`.
- Hypotheses: `x` in ball; `p` prime; `L` complete ultrametric NormedAlgebra.
- Uses from project: [InExpBall, norm_padicExp_sub_one, summable_padicExp_terms, padicLog_eq_tsum_coeff, tsum_coeff_exp_sub_one, master_bridge, summable_prod_family, norm_coeff_log_le, norm_coeff_exp_le, log_subst_exp_sub_one, eval_X, padicExp_eq_tsum_coeff]
- Used by: `padicLog_mul`.
- Visibility: public (in `Inversion`)
- Lines: 982-1003 (proof ~21 lines)
- Notes: none.

### theorem padicLog_mul
- Type: `theorem padicLog_mul {x y : L} (hx : InExpBall p (x - 1)) (hy : InExpBall p (y - 1)) : padicLog p (x * y) = padicLog p x + padicLog p y`
- What: E4 / RJW 5.14 — the logarithm is multiplicative on `1 + 𝔪`.
- How: Sets `a = log x`, `b = log y`; shows `a, b, a+b` are in the ball (using `norm_padicLog` and ultrametric `norm_add_le_max`); applies `padicExp_padicLog` and the functional equation `padicExp_add`, then `padicLog_padicExp`.
- Hypotheses: `x-1, y-1` in ball; `p` prime; `L` complete ultrametric NormedAlgebra.
- Uses from project: [InExpBall, padicLog, norm_padicLog, padicExp_padicLog, padicExp_add, padicLog_padicExp]
- Used by: unused in file
- Visibility: public (in `Inversion`)
- Lines: 1005-1025 (proof ~19 lines)
- Notes: none.

### theorem coe_norm_le_inv_of_mem_span
- Type: `theorem coe_norm_le_inv_of_mem_span {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : ‖(x : ℚ_[p])‖ ≤ (p : ℝ)⁻¹`
- What: E5 — an element of `pℤ_p` has `ℚ_[p]`-norm at most `p⁻¹`.
- How: Rewrites `p⁻¹` as `p^{-1}` and uses `PadicInt.norm_le_pow_iff_mem_span_pow` at exponent 1 (with `PadicInt.norm_def`).
- Hypotheses: `x ∈ pℤ_p`; `p` prime.
- Uses from project: []
- Used by: `inExpBall_of_mem_span`, `pZpExp_coe`, `pZpExp_sub_one_mem`, `pZpLog_coe`, `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `pZp`)
- Lines: 1031-1038 (proof ~4 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem inExpBall_of_mem_span
- Type: `theorem inExpBall_of_mem_span (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : InExpBall p ((x : ℚ_[p]))`
- What: E5 — for odd `p`, `pℤ_p` lies strictly inside the exponential convergence ball.
- How: From `coe_norm_le_inv_of_mem_span`, `‖x‖^{p-1} ≤ (p⁻¹)^{p-1} < (p⁻¹)^1 = p⁻¹` since `p-1 ≥ 2` (where `hp2`/`p ≥ 3` enters), via `pow_lt_pow_right_of_lt_one₀`.
- Hypotheses: `p ≠ 2`, `x ∈ pℤ_p`; `p` prime.
- Uses from project: [coe_norm_le_inv_of_mem_span, InExpBall]
- Used by: `padicExp_converges_on_pZp`, `pZpExp_coe`, `pZpExp_sub_one_mem`, `pZpLog_coe`, `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `pZp`)
- Lines: 1040-1058 (proof ~13 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem padicExp_converges_on_pZp
- Type: `theorem padicExp_converges_on_pZp (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : Summable fun n : ℕ => (n.factorial : ℚ_[p])⁻¹ • ((x : ℚ_[p]) ^ n)`
- What: RJW 5.14 first half — for odd `p`, the exp series converges on `pℤ_p`.
- How: Direct application of `summable_padicExp_terms` (at `L = ℚ_[p]`) to `inExpBall_of_mem_span`.
- Hypotheses: `p ≠ 2`, `x ∈ pℤ_p`; `p` prime.
- Uses from project: [summable_padicExp_terms, inExpBall_of_mem_span]
- Used by: unused in file
- Visibility: public (in `pZp`)
- Lines: 1060-1068 (proof 1 line)
- Notes: none.

### def pZpExp
- Type: `noncomputable def pZpExp (x : ℤ_[p]) : ℤ_[p] := if h : ‖padicExp p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicExp p ((x : ℚ_[p])), h⟩ else 1`
- What: The integral exponential on `pℤ_p` (odd `p`), valued in `1 + pℤ_p`; junk-total via an integrality certificate (junk value 1).
- How: Definition (dite on the integrality bound).
- Hypotheses: `p` prime.
- Uses from project: [padicExp]
- Used by: `pZpExp_coe`, `pZpExp_sub_one_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `pZp`)
- Lines: 1070-1075 (def)
- Notes: none.

### theorem pZpExp_coe
- Type: `theorem pZpExp_coe (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : ((pZpExp p x : ℤ_[p]) : ℚ_[p]) = padicExp p ((x : ℚ_[p]))`
- What: E5 — on `pℤ_p` (odd `p`) the analytic exponential is integral, so `pZpExp` takes its true branch.
- How: Proves `‖exp x‖ ≤ 1` by writing `exp x = 1 + (exp x - 1)` and bounding via ultrametric `norm_add_le_max` with `norm_padicExp_sub_one` and `‖x‖ ≤ 1`; then `dif_pos`.
- Hypotheses: `p ≠ 2`, `x ∈ pℤ_p`; `p` prime.
- Uses from project: [pZpExp, inExpBall_of_mem_span, norm_padicExp_sub_one, coe_norm_le_inv_of_mem_span, padicExp]
- Used by: `pZpExp_sub_one_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `pZp`)
- Lines: 1077-1094 (proof ~17 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem pZpExp_sub_one_mem
- Type: `theorem pZpExp_sub_one_mem (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : pZpExp p x - 1 ∈ Ideal.span {(p : ℤ_[p])}`
- What: `exp(x) - 1 ∈ pℤ_p`, i.e. `pZpExp` lands in `1 + pℤ_p`.
- How: Reduces membership to `‖pZpExp x - 1‖ ≤ p^{-1}` (`PadicInt.norm_le_pow_iff_mem_span_pow`), rewrites via `pZpExp_coe` and `norm_padicExp_sub_one`, concludes by `coe_norm_le_inv_of_mem_span`.
- Hypotheses: `p ≠ 2`, `x ∈ pℤ_p`; `p` prime.
- Uses from project: [pZpExp, pZpExp_coe, norm_padicExp_sub_one, inExpBall_of_mem_span, coe_norm_le_inv_of_mem_span]
- Used by: unused in file
- Visibility: public (in `pZp`)
- Lines: 1096-1103 (proof ~6 lines)
- Notes: none.

### def pZpLog
- Type: `noncomputable def pZpLog (x : ℤ_[p]) : ℤ_[p] := if h : ‖padicLog p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicLog p ((x : ℚ_[p])), h⟩ else 0`
- What: The integral logarithm on `1 + pℤ_p` (odd `p`), valued in `pℤ_p`; junk-total via an integrality certificate (junk value 0).
- How: Definition (dite on the integrality bound).
- Hypotheses: `p` prime.
- Uses from project: [padicLog]
- Used by: `pZpLog_coe`, `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `pZp`)
- Lines: 1105-1110 (def)
- Notes: none.

### theorem pZpLog_coe
- Type: `theorem pZpLog_coe (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) : ((pZpLog p x : ℤ_[p]) : ℚ_[p]) = padicLog p ((x : ℚ_[p]))`
- What: E5 — on `1 + pℤ_p` (odd `p`) the analytic logarithm is integral, so `pZpLog` takes its true branch.
- How: Shows `(x:ℚ_[p]) - 1 = (x-1 : ℤ_[p])` is in the ball, bounds `‖log x‖ = ‖x-1‖ ≤ 1` via `norm_padicLog` and `coe_norm_le_inv_of_mem_span`, then `dif_pos`.
- Hypotheses: `p ≠ 2`, `x - 1 ∈ pℤ_p`; `p` prime.
- Uses from project: [pZpLog, inExpBall_of_mem_span, norm_padicLog, coe_norm_le_inv_of_mem_span, padicLog]
- Used by: `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `pZp`)
- Lines: 1112-1126 (proof ~14 lines)
- Notes: none. `omit [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`.

### theorem pZpLog_mem
- Type: `theorem pZpLog_mem (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) : pZpLog p x ∈ Ideal.span {(p : ℤ_[p])}`
- What: `log(x) ∈ pℤ_p`, i.e. `pZpLog` lands in `pℤ_p`.
- How: Reduces to `‖pZpLog x‖ ≤ p^{-1}` (`PadicInt.norm_le_pow_iff_mem_span_pow`), rewrites via `pZpLog_coe` and `norm_padicLog`, concludes by `coe_norm_le_inv_of_mem_span`.
- Hypotheses: `p ≠ 2`, `x - 1 ∈ pℤ_p`; `p` prime.
- Uses from project: [pZpLog, inExpBall_of_mem_span, pZpLog_coe, norm_padicLog, coe_norm_le_inv_of_mem_span]
- Used by: `padicExp_smul_padicLog_eq_onePAdicPow`.
- Visibility: public (in `pZp`)
- Lines: 1128-1138 (proof ~8 lines)
- Notes: none.

### theorem padicExp_smul_padicLog_eq_onePAdicPow
- Type: `theorem padicExp_smul_padicLog_eq_onePAdicPow (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : x - 1 ∈ Ideal.span {(p : ℤ_[p])}) (s : ℤ_[p]) : pZpExp p (s * pZpLog p x) = PadicInt.onePAdicPow p x hx s`
- What: RJW 5.14 second half — for `s ∈ ℤ_p`, `x ↦ x^s := exp(s·log x)` is well-defined and agrees with the character `PadicInt.onePAdicPow` (uniqueness of continuous characters).
- How: Builds the `AddChar ℤ_[p] ℤ_[p]` `κ : t ↦ pZpExp(t·ℓ)` (with `ℓ = pZpLog x`), proving `map_zero_eq_one'` (`padicExp_zero`) and `map_add_eq_mul'` (`padicExp_add`); shows `κ` is `LipschitzWith 1` (continuous) via `norm_padicExp_sub_padicExp` and `‖ℓ‖ ≤ 1`; computes `κ 1 = x` via `padicExp_padicLog`; then `PadicInt.eq_addChar_of_value_at_one` (using `PadicInt.tendsto_pow_atTop_nhds_zero_of_mem_span`) forces `κ = onePAdicPow`, evaluated at `s`.
- Hypotheses: `p ≠ 2`, `x - 1 ∈ pℤ_p`, `s ∈ ℤ_p`; `p` prime.
- Uses from project: [pZpExp, pZpLog, pZpLog_mem, pZpExp_coe, padicExp_zero, padicExp_add, inExpBall_of_mem_span, norm_padicExp_sub_padicExp, coe_norm_le_inv_of_mem_span, pZpLog_coe, padicExp_padicLog]
- Used by: unused in file
- Visibility: public (in `pZp`)
- Lines: 1140-1198 (proof ~52 lines)
- Notes: OVER-50 (needs /decompose-proof).

---

## File Summary

Total declarations: 46
- defs: 6 (`padicExp`, `padicLog`, `pZpExp`, `pZpLog`, `InExpBall`; plus `def InExpBall` is a Prop-valued def — counted) — precisely: `InExpBall`, `padicExp`, `padicLog`, `pZpExp`, `pZpLog` = 5 noncomputable/Prop defs.
- lemmas + theorems: 40
- instances: 1 (`NonarchimedeanRing L`)

(46 = 5 defs + 40 theorems + 1 instance.)

Key API (used by ≥3 in-file):
- `InExpBall` — the central convergence predicate (used by ~20+ decls).
- `padicExp` — used by ~12 decls.
- `padicLog` — used by ~8 decls.
- `summable_padicExp_terms` — used by 5.
- `inExpBall_of_mem_span` — used by 6.
- `coe_norm_le_inv_of_mem_span` — used by 6.
- `norm_padicExp_sub_one` — used by 3.
- `norm_padicLog` — used by 3.
- `master_bridge` — used by 2 (the two inversion theorems; near-key).
- `summable_prod_family` — used by 2.

Unused in file (terminal/exported API): `padicLog_one`, `hasSum_pow_fin`, `padicLog_mul`, `padicExp_converges_on_pZp`, `pZpExp_sub_one_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`. (These are the project's public deliverables — exported for downstream Iwasawa/character work, not consumed here.)

Decls with sorry: NONE.

set_option: NONE.

Proofs > 50 lines (OVER-50) — 6 total:
1. `norm_factorial_inv_smul_pow_sub_lt` (lines 139-199, ~56)
2. `norm_padicExp_sub_padicExp` (lines 201-259, ~55)
3. `exp_subst_log` (lines 504-561, ~54)
4. `summable_prod_family` (lines 786-853, ~63)
5. `padicExp_smul_padicLog_eq_onePAdicPow` (lines 1140-1198, ~52)
6. (borderline) — only the five above are clearly >50; `padicExp_add` and others are 30-50.

Correction: exactly 5 proofs strictly >50 lines: `norm_factorial_inv_smul_pow_sub_lt`, `norm_padicExp_sub_padicExp`, `exp_subst_log`, `summable_prod_family`, `padicExp_smul_padicLog_eq_onePAdicPow`.

Proofs 30-50 lines (long) — 3 total:
1. `padicExp_add` (lines 268-307, ~35)
2. `norm_padicLog` (lines 435-477, ~42)
3. `norm_coeff_prod_le` (lines 737-766, ~30)
