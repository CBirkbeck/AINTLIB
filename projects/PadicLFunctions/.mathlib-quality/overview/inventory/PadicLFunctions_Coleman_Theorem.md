# Inventory: `PadicLFunctions/Coleman/Theorem.lean`

File-level: the evaluation-at-`π_n` layer of the Coleman map (RJW §9). A `ℤ_p`-power series `f` is identified with the rigid-analytic function `z ↦ f(z)` on `B(0,1) ⊂ ℂ_p`; `evalPi f n = f(π_n)`. Deliverables: ring-hom behaviour at each level, integrality, `φ`-equivariance, Weierstrass uniqueness, single-level interpolation, the evaluation/norm commuting square, and Coleman's theorem (`coleman_existsUnique`, `colemanSeries`, multiplicativity, injectivity).

`variable (p : ℕ) [hp : Fact p.Prime]` throughout; `open PowerSeries`; `namespace PadicLFunctions.Coleman`.

---

### def toCp
- Type: `noncomputable def toCp : ℤ_[p] →+* ℂ_[p]`
- What: The coefficient inclusion `ℤ_p ↪ ℚ_p ↪ ℂ_p` as a ring homomorphism (the §7 `M`-pattern).
- How: Composition `(algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom)`.
- Hypotheses: none beyond `p` prime.
- Uses from project: []
- Used by: `norm_toCp`, `norm_coeff_map_le_one`, `evalPi`, `evalPi_C`, `evalPi_coe_polynomial`, `quot_mem_O`, `exists_residue_pi`, `evalPiES`, `leftMulMatrix_zetaBasis_coe`, `norm_evalPi_sub_le_of_modEqPow`, `tendsto_evalPi_of_tendsto`, `evalPi_partialSum_mem_K`, and most evaluation lemmas.
- Visibility: public
- Lines: 61-62 (def body 1 line)
- Notes: none

### theorem norm_toCp
- Type: `theorem norm_toCp (x : ℤ_[p]) : ‖toCp p x‖ = ‖x‖`
- What: `toCp` is isometric: it preserves norm on `ℤ_p`.
- How: Unfold `toCp`; the `ℚ_p ↪ ℂ_p` extension is isometric (`norm_algebraMap'`) and `ℤ_p ↪ ℚ_p` preserves norm by `PadicInt.norm_def`.
- Hypotheses: none.
- Uses from project: [toCp]
- Used by: `norm_coeff_map_le_one`, `exists_evalPi_eq` (via `hkey`), `norm_evalPi_sub_le_of_modEqPow`, `tendsto_evalPi_of_tendsto`, `exists_residue_pi` (`hnormtm`).
- Visibility: public
- Lines: 67-68 (proof 2 lines)
- Notes: none

### theorem norm_coeff_map_le_one
- Type: `theorem norm_coeff_map_le_one (f : PowerSeries ℤ_[p]) (k : ℕ) : ‖coeff k (PowerSeries.map (toCp p) f)‖ ≤ 1`
- What: The pushed-forward coefficients of a `ℤ_p`-series are in the unit ball of `ℂ_p`.
- How: `coeff_map` + `norm_toCp` reduce to `‖coeff k f‖ ≤ 1` in `ℤ_p` (`PadicInt.norm_le_one`).
- Hypotheses: none.
- Uses from project: [toCp, norm_toCp]
- Used by: `summable_evalPi`, `evalPi_mem_O`, `evalPi_phi`.
- Visibility: public
- Lines: 72-75 (proof 3 lines)
- Notes: none

### def evalPi
- Type: `noncomputable def evalPi (f : PowerSeries ℤ_[p]) (n : ℕ) : ℂ_[p]`
- What: **Evaluation at `π_n`**: the value `f(π_n)` of a `ℤ_p`-power series at the uniformiser `π_n ∈ B(0,1)`.
- How: `seriesEval (PowerSeries.map (toCp p) f) (pi p n)` — push coefficients into `ℂ_p`, sum the convergent series at `π_n`.
- Hypotheses: none in the def; convergence needs `n ≥ 1`.
- Uses from project: [toCp, seriesEval, pi]
- Used by: essentially every subsequent declaration in the file.
- Visibility: public
- Lines: 80-81 (def body 1 line)
- Notes: none

### theorem summable_evalPi
- Type: `theorem summable_evalPi (f) {n} (hn : 1 ≤ n) : Summable fun k => coeff k (map (toCp p) f) * pi p n ^ k`
- What: The evaluation series for `f(π_n)` converges when `n ≥ 1`.
- How: `summable_seriesEval_of_norm_coeff_le_one` with integral coefficients (`norm_coeff_map_le_one`) and `‖π_n‖ < 1` (`norm_pi_lt_one`).
- Hypotheses: `n ≥ 1`.
- Uses from project: [toCp, pi, norm_coeff_map_le_one, summable_seriesEval_of_norm_coeff_le_one, norm_pi_lt_one]
- Used by: `evalPi_add`, `evalPi_sub`, `evalPi_mul`, `evalPi_mem_O`, `exists_evalPi_eq`.
- Visibility: public
- Lines: 85-88 (proof 2 lines)
- Notes: none

### theorem evalPi_add
- Type: `theorem evalPi_add (f g) {n} (hn : 1 ≤ n) : evalPi p (f + g) n = evalPi p f n + evalPi p g n`
- What: Evaluation at `π_n` is additive for `n ≥ 1`.
- How: `map_add` then `seriesEval_add` with both convergence inputs from `summable_evalPi`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, summable_evalPi, seriesEval_add]
- Used by: `evalPiHom`.
- Visibility: public
- Lines: 98-101 (proof 2 lines)
- Notes: none

### theorem evalPi_sub
- Type: `theorem evalPi_sub (f g) {n} (hn : 1 ≤ n) : evalPi p (f - g) n = evalPi p f n - evalPi p g n`
- What: Evaluation at `π_n` respects subtraction for `n ≥ 1`.
- How: `map_sub` then `seriesEval_sub` with convergence from `summable_evalPi`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, summable_evalPi, seriesEval_sub]
- Used by: `evalPi_injective` (`hzero`), `norm_evalPi_sub_le_of_modEqPow`, `tendsto_evalPi_of_tendsto`.
- Visibility: public
- Lines: 104-107 (proof 2 lines)
- Notes: none

### theorem evalPi_mul
- Type: `theorem evalPi_mul (f g) {n} (hn : 1 ≤ n) : evalPi p (f * g) n = evalPi p f n * evalPi p g n`
- What: Evaluation at `π_n` is multiplicative for `n ≥ 1` (nonarchimedean Cauchy product).
- How: `map_mul` then `seriesEval_mul` with convergence from `summable_evalPi`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, summable_evalPi, seriesEval_mul]
- Used by: `evalPi_pow`, `evalPiHom`, `evalPi_injective`, `norm_evalPi_sub_le_of_modEqPow`, `colemanSeries_mul`, `evalPi_one_add_X_pow`.
- Visibility: public
- Lines: 110-113 (proof 2 lines)
- Notes: none

### theorem evalPi_one
- Type: `@[simp] theorem evalPi_one (n : ℕ) : evalPi p (1 : PowerSeries ℤ_[p]) n = 1`
- What: The constant series `1` evaluates to `1`.
- How: `map_one`, rewrite `1` as `C 1`, then `seriesEval_C`.
- Hypotheses: none.
- Uses from project: [evalPi, seriesEval_C]
- Used by: `evalPi_pow`, `evalPiHom`, `evalPi_one_add_X_pow`, `exists_evalPi_eq` (`hinv`).
- Visibility: public (simp)
- Lines: 116-119 (proof 2 lines)
- Notes: none

### theorem evalPi_X
- Type: `@[simp] theorem evalPi_X (n : ℕ) : evalPi p (PowerSeries.X) n = pi p n`
- What: The monomial `X` evaluates to `π_n`.
- How: `map_X`, then `tsum_eq_single 1` (only the degree-1 term survives), `coeff_one_X`, `pow_one`.
- Hypotheses: none.
- Uses from project: [evalPi, pi, seriesEval]
- Used by: `evalPi_one_add_X_pow`.
- Visibility: public (simp)
- Lines: 122-126 (proof 3 lines)
- Notes: none

### theorem evalPi_pow
- Type: `theorem evalPi_pow (f) (k : ℕ) {n} (hn : 1 ≤ n) : evalPi p (f ^ k) n = evalPi p f n ^ k`
- What: Evaluation commutes with taking powers, for `n ≥ 1`.
- How: Induction on `k`; base via `evalPi_one`, step via `pow_succ` + `evalPi_mul`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, evalPi_one, evalPi_mul]
- Used by: `evalPi_one_add_X_pow`.
- Visibility: public
- Lines: 129-133 (proof 4 lines)
- Notes: none

### theorem finiteDimensional_K
- Type: `private theorem finiteDimensional_K (n : ℕ) : FiniteDimensional ℚ_[p] (K p n)`
- What: `K_n = ℚ_p(ξ_{p^n})` is finite-dimensional over `ℚ_p`.
- How: `ξ_{p^n}` is integral (root of `X^{p^n} − 1`, monic, via `zetaSys_primitiveRoot.pow_eq_one`), then `IntermediateField.adjoin.finiteDimensional`.
- Hypotheses: none.
- Uses from project: [zetaSys_primitiveRoot, zetaSys, K]
- Used by: `isClosed_K`.
- Visibility: private
- Lines: 140-146 (proof 6 lines)
- Notes: re-derives locally because the Tower instance is private.

### theorem isClosed_K
- Type: `private theorem isClosed_K (n : ℕ) : IsClosed (X := ℂ_[p]) (K p n : Set ℂ_[p])`
- What: `K_n` is a closed subset of `ℂ_p`.
- How: A finite-dim `ℚ_p`-subspace of a normed space over complete `ℚ_p` is complete hence closed (`Submodule.closed_of_finiteDimensional`, using `finiteDimensional_K`).
- Hypotheses: none.
- Uses from project: [K, finiteDimensional_K]
- Used by: `evalPi_mem_O`.
- Visibility: private
- Lines: 151-153 (proof 2 lines)
- Notes: none

### theorem evalPi_partialSum_mem_K
- Type: `private theorem evalPi_partialSum_mem_K (f) (n m : ℕ) : (∑ k ∈ range m, coeff k (map (toCp p) f) * pi p n ^ k) ∈ K p n`
- What: Finite partial sums of the evaluation series lie in `K_n`.
- How: `sum_mem`/`mul_mem`/`pow_mem`: each coefficient is `algebraMap`-image (so in `K_n`, via `IntermediateField.algebraMap_mem`), each `π_n^k ∈ K_n` (`pi_mem_K`).
- Hypotheses: none.
- Uses from project: [toCp, pi, K, pi_mem_K]
- Used by: `evalPi_mem_O`.
- Visibility: private
- Lines: 158-162 (proof 4 lines)
- Notes: none

### theorem evalPi_mem_O
- Type: `theorem evalPi_mem_O (f) {n} (hn : 1 ≤ n) : evalPi p f n ∈ O p n`
- What: **Integrality**: `f(π_n) ∈ 𝒪_n` for `n ≥ 1`.
- How: Two halves. `f(π_n) ∈ K_n`: limit of `K_n`-valued partial sums in the closed set `K_n` (`isClosed_K.mem_of_tendsto`, `hasSum.tendsto_sum_nat`, `evalPi_partialSum_mem_K`). `‖f(π_n)‖ ≤ 1`: ultrametric `tsum` bound `IsUltrametricDist.norm_tsum_le_of_forall_le`, each term `≤ 1·1`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, O, isClosed_K, summable_evalPi, evalPi_partialSum_mem_K, seriesEval, norm_coeff_map_le_one, pi, norm_pi_lt_one]
- Used by: `evalPiES`, `norm_evalPi_sub_le_of_modEqPow`, `leftMulMatrix_zetaBasis_coe`, `evalPi_normOp`.
- Visibility: public
- Lines: 167-183 (proof 17 lines)
- Notes: none

### theorem one_add_pi_pow_sub_one
- Type: `private theorem one_add_pi_pow_sub_one (n : ℕ) : (1 + pi p (n + 1)) ^ p - 1 = pi p n`
- What: The value identity `(1 + π_{n+1})^p − 1 = π_n` behind the `φ`-step.
- How: `1 + π_{n+1} = ξ_{p^{n+1}}` (uniformiser def) and `ξ_{p^{n+1}}^p = ξ_{p^n}` (`zetaSys_pow_p`), so value is `ξ_{p^n} − 1 = π_n`.
- Hypotheses: none.
- Uses from project: [pi, zetaSys, zetaSys_pow_p]
- Used by: `evalPi_phi`.
- Visibility: private
- Lines: 190-193 (proof 3 lines)
- Notes: none

### theorem evalPi_phi
- Type: `theorem evalPi_phi (f) {n} (hn : 1 ≤ n) : evalPi p (phiSeries p f) (n + 1) = evalPi p f n`
- What: **`φ`-equivariance** (RJW eq. (φ-π_n)): `φ(f)(π_{n+1}) = f(π_n)` for the Frobenius substitution `φ`. Engine of inverse-limit compatibility.
- How: `map toCp` commutes with `φ` (`map_phiSeries`); the `K`-native `φ`-bridge `seriesEval_phi_of_summable_prod` rewrites to evaluation of `map toCp f` at `(1+π_{n+1})^p−1 = π_n` (`one_add_pi_pow_sub_one`); convergence via `summable_prod_of_norm_coeff_le_one`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, phiSeries, map_phiSeries, seriesEval_phi_of_summable_prod, toCp, pi, norm_coeff_map_le_one, norm_pi_lt_one, summable_prod_of_norm_coeff_le_one, one_add_pi_pow_sub_one]
- Used by: `evalPi_digitMatrix_col`.
- Visibility: public
- Lines: 204-212 (proof 7 lines)
- Notes: none

### theorem evalPi_C
- Type: `@[simp] theorem evalPi_C (a : ℤ_[p]) (n : ℕ) : evalPi p (PowerSeries.C a) n = toCp p a`
- What: The constant series `C a` evaluates to its pushed-forward constant `toCp a`.
- How: `map_C` then `seriesEval_C`; no convergence needed.
- Hypotheses: none.
- Uses from project: [evalPi, toCp, seriesEval_C]
- Used by: `evalPi_injective` (`heval`), `norm_evalPi_sub_le_of_modEqPow`.
- Visibility: public (simp)
- Lines: 226-227 (proof 1 line)
- Notes: none

### theorem evalPi_coe_polynomial
- Type: `private theorem evalPi_coe_polynomial (q : Polynomial ℤ_[p]) (n : ℕ) : evalPi p (q : PowerSeries ℤ_[p]) n = (q.map (toCp p)).eval (pi p n)`
- What: For a polynomial coerced to a power series, `evalPi` equals the genuine `Polynomial.eval` of the mapped polynomial.
- How: `polynomial_map_coe`; `tsum_eq_sum` over `range (natDegree+1)` (higher coeffs vanish by `coeff_eq_zero_of_natDegree_lt`); `Polynomial.eval_eq_sum_range`.
- Hypotheses: none.
- Uses from project: [evalPi, toCp, pi, seriesEval]
- Used by: `evalPi_injective` (`hr0`).
- Visibility: private
- Lines: 233-241 (proof 6 lines)
- Notes: none

### theorem pi_norm_injective
- Type: `private theorem pi_norm_injective {n m} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : ‖pi p n‖ = ‖pi p m‖) : n = m`
- What: The uniformisers have **distinct norms**, so `n ↦ ‖π_n‖` is injective for `n ≥ 1`.
- How: `by_contra` + `wlog n < m`; raise both to the strictly larger totient `φ(p^m)`, use `norm_pi_pow_totient` (`= p⁻¹`) and strict monotonicity of `φ` on `p`-powers (`Nat.totient_prime_pow`, `Nat.pow_lt_pow_right`); a smaller base raised to a larger exponent is strictly smaller (`pow_lt_pow_right_of_lt_one₀`) — contradiction.
- Hypotheses: `n ≥ 1`, `m ≥ 1`, equal norms.
- Uses from project: [pi, pi_ne_zero, norm_pi_pow_totient, norm_pi_lt_one]
- Used by: `evalPi_injective`.
- Visibility: private
- Lines: 248-263 (proof 14 lines)
- Notes: none

### theorem exists_C_pow_mul
- Type: `private theorem exists_C_pow_mul (d) (hd : d ≠ 0) : ∃ (m) (d'), d = C (p^m) * d' ∧ ∃ k, ¬ p ∣ coeff k d'`
- What: **`p`-power normalisation**: a nonzero `d` is `C(p^m)·d'` with some coefficient of `d'` not divisible by `p` (the hypothesis Weierstrass preparation needs).
- How: `m := sInf` of valuations over nonzero coefficients (`Nat.sInf_mem`); each coeff is `p^m`-divisible (`PadicInt.mem_span_pow_iff_le_valuation` + `Nat.sInf_le`); divide coefficient-wise via `Classical.choice` dvd-witnesses (`(hdvd k).choose`); the minimal-valuation coefficient is not `p`-divisible (else valuation `≥ m+1`, contradicting minimality via `omega`).
- Hypotheses: `d ≠ 0`.
- Uses from project: []
- Used by: `evalPi_injective`.
- Visibility: private
- Lines: 271-298 (proof 28 lines)
- Notes: long(30-50)? No — 28 lines; uses `classical`.

### theorem evalPi_injective
- Type: `theorem evalPi_injective {f g} (h : ∀ n, 1 ≤ n → evalPi p f n = evalPi p g n) : f = g`
- What: **Uniqueness of the interpolating series** (RJW lem:unique-coleman): a `ℤ_p`-power series is determined by its values at the `π_n`, `n ≥ 1`.
- How: The source's Weierstrass argument. `by_contra`; set `d := f − g ≠ 0`, so `d(π_n) = 0` (`evalPi_sub`). Normalise `d = C(p^m)·d'` (`exists_C_pow_mul`); show `d' mod p ≠ 0` via the residue map (`IsLocalRing.residue_eq_zero_iff`, `PadicInt.maximalIdeal_eq_span_p`); apply mathlib Weierstrass preparation `PowerSeries.exists_isWeierstrassFactorization` to get `d' = r·u`, `r` distinguished monic, `u` a unit. Evaluate: `toCp(p^m) ≠ 0` and `u(π_n) ≠ 0` peel off (unit value invertible), so `r.map toCp` (nonzero, monic) vanishes at every `π_n`. The `π_{n+1}` are infinitely many distinct points (`pi_norm_injective` + `Set.infinite_of_injective_forall_mem`), forcing `r' = 0` (`Polynomial.eq_zero_of_infinite_isRoot`) — contradiction.
- Hypotheses: `f`, `g` agree at all `π_n` for `n ≥ 1`.
- Uses from project: [evalPi, evalPi_sub, exists_C_pow_mul, evalPi_mul, evalPi_C, evalPi_coe_polynomial, pi, pi_norm_injective, toCp]
- Used by: `coleman_existsUnique` (uniqueness + `𝒩`-invariance), `colemanSeries_mul`, `colemanSeries_eq_iff`.
- Visibility: public
- Lines: 313-356 (proof 44 lines)
- Notes: **long(30-50)** — 44-line proof; mathlib Weierstrass preparation `exists_isWeierstrassFactorization` is the hinge.

### theorem quot_mem_O
- Type: `private theorem quot_mem_O {n} (hn : 1 ≤ n) {r : ℂ_[p]} (hr : r ∈ O p n) (a : ℤ_[p]) (hres : ‖r - toCp p a‖ ≤ ‖pi p n‖) : (r - toCp p a) / pi p n ∈ O p n`
- What: The greedy-step remainder `(r − a)/π_n` stays in `𝒪_n`.
- How: `K_n`-membership since `K_n` is a field and `π_n ≠ 0` (`div_mem`, `pi_mem_K`); norm `≤ 1` since `‖r − a‖ ≤ ‖π_n‖` (`norm_div`, `div_le_one`).
- Hypotheses: `n ≥ 1`, `r ∈ 𝒪_n`, `‖r − a‖ ≤ ‖π_n‖`.
- Uses from project: [O, K, toCp, pi, pi_mem_K, pi_ne_zero]
- Used by: `exists_evalPi_eq` (the `seq` recursion).
- Visibility: private
- Lines: 375-384 (proof 9 lines)
- Notes: none

### theorem term_norm_le_pi
- Type: `private theorem term_norm_le_pi {n} (hn : 1 ≤ n) (q : ℚ_[p]) {i} (hi1 : 1 ≤ i) (hiM : i < totient (p^n)) (hle : ‖q‖ * ‖pi p n‖ ^ i ≤ 1) : ‖q‖ * ‖pi p n‖ ^ i ≤ ‖pi p n‖`
- What: A `≤ 1` term `‖q‖·‖π_n‖^i` (with `1 ≤ i < φ(p^n)`) of the orthogonal expansion is in fact `≤ ‖π_n‖`.
- How: Raise to `M = φ(p^n)`; write `‖q‖ = p^k` (`Padic.norm_eq_zpow_neg_valuation`) and `‖π_n‖^M = p⁻¹` (`norm_pi_pow_totient`); the inequality becomes `kM − i ≤ 0`, and `1 ≤ i < M` forces `k ≤ 0` hence `kM − i ≤ −1` (`nlinarith`); convert back via `le_of_pow_le_pow_left₀`.
- Hypotheses: `n ≥ 1`, `1 ≤ i < φ(p^n)`, term `≤ 1`.
- Uses from project: [pi, norm_pi_pow_totient, pi_ne_zero]
- Used by: `exists_residue_pi`.
- Visibility: private
- Lines: 390-416 (proof 27 lines)
- Notes: none

### theorem term_norm_distinct
- Type: `private theorem term_norm_distinct {n} (hn : 1 ≤ n) {qa qb} {a b} (ha : a < totient (p^n)) (hb : b < totient (p^n)) (hab : a ≠ b) (hqa : qa ≠ 0) (hqb : qb ≠ 0) : ‖qa‖ * ‖pi p n‖ ^ a ≠ ‖qb‖ * ‖pi p n‖ ^ b`
- What: Distinct terms of the orthogonal expansion (nonzero `ℚ_p`-coeffs) have **distinct norms** (the orthogonality input).
- How: Raise to `M = φ(p^n)`; both become `p^{Mv−exp}`; equality forces `(v_a − v_b)M = a − b`, impossible for `a ≠ b` with `|a−b| < M` (`zpow_right_injective₀`, then case `ka − kb = 0` vs `|·M| ≥ M`, `omega`).
- Hypotheses: `n ≥ 1`, `a,b < φ(p^n)`, `a ≠ b`, both coeffs nonzero.
- Uses from project: [pi, norm_pi_pow_totient]
- Used by: `exists_residue_pi` (`hdistinct`).
- Visibility: private
- Lines: 422-456 (proof 35 lines)
- Notes: **long(30-50)** — 35-line proof; hinges on `zpow_right_injective₀`.

### theorem exists_residue_pi
- Type: `theorem exists_residue_pi {n} (hn : 1 ≤ n) {x : ℂ_[p]} (hx : x ∈ K p n) (hxnorm : ‖x‖ ≤ 1) : ∃ a : ℤ_[p], ‖x - toCp p a‖ ≤ ‖pi p n‖`
- What: **The residue step** (RJW TeX 2542-2547): every `x ∈ 𝒪_n` is `≡ a mod π_n` for some `a : ℤ_p`.
- How: `K_n = ℚ_p(π_n)` (`hKeq`); `π_n` integral. Use the power basis `pb := adjoin.powerBasis hint` of dim `φ(p^n)` (`finrank_K`); expand `x = Σ tm i` via `Basis.sum_repr` (`hexp`); terms have pairwise distinct norms (`term_norm_distinct`), so ultrametric orthogonality `IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne` gives each term `≤ ‖x‖ ≤ 1` (`hperterm`, `hterm_le_one`); constant coeff `q_0 ∈ ℤ_p` (`a`), tail bounded `≤ ‖π_n‖` termwise (`term_norm_le_pi`, `norm_sum_le_of_forall_le_of_nonneg`).
- Hypotheses: `n ≥ 1`, `x ∈ K_n`, `‖x‖ ≤ 1`.
- Uses from project: [K, toCp, pi, zetaSys_primitiveRoot, zetaSys, finrank_K, term_norm_distinct, term_norm_le_pi]
- Used by: `exists_evalPi_eq` (the residue oracle).
- Visibility: public (promoted from private for `Iwasawa/ResidueField.lean`)
- Lines: 458-565 (proof ~89 lines, decl 474-565)
- Notes: **OVER-50** (needs /decompose-proof) — ~89-line proof; `set_option synthInstance.maxHeartbeats 1000000`, `set_option maxHeartbeats 1000000`; uses `classical`.

### theorem exists_evalPi_eq
- Type: `theorem exists_evalPi_eq {n} (hn : 1 ≤ n) {u : ℂ_[p]} (hu : u ∈ O p n) (hnorm : ‖u‖ = 1) : ∃ f : PowerSeries ℤ_[p], IsUnit f ∧ evalPi p f n = u`
- What: **Single-level interpolation** (RJW TeX 2538-2547, T904b): every norm-one `u ∈ 𝒪_n` is `f(π_n)` for a unit `f ∈ ℤ_p⟦T⟧^×`.
- How: Source's greedy `π_n`-adic digits. Residue oracle from `exists_residue_pi`; `Nat.rec` remainder/digit recursion `seq` carrying `r_k ∈ 𝒪_n` (`quot_mem_O`), digits `a_k`. Telescoping `u − Σ_{j<m} a_j π_n^j = π_n^m·r_m` (`htel`, induction, `linear_combination`). Unit: `‖u − a_0‖ < 1 = ‖u‖`, ultrametric isoceles (`norm_add_eq_max_of_norm_ne_norm`) gives `‖a_0‖ = 1`, so `constantCoeff f` is a `ℤ_p`-unit (`PowerSeries.isUnit_iff_constantCoeff`, `PadicInt.isUnit_iff`). Interpolation: partial sums tend to `u` (telescoping, `‖π_n‖^m → 0`) and to `f(π_n)` (`hasSum.tendsto_sum_nat`), so equal by `tendsto_nhds_unique`.
- Hypotheses: `n ≥ 1`, `u ∈ 𝒪_n`, `‖u‖ = 1`.
- Uses from project: [O, evalPi, pi, pi_ne_zero, exists_residue_pi, quot_mem_O, toCp, norm_toCp, norm_pi_lt_one, summable_evalPi]
- Used by: `coleman_existsUnique` (per-level interpolants, step (a)).
- Visibility: public
- Lines: 578-653 (proof ~75 lines)
- Notes: **OVER-50** (needs /decompose-proof) — ~75-line proof; uses `classical`.

### def evalPiHom
- Type: `noncomputable def evalPiHom {n} (hn : 1 ≤ n) : PowerSeries ℤ_[p] →+* ℂ_[p]`
- What: Evaluation `f ↦ f(π_n)` bundled as a ring homomorphism (for `n ≥ 1`), enabling `RingHom.map_det`/`map_sum` to transport det/Σ through evaluation.
- How: Fields from the evaluation pack: `map_one' = evalPi_one`, `map_mul' = evalPi_mul`, `map_add' = evalPi_add`, `map_zero'` from `map_zero`/`seriesEval`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, evalPi_one, evalPi_mul, evalPi_add, seriesEval]
- Used by: `evalPiHom_apply`, `evalPi_digitMatrix_col`, `leftMulMatrix_zetaBasis_coe`, `evalPi_normOp`.
- Visibility: public
- Lines: 680-685 (def body 5 lines)
- Notes: `variable {p}` from line 675 onward.

### theorem evalPiHom_apply
- Type: `@[simp] theorem evalPiHom_apply {n} (hn : 1 ≤ n) (f) : evalPiHom hn f = evalPi p f n`
- What: The bundled hom applies as `evalPi`.
- How: `rfl`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPiHom, evalPi]
- Used by: `evalPi_digitMatrix_col`, `leftMulMatrix_zetaBasis_coe`, `evalPi_normOp`.
- Visibility: public (simp)
- Lines: 688-689 (proof rfl)
- Notes: none

### theorem evalPi_one_add_X_pow
- Type: `theorem evalPi_one_add_X_pow (i : ℕ) {n} (hn : 1 ≤ n) : evalPi p ((1 + X)^i) n = zetaSys p n ^ i`
- What: `(1+T)^i` evaluates to `(1+π_n)^i = ξ_n^i` at `π_n`, for `n ≥ 1`.
- How: `evalPi_pow`, `evalPi_add`, `evalPi_one`, `evalPi_X`, and `1 + π_n = ξ_n` (`pi` def).
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, evalPi_pow, evalPi_add, evalPi_one, evalPi_X, pi, zetaSys]
- Used by: `evalPi_digitMatrix_col`.
- Visibility: public
- Lines: 692-695 (proof 3 lines)
- Notes: none

### theorem evalPi_digitMatrix_col
- Type: `theorem evalPi_digitMatrix_col (f) (j : Fin p) {n} (hn : 1 ≤ n) : evalPi p f (n+1) * zetaSys p (n+1)^(j:ℕ) = ∑ i : Fin p, evalPi p ((digitMatrix f) i j) n * zetaSys p (n+1)^(i:ℕ)`
- What: **The evaluated digit identity** (T907 crux): the matrix `(evalPi (M_ij) n)` is the multiplication-by-`y` matrix (`y := evalPi f (n+1)`) in the `ξ_{n+1}`-power basis of `K_{n+1}/K_n`.
- How: Apply `evalPiHom` to the formal column identity `digitMatrix_col_isDigitDecomp`; `map_mul`/`map_sum`; `evalPi_one_add_X_pow` for the `ξ`-powers; `φ`-equivariance `evalPi_phi` converts `φ(M_ij)(π_{n+1}) = M_ij(π_n)`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, zetaSys, digitMatrix, evalPiHom, digitMatrix_col_isDigitDecomp, evalPiHom_apply, evalPi_one_add_X_pow, evalPi_phi]
- Used by: `leftMulMatrix_zetaBasis_coe`.
- Visibility: public
- Lines: 703-713 (proof 11 lines)
- Notes: none

### def zetaPow
- Type: `private noncomputable def zetaPow {n} (i : Fin p) : IntermediateField.extendScalars (K_le_succ p n)`
- What: The basis vector `ξ_{n+1}^i ∈ extendScalars (K_n ≤ K_{n+1})` (`i < p`).
- How: `⟨zetaSys p (n+1)^i, mem_extendScalars … (pow_mem (zetaSys_mem_K …))⟩`.
- Hypotheses: none.
- Uses from project: [K_le_succ, zetaSys, zetaSys_mem_K]
- Used by: `zetaPow_coe`, `linearIndependent_zetaPow`, `zetaBasis`, `zetaBasis_apply`.
- Visibility: private
- Lines: 726-730 (def body 3 lines)
- Notes: none

### theorem zetaPow_coe
- Type: `@[simp] private theorem zetaPow_coe {n} (i : Fin p) : ((zetaPow i : extendScalars …) : ℂ_[p]) = zetaSys p (n+1)^(i:ℕ)`
- What: The `ℂ_p`-coercion of `zetaPow i` is `ξ_{n+1}^i`.
- How: `rfl`.
- Hypotheses: none.
- Uses from project: [zetaPow, K_le_succ, zetaSys]
- Used by: `linearIndependent_zetaPow`, `leftMulMatrix_zetaBasis_coe`.
- Visibility: private (simp)
- Lines: 733-735 (proof rfl)
- Notes: none

### theorem linearIndependent_zetaPow
- Type: `private theorem linearIndependent_zetaPow {n} (hn : 1 ≤ n) : LinearIndependent (K p n) (zetaPow (n := n))`
- What: `K_n`-linear independence of the `ξ_{n+1}`-powers (the uniqueness half of T903b, repackaged).
- How: `Fintype.linearIndependent_iff`; project a relation to `ℂ_p` with `K_n`-coefficients (`hproj`), then `O_succ_digits_unique` (comparing to the all-zero coefficients) forces all `e k = 0`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [K, zetaPow, zetaPow_coe, zetaSys, O_succ_digits_unique]
- Used by: `zetaBasis`.
- Visibility: private
- Lines: 739-753 (proof 13 lines)
- Notes: none

### def zetaBasis
- Type: `private noncomputable def zetaBasis {n} (hn : 1 ≤ n) : Module.Basis (Fin p) (K p n) (extendScalars (K_le_succ p n))`
- What: The `ξ_{n+1}`-power `K_n`-basis of `K_{n+1}` (a linearly independent family of cardinality `p = [K_{n+1}:K_n]`).
- How: `basisOfLinearIndependentOfCardEqFinrank` from `linearIndependent_zetaPow` with `card = finrank` via `finrank_K_succ`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [K, K_le_succ, linearIndependent_zetaPow, finrank_K_succ]
- Used by: `zetaBasis_apply`, `leftMulMatrix_zetaBasis_coe`, `evalPi_normOp`.
- Visibility: private
- Lines: 760-764 (def body 3 lines)
- Notes: `set_option synthInstance.maxHeartbeats 1000000`.

### theorem zetaBasis_apply
- Type: `@[simp] private theorem zetaBasis_apply {n} (hn : 1 ≤ n) (i : Fin p) : zetaBasis hn i = zetaPow (n := n) i`
- What: The basis evaluates to `zetaPow i`.
- How: Unfold `zetaBasis`; `coe_basisOfLinearIndependentOfCardEqFinrank`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [zetaBasis, zetaPow]
- Used by: `leftMulMatrix_zetaBasis_coe`.
- Visibility: private (simp)
- Lines: 769-771 (proof 1 line)
- Notes: `set_option synthInstance.maxHeartbeats 1000000`.

### def evalPiES
- Type: `private noncomputable def evalPiES (f) {n} (hn : 1 ≤ n) : IntermediateField.extendScalars (K_le_succ p n)`
- What: `evalPi f (n+1)` packaged as an element of `extendScalars` (i.e. of `K_{n+1}` over `K_n`).
- How: `⟨evalPi p f (n+1), mem_extendScalars … (evalPi_mem_O …).1⟩`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [K_le_succ, evalPi, evalPi_mem_O]
- Used by: `leftMulMatrix_zetaBasis_coe`, `evalPi_normOp`.
- Visibility: private
- Lines: 774-777 (def body 3 lines)
- Notes: none

### theorem leftMulMatrix_zetaBasis_coe
- Type: `private theorem leftMulMatrix_zetaBasis_coe (f) {n} (hn : 1 ≤ n) (i j : Fin p) : ((leftMulMatrix (zetaBasis hn) (evalPiES f hn) i j : K p n) : ℂ_[p]) = evalPi p ((digitMatrix f) i j) n`
- What: **Matrix-entry identification** (T907 crux): the multiplication-by-`evalPi f (n+1)` matrix in the `ξ_{n+1}`-power basis has entries exactly `evalPi (M_ij) n`.
- How: Set `a_i := ⟨evalPi (M_ij) n, …⟩ ∈ K_n` (integral via `evalPi_mem_O`); show `y·b_j = Σ a_i • b_i` in extendScalars (project to `ℂ_p`, apply `evalPi_digitMatrix_col`); then `Algebra.leftMulMatrix_eq_repr_mul` + `Basis.repr_sum_self`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [K, evalPi, evalPi_mem_O, evalPiES, zetaBasis, zetaBasis_apply, zetaPow_coe, evalPi_digitMatrix_col, digitMatrix]
- Used by: `evalPi_normOp`.
- Visibility: private
- Lines: 786-802 (proof 17 lines)
- Notes: `set_option synthInstance.maxHeartbeats 1000000`.

### theorem evalPi_normOp
- Type: `theorem evalPi_normOp (f) {n} (hn : 1 ≤ n) : evalPi p (normOp f) n = levelNorm p n (evalPi p f (n + 1))`
- What: **The evaluation/norm commuting square** (T907, RJW lem:norm power series vs units): evaluating the norm operator at `π_n` equals the level-norm of the value at `π_{n+1}`. No `p`-odd hypothesis needed.
- How: Determinant route (R10.4). `normOp_eq_det`, then `RingHom.map_det` pushes `evalPiHom` through the determinant; the mapped matrix agrees entrywise (`hmat`, via `leftMulMatrix_zetaBasis_coe`) with the `K_n ↪ ℂ_p`-image of the multiplication matrix, whose det is `Algebra.norm` (`Algebra.norm_eq_matrix_det`); finally `levelNorm_apply`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [evalPi, normOp, levelNorm, evalPi_mem_O, K, evalPiHom, evalPiHom_apply, digitMatrix, zetaBasis, evalPiES, leftMulMatrix_zetaBasis_coe, normOp_eq_det, levelNorm_apply]
- Used by: `coleman_existsUnique` (steps (b), (f)), `colemanSeries`/uniqueness chain indirectly.
- Visibility: public
- Lines: 815-830 (proof 16 lines)
- Notes: `set_option synthInstance.maxHeartbeats 1000000`.

### theorem norm_elems_eq_one
- Type: `private theorem norm_elems_eq_one (u : NormCompatUnits p) (n : ℕ) : ‖(u.elems n : ℂ_[p])‖ = 1`
- What: For a member of `𝒰_∞`, the level-`n` unit value has norm exactly `1`.
- How: `‖u_n‖ ≤ 1` and `‖u_n⁻¹‖ ≤ 1` (membership in `𝒪_n`); `u_n·u_n⁻¹ = 1` gives `‖u_n‖·‖u_n⁻¹‖ = 1`; `nlinarith`.
- Hypotheses: none beyond a `NormCompatUnits`.
- Uses from project: [NormCompatUnits, O]
- Used by: `coleman_existsUnique` (step (a)).
- Visibility: private
- Lines: 858-865 (proof 7 lines)
- Notes: `variable (p)` restored at line 853.

### theorem norm_evalPi_sub_le_of_modEqPow
- Type: `theorem norm_evalPi_sub_le_of_modEqPow {m} {f g} (hfg : ModEqPow p (m+1) f g) {n} (hn : 1 ≤ n) : ‖evalPi p f n - evalPi p g n‖ ≤ ((p:ℝ)⁻¹)^(m+1)`
- What: **The mod-`p^{m+1}` evaluation bridge** (the (d)-step proximity): a congruence `f ≡ g mod p^{m+1}` pushes to `‖f(π_n) − g(π_n)‖ ≤ p^{−(m+1)}`.
- How: Write `f − g = C(p^{m+1})·h` (`modEqPow_iff_exists_C_mul`); `evalPi_sub`/`evalPi_mul`/`evalPi_C` give `f(π_n) − g(π_n) = toCp(p^{m+1})·h(π_n)`; `‖toCp(p^{m+1})‖ = p^{−(m+1)}` (`norm_toCp`, `PadicInt.norm_p`) and `‖h(π_n)‖ ≤ 1` (`evalPi_mem_O`).
- Hypotheses: `f ≡ g mod p^{m+1}`, `n ≥ 1`.
- Uses from project: [evalPi, ModEqPow, modEqPow_iff_exists_C_mul, evalPi_sub, evalPi_mul, evalPi_C, toCp, norm_toCp, evalPi_mem_O]
- Used by: `coleman_existsUnique` (step (d), `hbound`).
- Visibility: public
- Lines: 872-882 (proof 11 lines)
- Notes: none

### theorem tendsto_evalPi_of_tendsto
- Type: `theorem tendsto_evalPi_of_tendsto {g : ℕ → PowerSeries ℤ_[p]} {h} (hg : Tendsto g atTop (nhds h)) {n} (hn : 1 ≤ n) : Tendsto (fun j => evalPi p (g j) n) atTop (nhds (evalPi p h n))`
- What: **The evaluation-continuity bridge** (T909-feeding): coefficientwise (Pi-topology) convergence `g_j → h` forces `g_j(π_n) → h(π_n)`, for `n ≥ 1`.
- How: Honest ultrametric `max`-argument. For `ε`, pick `N` with `‖π_n‖^N < ε`; the head `Σ_{k<N}‖coeff_k(g_j − h)‖ → 0` (finitely many coeffs converge, `tendsto_coeff` + `tendsto_finsetSum`); the difference is the `tsum`, each term `≤ max(head-sum, ‖π_n‖^N)` (`IsUltrametricDist.norm_tsum_le_of_forall_le`), and that max `< ε` eventually.
- Hypotheses: `g_j → h` in Pi-topology, `n ≥ 1`.
- Uses from project: [evalPi, pi, norm_pi_lt_one, evalPi_sub, seriesEval, toCp, norm_toCp, tendsto_coeff]
- Used by: `coleman_existsUnique` (step (d), `hlimA`).
- Visibility: public
- Lines: 892-956 (proof ~65 lines)
- Notes: **OVER-50** (needs /decompose-proof) — ~65-line proof; `open scoped PowerSeries.WithPiTopology`.

### theorem coleman_existsUnique
- Type: `theorem coleman_existsUnique (u : NormCompatUnits p) : ∃! f : PowerSeries ℤ_[p], IsUnit f ∧ normOp f = f ∧ ∀ n, 1 ≤ n → evalPi p f n = (u.elems n : ℂ_[p])`
- What: **Coleman's theorem** (T910, RJW thm:coleman power series / thm:coleman map 2): for every norm-compatible system `u ∈ 𝒰_∞`, a *unique* `𝒩`-invariant unit power series `f` interpolates `u` (`f(π_n) = u_n`, `n ≥ 1`).
- How: Uniqueness is Weierstrass `evalPi_injective`. Existence is the diagonal/compactness argument: (a) per-level interpolants `F_m` (`exists_evalPi_eq`, `norm_elems_eq_one`); (b) `𝒩^[k] F_{n+k}(π_n) = u_n` by induction via `evalPi_normOp` + `u.compat`; (c) diagonal `g_m := 𝒩^[m] F_{2m}`, convergent subsequence `g_{φ j} → f_u` (`exists_subseq_tendsto`); (d) `f_u(π_n) = u_n` via `tendsto_evalPi_of_tendsto` (limit A) and a squeeze using `normOp_iterate_modEq` + `norm_evalPi_sub_le_of_modEqPow` (limit B), `tendsto_nhds_unique`; (e) `IsUnit f_u` (`normOp_iterate_isUnit`, `isClosed_isUnit.mem_of_tendsto`); (f) `𝒩 f_u = f_u` via `evalPi_injective`.
- Hypotheses: `u : NormCompatUnits p`.
- Uses from project: [NormCompatUnits, evalPi, normOp, evalPi_injective, exists_evalPi_eq, norm_elems_eq_one, evalPi_normOp, tendsto_evalPi_of_tendsto, norm_evalPi_sub_le_of_modEqPow, exists_subseq_tendsto, normOp_iterate_isUnit, normOp_iterate_modEq, isClosed_isUnit, pi, norm_pi_lt_one]
- Used by: `colemanSeries`, `colemanSeries_isUnit`, `normOp_colemanSeries`, `evalPi_colemanSeries`, `colemanSeries_mul`, `colemanSeries_eq_iff`.
- Visibility: public
- Lines: 981-1060 (proof ~80 lines)
- Notes: **OVER-50** (needs /decompose-proof) — ~80-line proof; uses `classical`.

### def colemanSeries
- Type: `noncomputable def colemanSeries (u : NormCompatUnits p) : PowerSeries ℤ_[p]`
- What: **The Coleman series** of `u ∈ 𝒰_∞`: the unique `𝒩`-invariant unit power series interpolating `u`.
- How: `(coleman_existsUnique p u).choose`.
- Hypotheses: `u : NormCompatUnits p`.
- Uses from project: [NormCompatUnits, coleman_existsUnique]
- Used by: `colemanSeries_isUnit`, `normOp_colemanSeries`, `evalPi_colemanSeries`, `colemanSeries_mul`, `colemanSeries_eq_iff`.
- Visibility: public
- Lines: 1065-1066 (def body 1 line)
- Notes: none

### theorem colemanSeries_isUnit
- Type: `theorem colemanSeries_isUnit (u : NormCompatUnits p) : IsUnit (colemanSeries p u)`
- What: `colemanSeries u` is a unit.
- How: First clause of `coleman_existsUnique`'s `choose_spec`.
- Hypotheses: `u : NormCompatUnits p`.
- Uses from project: [NormCompatUnits, colemanSeries, coleman_existsUnique]
- Used by: `colemanSeries_mul`, `colemanSeries_eq_iff`.
- Visibility: public
- Lines: 1069-1070 (proof 1 line)
- Notes: none

### theorem normOp_colemanSeries
- Type: `theorem normOp_colemanSeries (u : NormCompatUnits p) : normOp (colemanSeries p u) = colemanSeries p u`
- What: `colemanSeries u` is `𝒩`-invariant.
- How: Second clause of `coleman_existsUnique`'s `choose_spec`.
- Hypotheses: `u : NormCompatUnits p`.
- Uses from project: [NormCompatUnits, normOp, colemanSeries, coleman_existsUnique]
- Used by: `colemanSeries_mul`, `colemanSeries_eq_iff`.
- Visibility: public
- Lines: 1073-1075 (proof 1 line)
- Notes: none

### theorem evalPi_colemanSeries
- Type: `theorem evalPi_colemanSeries (u : NormCompatUnits p) {n} (hn : 1 ≤ n) : evalPi p (colemanSeries p u) n = (u.elems n : ℂ_[p])`
- What: `colemanSeries u` interpolates `u`: value `u_n` at `π_n` for `n ≥ 1`.
- How: Third clause of `coleman_existsUnique`'s `choose_spec`.
- Hypotheses: `u : NormCompatUnits p`, `n ≥ 1`.
- Uses from project: [NormCompatUnits, evalPi, colemanSeries, coleman_existsUnique]
- Used by: `colemanSeries_mul`, `colemanSeries_eq_iff`.
- Visibility: public
- Lines: 1079-1081 (proof 1 line)
- Notes: none

### theorem colemanSeries_mul
- Type: `theorem colemanSeries_mul (u v : NormCompatUnits p) : colemanSeries p (u * v) = colemanSeries p u * colemanSeries p v`
- What: **Multiplicativity of the Coleman map** (RJW thm:coleman map 2): `u ↦ colemanSeries u` is a homomorphism.
- How: The product `colemanSeries u · colemanSeries v` satisfies all three defining clauses of `coleman_existsUnique (u·v)` (`IsUnit.mul`, `normOp_mul`, `evalPi_mul` against `(u·v).elems n = u_n·v_n`), so it equals `colemanSeries (u·v)` by `(coleman_existsUnique …).unique`.
- Hypotheses: `u, v : NormCompatUnits p`.
- Uses from project: [NormCompatUnits, colemanSeries, coleman_existsUnique, colemanSeries_isUnit, normOp, normOp_mul, normOp_colemanSeries, evalPi_mul, evalPi_colemanSeries]
- Used by: unused in file.
- Visibility: public
- Lines: 1088-1098 (proof 9 lines)
- Notes: none

### theorem NormCompatUnits.ext
- Type: `@[ext] theorem ext {u v : NormCompatUnits p} (h : u.elems = v.elems) : u = v`
- What: Two members of `𝒰_∞` with equal unit systems are equal (the other fields are propositions).
- How: `cases u; cases v`; `mk.injEq`; the hypothesis.
- Hypotheses: equal `elems`.
- Uses from project: [NormCompatUnits]
- Used by: unused in file (feeds external injectivity characterisation).
- Visibility: public (in `namespace NormCompatUnits`, `variable {p}`)
- Lines: 1112-1114 (proof 1 line)
- Notes: docstring flags a vestigial unconstrained `elems 0`.

### theorem colemanSeries_eq_iff
- Type: `theorem colemanSeries_eq_iff {u v : NormCompatUnits p} : colemanSeries p u = colemanSeries p v ↔ ∀ n, 1 ≤ n → u.elems n = v.elems n`
- What: **Injectivity of the Coleman map** (RJW thm:coleman map 2), pinned to the `n ≥ 1` interpolation data.
- How: Forward: equal series have equal values `u_n = colemanSeries(·)(π_n) = v_n` (`evalPi_colemanSeries`), `Units.ext`. Backward: if `u_n = v_n` (`n ≥ 1`), `colemanSeries v` also interpolates `u`, so `coleman_existsUnique u`'s uniqueness gives equality.
- Hypotheses: `u, v : NormCompatUnits p` (iff, so the `n ≥ 1` agreement appears on the RHS).
- Uses from project: [NormCompatUnits, colemanSeries, coleman_existsUnique, evalPi_colemanSeries, colemanSeries_isUnit, normOp_colemanSeries]
- Used by: unused in file.
- Visibility: public
- Lines: 1131-1140 (proof 9 lines)
- Notes: the `n ≥ 1` restriction is forced by the unconstrained level-0 unit.

---

## File Summary

**Total declarations: 35** — defs **7** (`toCp`, `evalPi`, `evalPiHom`, `zetaPow`, `zetaBasis`, `evalPiES`, `colemanSeries`) / lemmas+theorems **26** / instances **0** (also: 1 structure-`ext` theorem `NormCompatUnits.ext` counted among theorems; 0 structures/classes/abbrevs/inductives defined here).

**Key API (used by ≥3 in-file):**
- `toCp` — used by ~12 decls.
- `evalPi` — used by essentially all subsequent decls.
- `evalPi_mul` — used by `evalPi_pow`, `evalPiHom`, `evalPi_injective`, `norm_evalPi_sub_le_of_modEqPow`, `colemanSeries_mul`, `evalPi_one_add_X_pow`.
- `evalPi_one` — used by `evalPi_pow`, `evalPiHom`, `evalPi_one_add_X_pow`, `exists_evalPi_eq`.
- `evalPi_mem_O` — used by `evalPiES`, `norm_evalPi_sub_le_of_modEqPow`, `leftMulMatrix_zetaBasis_coe`, `evalPi_normOp`.
- `evalPi_injective` — used by `coleman_existsUnique`, `colemanSeries_mul`, `colemanSeries_eq_iff`.
- `coleman_existsUnique` — used by `colemanSeries` + all 5 `colemanSeries` lemmas.
- `colemanSeries` / `colemanSeries_isUnit` / `normOp_colemanSeries` / `evalPi_colemanSeries` — each used by `colemanSeries_mul` and `colemanSeries_eq_iff` (`colemanSeries` by all 5).

**Unused in file (terminal API, consumed downstream):** `colemanSeries_mul`, `colemanSeries_eq_iff`, `NormCompatUnits.ext`, and `exists_residue_pi` (promoted public for `Iwasawa/ResidueField.lean`).

**Decls with `sorry`: none.** **`TODO`/`admit`: none.**

**`set_option` directives (6 occurrences across 5 decls):** `exists_residue_pi` (`synthInstance.maxHeartbeats 1000000` + `maxHeartbeats 1000000`); `zetaBasis`, `zetaBasis_apply`, `leftMulMatrix_zetaBasis_coe`, `evalPi_normOp` (each `synthInstance.maxHeartbeats 1000000`).

**Proofs > 50 lines (OVER-50, need /decompose-proof) — 4:**
- `exists_residue_pi` (~89 lines)
- `coleman_existsUnique` (~80 lines)
- `exists_evalPi_eq` (~75 lines)
- `tendsto_evalPi_of_tendsto` (~65 lines)

**Proofs 30-50 lines (long) — 2:**
- `evalPi_injective` (44 lines)
- `term_norm_distinct` (35 lines)

(`exists_C_pow_mul` at 28 lines is near-threshold but under 30.)
