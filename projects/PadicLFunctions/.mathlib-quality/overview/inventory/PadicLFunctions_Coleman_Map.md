# Inventory: PadicLFunctions/Coleman/Map.lean

File header (RJW §10.2, TeX 2572–2628): builds the cyclotomic units of the local tower `K_n = ℚ_p(μ_{p^n})`, the packaged norm-compatible unit tower `c(a)`, the two power-series/measure identities feeding the Coleman-map computation, and culminates in the Coleman map `Col` and the theorem `coleman_to_kl` relating it to the Kubota–Leopoldt `ζ_p`.

---

### theorem norm_primitiveRoot_eq_one
- Type: `{n : ℕ} {ξ : ℂ_[p]} (hξ : IsPrimitiveRoot ξ (p ^ n)) : ‖ξ‖ = 1`
- What: A primitive `p^n`-th root of unity in `ℂ_p` has norm `1`.
- How: From `‖ξ‖^{p^n} = ‖ξ^{p^n}‖ = ‖1‖ = 1` (via `norm_pow`, `hξ.pow_eq_one`); `le_antisymm` rules out `‖ξ‖ > 1` (`one_lt_pow₀`) and `‖ξ‖ < 1` (`pow_lt_one₀`) by contradiction with that power equation.
- Hypotheses: `ξ` is a primitive `p^n`-th root of unity in `ℂ_p`; `p` prime (instance).
- Uses from project: []
- Used by: `norm_sub_one_eq`
- Visibility: private
- Lines: 46–52 (proof ~5 lines)
- Notes: none. Docstring: "Reproduced from `Tower`'s private helper."

### theorem norm_pow_sub_one_le
- Type: `{ξ : ℂ_[p]} (hξ1 : ‖ξ‖ = 1) (c : ℕ) : ‖ξ ^ c - 1‖ ≤ ‖ξ - 1‖`
- What: For a norm-one element `ξ`, `‖ξ^c − 1‖ ≤ ‖ξ − 1‖`.
- How: Factor `ξ^c − 1 = (∑_{i<c} ξ^i)(ξ − 1)` (`geom_sum_mul`), take `norm_mul`; the geometric-sum factor has norm `≤ 1` by the ultrametric bound `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` (each term `‖ξ^i‖ = 1`), then `mul_le_of_le_one_left`.
- Hypotheses: `ξ` has norm `1`; `ℂ_p` ultrametric (ambient).
- Uses from project: []
- Used by: `norm_sub_one_eq`
- Visibility: private
- Lines: 57–64 (proof ~7 lines)
- Notes: none. Docstring: "Reproduced from `Tower`."

### theorem norm_sub_one_eq
- Type: `{n : ℕ} {ξ η : ℂ_[p]} (hξ : IsPrimitiveRoot ξ (p ^ n)) (hη : IsPrimitiveRoot η (p ^ n)) : ‖ξ - 1‖ = ‖η - 1‖`
- What: Any two primitive `p^n`-th roots of unity have equal `‖· − 1‖`.
- How: Each root is a power of the other (`eq_pow_of_pow_eq_one`, same cyclic group), so `norm_pow_sub_one_le` gives `‖ξ−1‖ ≤ ‖η−1‖` and the reverse; `le_antisymm`.
- Hypotheses: `ξ, η` primitive `p^n`-th roots in `ℂ_p`; `p` prime.
- Uses from project: []
- Used by: `norm_zetaSys_pow_sub_one_eq`
- Visibility: private
- Lines: 69–77 (proof ~7 lines)
- Notes: none. Docstring: "Reproduced from `Tower`."

### theorem zetaSys_pow_primitiveRoot
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (n : ℕ) : IsPrimitiveRoot (zetaSys p n ^ a) (p ^ n)`
- What: `ξ_{p^n}^a` is again a primitive `p^n`-th root of unity when `a` is coprime to `p`.
- How: `IsPrimitiveRoot.pow_of_coprime` applied to `zetaSys_primitiveRoot`, using `a` coprime to `p^n` (`Nat.Coprime.pow_right` from `hp.out.coprime_iff_not_dvd`).
- Hypotheses: `p ∤ a`; `n` arbitrary; `p` prime.
- Uses from project: [`zetaSys`, `zetaSys_primitiveRoot`]
- Used by: `norm_zetaSys_pow_sub_one_eq`
- Visibility: private
- Lines: 81–84 (proof 3 lines)
- Notes: none.

### theorem norm_zetaSys_pow_sub_one_eq
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (n : ℕ) : ‖zetaSys p n ^ a - 1‖ = ‖zetaSys p n - 1‖`
- What: Numerator and denominator of `c_n(a)` have equal norm (RJW TeX 2573): `‖ξ_{p^n}^a − 1‖ = ‖ξ_{p^n} − 1‖`.
- How: Both `ξ_{p^n}^a` and `ξ_{p^n}` are primitive `p^n`-th roots, so `norm_sub_one_eq` applies (with `zetaSys_pow_primitiveRoot` and `zetaSys_primitiveRoot`).
- Hypotheses: `p ∤ a`; `p` prime.
- Uses from project: [`zetaSys`, `zetaSys_pow_primitiveRoot`, `zetaSys_primitiveRoot`]
- Used by: `norm_cycloUnit`
- Visibility: private
- Lines: 89–91 (proof 1 line)
- Notes: none.

### def cycloUnit
- Type: `(a n : ℕ) : ℂ_[p] := (zetaSys p n ^ a - 1) / (zetaSys p n - 1)`
- What: The cyclotomic unit `c_n(a) = (ξ_{p^n}^a − 1)/(ξ_{p^n} − 1)` of `K_n` (RJW TeX 2573); at level `0` it is the junk value `0/0 = 0`.
- How: Definition (quotient of two `zetaSys`-based elements).
- Hypotheses: none beyond `p` prime.
- Uses from project: [`zetaSys`]
- Used by: `cycloUnit_mem_K`, `norm_cycloUnit`, `cycloUnit_ne_zero`, `cycloUnit_mem_O`, `inv_cycloUnit_mem_O`, `levelNorm_cycloUnit`, `cyclo`, `evalPi_geomSum`
- Visibility: public
- Lines: 96–97 (def)
- Notes: noncomputable; none.

### theorem cycloUnit_mem_K
- Type: `(a : ℕ) {n : ℕ} (_hn : 1 ≤ n) : cycloUnit p a n ∈ K p n`
- What: `c_n(a)` lies in the intermediate field `K_n`.
- How: Both numerator `ξ_{p^n}^a − 1` and denominator `ξ_{p^n} − 1` lie in `K_n` (`zetaSys_mem_K`, `pow_mem`, `sub_mem`, `one_mem`); `IntermediateField.div_mem`.
- Hypotheses: `n ≥ 1` (unused in proof body, `_hn`); `p` prime.
- Uses from project: [`cycloUnit`, `K`, `zetaSys_mem_K`]
- Used by: `norm_cycloUnit` (no), `cycloUnit_mem_O`, `inv_cycloUnit_mem_O`
- Visibility: public
- Lines: 101–105 (proof ~4 lines)
- Notes: none.

### theorem zetaSys_sub_one_ne_zero
- Type: `{n : ℕ} (hn : 1 ≤ n) : zetaSys p n - 1 ≠ 0`
- What: The denominator `ξ_{p^n} − 1` of `c_n(a)` is nonzero for `n ≥ 1`.
- How: `sub_ne_zero_of_ne` from `ξ_{p^n} ≠ 1` (`IsPrimitiveRoot.ne_one`, since `p^n > 1` for `n ≥ 1` via `one_lt_pow₀`).
- Hypotheses: `n ≥ 1`; `p` prime.
- Uses from project: [`zetaSys`, `zetaSys_primitiveRoot`]
- Used by: `norm_cycloUnit`, `levelNorm_cycloUnit`
- Visibility: private
- Lines: 108–111 (proof ~3 lines)
- Notes: none.

### theorem norm_cycloUnit
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) : ‖cycloUnit p a n‖ = 1`
- What: `c_n(a)` has norm `1` (RJW TeX 2573).
- How: `norm_div`, then numerator and denominator have equal norm (`norm_zetaSys_pow_sub_one_eq`), so `div_self` (denominator-norm nonzero via `zetaSys_sub_one_ne_zero`).
- Hypotheses: `p ∤ a`; `n ≥ 1`; `p` prime.
- Uses from project: [`cycloUnit`, `norm_zetaSys_pow_sub_one_eq`, `zetaSys_sub_one_ne_zero`]
- Used by: `cycloUnit_ne_zero`, `cycloUnit_mem_O`, `inv_cycloUnit_mem_O`
- Visibility: public
- Lines: 115–118 (proof ~3 lines)
- Notes: none.

### theorem cycloUnit_ne_zero
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) : cycloUnit p a n ≠ 0`
- What: `c_n(a)` is nonzero (for `p ∤ a`, `n ≥ 1`).
- How: Its norm is `1 ≠ 0` (`norm_cycloUnit`, `norm_ne_zero_iff`).
- Hypotheses: `p ∤ a`; `n ≥ 1`; `p` prime.
- Uses from project: [`cycloUnit`, `norm_cycloUnit`]
- Used by: `cyclo`
- Visibility: public
- Lines: 121–123 (proof ~2 lines)
- Notes: none.

### theorem cycloUnit_mem_O
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) : cycloUnit p a n ∈ O p n`
- What: `c_n(a) ∈ 𝒪_n` (RJW TeX 2573).
- How: `O = K ⊓ {norm ≤ 1}` (`Subring.mem_inf`); membership in `K_n` (`cycloUnit_mem_K`) and norm `1 ≤ 1` (`norm_cycloUnit`).
- Hypotheses: `p ∤ a`; `n ≥ 1`; `p` prime.
- Uses from project: [`cycloUnit`, `O`, `cycloUnit_mem_K`, `norm_cycloUnit`]
- Used by: `cyclo`
- Visibility: public
- Lines: 126–129 (proof ~2 lines)
- Notes: none.

### theorem inv_cycloUnit_mem_O
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) : (cycloUnit p a n)⁻¹ ∈ O p n`
- What: `c_n(a)⁻¹ ∈ 𝒪_n`.
- How: Same argument as `cycloUnit_mem_O` with the inverse: `K_n` closed under inverse (`IntermediateField.inv_mem`), and `‖c_n(a)⁻¹‖ = 1⁻¹ = 1 ≤ 1` (`norm_inv`, `norm_cycloUnit`).
- Hypotheses: `p ∤ a`; `n ≥ 1`; `p` prime.
- Uses from project: [`cycloUnit`, `O`, `cycloUnit_mem_K`, `norm_cycloUnit`]
- Used by: `cyclo`
- Visibility: public
- Lines: 133–138 (proof ~4 lines)
- Notes: none.

### theorem levelNorm_inv
- Type: `{n : ℕ} {x : ℂ_[p]} (hx : x ∈ K p (n + 1)) (hx0 : x ≠ 0) : levelNorm p n x⁻¹ = (levelNorm p n x)⁻¹`
- What: The level norm `N_{n+1,n}` of an inverse is the inverse of the level norm.
- How: Multiplicativity `levelNorm x · levelNorm x⁻¹ = levelNorm (x·x⁻¹) = levelNorm 1 = 1` (`levelNorm_mul`, `mul_inv_cancel₀`, `levelNorm_one`; `x⁻¹ ∈ K_{n+1}` since field), then `eq_inv_of_mul_eq_one_left`.
- Hypotheses: `x ∈ K_{n+1}`, `x ≠ 0`; `p` prime.
- Uses from project: [`K`, `levelNorm`, `levelNorm_mul`, `levelNorm_one`]
- Used by: `levelNorm_div`
- Visibility: private
- Lines: 144–149 (proof ~3 lines)
- Notes: none.

### theorem levelNorm_div
- Type: `{n : ℕ} {x y : ℂ_[p]} (hx : x ∈ K p (n + 1)) (hy : y ∈ K p (n + 1)) (hy0 : y ≠ 0) : levelNorm p n (x / y) = levelNorm p n x / levelNorm p n y`
- What: The level norm of a quotient is the quotient of the level norms.
- How: `div_eq_mul_inv`, then `levelNorm_mul` and `levelNorm_inv`.
- Hypotheses: `x, y ∈ K_{n+1}`, `y ≠ 0`; `p` prime.
- Uses from project: [`K`, `levelNorm`, `levelNorm_mul`, `levelNorm_inv`]
- Used by: `levelNorm_cycloUnit`
- Visibility: private
- Lines: 153–157 (proof ~2 lines)
- Notes: none.

### theorem levelNorm_cycloUnit
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : levelNorm p n (cycloUnit p a (n + 1)) = cycloUnit p a n`
- What: Norm compatibility of the cyclotomic units (RJW TeX 2581–2585): `N_{n+1,n}(c_{n+1}(a)) = c_n(a)` for `n ≥ 1`.
- How: Unfold `cycloUnit` and apply `levelNorm_div`; the numerator collapses by `levelNorm_zetaSys_pow_sub_one` (`b = a`), the denominator by the same with `b = 1`, i.e. `levelNorm_pi` (rewriting through `pi`).
- Hypotheses: `p ∤ a`, `p ≠ 2`, `n ≥ 1`; `p` prime.
- Uses from project: [`cycloUnit`, `K`, `levelNorm`, `levelNorm_div`, `levelNorm_pi`, `levelNorm_zetaSys_pow_sub_one`, `zetaSys`, `zetaSys_mem_K`, `zetaSys_sub_one_ne_zero`, `pi`]
- Used by: `cyclo`, `colemanSeries_cyclo`
- Visibility: public
- Lines: 163–173 (proof ~9 lines)
- Notes: none.

### def cyclo
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) : NormCompatUnits p` (structure-instance with fields `elems`, `mem`, `inv_mem`, `compat`)
- What: The packaged cyclotomic-unit tower `c(a) = (c_n(a))_n` as a norm-compatible system of units (RJW TeX 2577); level `0` set to `1`, level `n ≥ 1` is `c_n(a)`.
- How: `elems n := if 1 ≤ n then Units.mk0 (cycloUnit p a n) … else 1`; `mem`/`inv_mem` case-split on `1 ≤ n` using `cycloUnit_mem_O` / `inv_cycloUnit_mem_O` (else `one_mem`); `compat` is `levelNorm_cycloUnit`.
- Hypotheses: `p ∤ a`, `p ≠ 2`; `p` prime.
- Uses from project: [`NormCompatUnits`, `cycloUnit`, `cycloUnit_ne_zero`, `cycloUnit_mem_O`, `inv_cycloUnit_mem_O`, `levelNorm_cycloUnit`, `O`]
- Used by: `colemanSeries_cyclo`, `Col_cyclo`, `coleman_to_kl`
- Visibility: public
- Lines: 180–197 (structure-instance body ~17 lines total across fields)
- Notes: noncomputable; none (each field proof short).

### theorem one_add_X_mul_derivativeFun_one_add_X_pow
- Type: `(a : ℕ) : (1 + X) * derivativeFun ((1 + X : PowerSeries ℤ_[p]) ^ a) = (a : PowerSeries ℤ_[p]) * (1 + X) ^ a`
- What: The identity `(1+T)·∂((1+T)^a) = a·(1+T)^a` over any commutative ring.
- How: Leibniz/`derivativeFun_mul` induction on `a` with `∂(1+T) = 1` (`derivativeFun_add`, `derivativeFun_one`, `derivative_X`); base case trivial; successor uses `pow_succ`, the IH, `push_cast`, `ring`.
- Hypotheses: none beyond `p` prime (works over the `ℤ_[p]` power-series ring).
- Uses from project: []
- Used by: `one_add_mul_derivative_log_geomSum`
- Visibility: private
- Lines: 202–216 (proof ~12 lines)
- Notes: long-ish but under 30. Hinges on `derivativeFun_mul`. none.

### theorem one_add_mul_derivative_log_geomSum
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (_ha0 : a ≠ 0) : (1 + X) * derivativeFun (PadicMeasure.geomSum p a) = (((a : PowerSeries ℤ_[p]) - 1) - PadicMeasure.Fa p a) * PadicMeasure.geomSum p a`
- What: Cleared logarithmic-derivative identity (RJW prop:coleman zetap, TeX 2595–2608): `∂log f_{c(a)} = (a−1) − F_a`, i.e. `(1+T)·(geomSum a)′ = ((a−1)−F_a)·geomSum a`.
- How: §8 T704 template. Differentiate `geomSum a · T = (1+T)^a − 1` (`geomSum_mul_X`) to get `hdiff`; the key step `hQ` is `one_add_X_mul_derivativeFun_one_add_X_pow`; `hFa` is `one_add_X_pow_sub_one_mul_Fa`. Cancel the regular element `T` (`mul_right_cancel₀`, `X_ne_zero`) after reducing both sides (`hL`, `hR`) and substituting `(1+T)^a = G·T + 1`; `ring`.
- Hypotheses: `p ∤ a`, `a ≠ 0` (the latter unused, `_ha0`); `p` prime.
- Uses from project: [`PadicMeasure.geomSum`, `PadicMeasure.geomSum_mul_X`, `PadicMeasure.Fa`, `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`, `one_add_X_mul_derivativeFun_one_add_X_pow`]
- Used by: `dlog_geomSum`
- Visibility: public
- Lines: 227–262 (proof ~35 lines)
- Notes: long(30-50). Hinges on `geomSum_mul_X`, `one_add_X_pow_sub_one_mul_Fa`, `one_add_X_mul_derivativeFun_one_add_X_pow`. No sorry/set_option.

### theorem res_sub
- Type: `{U : Set ℤ_[p]} (hU : IsClopen U) (μ ν : PadicMeasure p ℤ_[p]) : PadicMeasure.res p hU (μ - ν) = PadicMeasure.res p hU μ - PadicMeasure.res p hU ν`
- What: `Res_U` is additive.
- How: `LinearMap.ext`; unfold `res = cmul`, evaluate pointwise via `cmul_apply` and `LinearMap.sub_apply`.
- Hypotheses: `U` clopen; `p` prime.
- Uses from project: [`PadicMeasure.res`, `PadicMeasure.cmul_apply`]
- Used by: `res_derivative_log_geomSum`
- Visibility: private
- Lines: 265–270 (proof ~4 lines)
- Notes: none.

### theorem res_smul
- Type: `{U : Set ℤ_[p]} (hU : IsClopen U) (c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) : PadicMeasure.res p hU (c • μ) = c • PadicMeasure.res p hU μ`
- What: `Res_U` commutes with scalar multiplication.
- How: `LinearMap.ext`; unfold `res = cmul`, evaluate via `cmul_apply`, `LinearMap.smul_apply`.
- Hypotheses: `U` clopen; `p` prime.
- Uses from project: [`PadicMeasure.res`, `PadicMeasure.cmul_apply`]
- Used by: `res_units_symm_C`
- Visibility: private
- Lines: 273–278 (proof ~3 lines)
- Notes: none.

### theorem res_units_dirac_zero
- Type: `PadicMeasure.res p (PadicMeasure.isClopen_units p) (PadicMeasure.dirac p (0 : ℤ_[p])) = 0`
- What: The restriction of the Dirac mass `δ_0` to `ℤ_p^×` is `0` (since `0` is not a unit).
- How: `LinearMap.ext`; unfold `res`/`cmul_apply`/`dirac_apply`; the indicator `𝟙_{ℤ_p^×}(0)` is `0` (`Set.indicator_of_notMem`, `0` not a unit).
- Hypotheses: `p` prime.
- Uses from project: [`PadicMeasure.res`, `PadicMeasure.cmul_apply`, `PadicMeasure.dirac`, `PadicMeasure.dirac_apply`, `PadicMeasure.isClopen_units`]
- Used by: `res_units_symm_C`
- Visibility: private
- Lines: 282–294 (proof ~10 lines)
- Notes: none. Hinges on `Set.indicator_of_notMem`.

### theorem res_units_symm_C
- Type: `(c : ℤ_[p]) : PadicMeasure.res p (PadicMeasure.isClopen_units p) ((PadicMeasure.mahlerLinearEquiv p).symm (PowerSeries.C (R := ℤ_[p]) c)) = 0`
- What: The measure attached to the constant series `c` is `c·δ_0`, whose residue at `ℤ_p^×` vanishes.
- How: Show `𝓐⁻¹(C c) = c • δ_0` (`hsymm`): write `C c = c • 1`, use `map_smul`, then identify `𝓐⁻¹(1) = δ_0` by injectivity of `mahlerLinearEquiv` (`mahlerTransform_dirac`, `binomialSeries_zero`). Then `res_smul`, `res_units_dirac_zero`, `smul_zero`.
- Hypotheses: `p` prime.
- Uses from project: [`PadicMeasure.res`, `PadicMeasure.isClopen_units`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.mahlerLinearEquiv_apply`, `PadicMeasure.dirac`, `PadicMeasure.mahlerTransform_dirac`, `res_smul`, `res_units_dirac_zero`, `binomialSeries_zero`]
- Used by: `res_derivative_log_geomSum`
- Visibility: private
- Lines: 298–309 (proof ~11 lines)
- Notes: none. Hinges on `mahlerTransform_dirac`, `binomialSeries_zero`.

### theorem res_derivative_log_geomSum
- Type: `{a : ℕ} (_ha : ¬ (p : ℕ) ∣ a) (_ha0 : a ≠ 0) : PadicMeasure.res p (…isClopen_units) ((mahlerLinearEquiv).symm (((a) - 1) - Fa p a)) = - PadicMeasure.res p (…isClopen_units) (PadicMeasure.muA p a)`
- What: RJW lem:relate cyclo to mua (TeX 2611–2624), measure-level form: `Res_{ℤ_p^×}(μ_{(a−1)−F_a}) = −Res_{ℤ_p^×}(μ_a)`.
- How: Rewrite the constant part `a−1` as `C ((a:ℤ_p)−1)` (`hconst`); split via `map_sub` and `res_sub`; the constant residue vanishes (`res_units_symm_C`), leaving `−Res(𝓐⁻¹(F_a)) = −Res(μ_a)` (`muA` defn, `zero_sub`).
- Hypotheses: `p ∤ a`, `a ≠ 0` (both unused, `_`-prefixed); `p` prime.
- Uses from project: [`PadicMeasure.res`, `PadicMeasure.isClopen_units`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.Fa`, `PadicMeasure.muA`, `res_sub`, `res_units_symm_C`]
- Used by: `Col_cyclo`
- Visibility: public
- Lines: 316–324 (proof ~4 lines)
- Notes: none.

### theorem evalPi_geomSum
- Type: `(a : ℕ) {m : ℕ} (hm : 1 ≤ m) : evalPi p (PadicMeasure.geomSum p a) m = cycloUnit p a m`
- What: RJW TeX 2589–2592: `geomSum a` evaluated at the uniformiser `π_m` (`m ≥ 1`) equals the cyclotomic unit `c_m(a)`.
- How: From `geomSum a · T = (1+T)^a − 1` (`geomSum_mul_X`), apply `evalPi` (which is multiplicative `evalPi_mul`, etc.) to get `(geomSum a)(π_m)·π_m = ξ_m^a − 1` via `evalPi_one_add_X_pow`, `evalPi_X`, `evalPi_sub`, `evalPi_one`; then divide (`eq_div_iff`, `π_m = ξ_m − 1 ≠ 0` via `pi_ne_zero`) to match `cycloUnit`.
- Hypotheses: `m ≥ 1`; `p` prime.
- Uses from project: [`evalPi`, `PadicMeasure.geomSum`, `PadicMeasure.geomSum_mul_X`, `cycloUnit`, `pi`, `pi_ne_zero`, `evalPi_X`, `evalPi_mul`, `evalPi_sub`, `evalPi_one_add_X_pow`, `evalPi_one`, `zetaSys`]
- Used by: `colemanSeries_cyclo`
- Visibility: public
- Lines: 331–337 (proof ~5 lines)
- Notes: none.

### theorem colemanSeries_cyclo
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) : colemanSeries p (cyclo p ha hp2) = PadicMeasure.geomSum p a`
- What: RJW prop:coleman zetap (TeX 2589–2592): the Coleman power series of the tower `c(a)` is `geomSum a = ((1+T)^a − 1)/T`.
- How: Uniqueness of the Coleman series (`coleman_existsUnique` `.unique`): `geomSum a` satisfies the three defining clauses — `IsUnit` (`isUnit_geomSum`), `𝒩`-invariance `normOp (geomSum a) = geomSum a` (`hnorm`, via `evalPi_injective` + `evalPi_normOp` + `evalPi_geomSum` + `levelNorm_cycloUnit`), and interpolation `(geomSum a)(π_n) = (cyclo a).elems n` (`heval`, via `evalPi_geomSum`).
- Hypotheses: `p ∤ a`, `p ≠ 2`; `p` prime.
- Uses from project: [`colemanSeries`, `cyclo`, `PadicMeasure.geomSum`, `PadicMeasure.isUnit_geomSum`, `normOp`, `evalPi`, `evalPi_injective`, `evalPi_normOp`, `evalPi_geomSum`, `levelNorm_cycloUnit`, `coleman_existsUnique`]
- Used by: `Col_cyclo`
- Visibility: public
- Lines: 352–365 (proof ~12 lines)
- Notes: none. Hinges on `coleman_existsUnique`, `evalPi_normOp`, `evalPi_injective`.

### def dlog
- Type: `(f : PowerSeries ℤ_[p]) : PowerSeries ℤ_[p] := (1 + PowerSeries.X) * PowerSeries.derivativeFun f * Ring.inverse f`
- What: The logarithmic derivative `∂log f = (1+T)·f′·f⁻¹` of a power series (RJW §10.2, Def:coleman map, TeX 2829); honest for units, junk `0`·factor off the units.
- How: Definition (`Ring.inverse` for the inverse factor).
- Hypotheses: none beyond `p` prime.
- Uses from project: []
- Used by: `Col`, `dlog_geomSum`, `Col_cyclo`
- Visibility: public
- Lines: 372–373 (def)
- Notes: noncomputable; none.

### theorem iota_comp_extendByZero
- Type: `(μ : PadicMeasure p ℤ_[p]) : PadicMeasure.iota p (μ.comp (PadicMeasure.extendByZero p)) = PadicMeasure.res p (PadicMeasure.isClopen_units p) μ`
- What: `ι(μ.comp extendByZero) = Res_{ℤ_p^×}(μ)`: precomposing a `ℤ_p`-measure with the units-section and re-embedding by `ι` recovers the restriction to `ℤ_p^×`.
- How: `LinearMap.ext`; `change` to the explicit pointwise statement, then `extendByZero_comp_unitsVal` rewrites the section composite to the charFn-multiplication form.
- Hypotheses: `p` prime.
- Uses from project: [`PadicMeasure.iota`, `PadicMeasure.extendByZero`, `PadicMeasure.res`, `PadicMeasure.isClopen_units`, `PadicMeasure.unitsValCM`, `PadicMeasure.extendByZero_comp_unitsVal`]
- Used by: `Col_cyclo`
- Visibility: public
- Lines: 379–385 (proof ~4 lines)
- Notes: none.

### def Col
- Type: `(u : NormCompatUnits p) : PadicMeasure p ℤ_[p]ˣ := PadicMeasure.unitsCmul p (PadicMeasure.invCM p) (((mahlerLinearEquiv).symm (dlog p (colemanSeries p u))).comp (PadicMeasure.extendByZero p))`
- What: The Coleman map `Col : 𝒰_∞ → Λ(ℤ_p^×)` (RJW Def:coleman map, TeX 2826–2832), realised measure-side as `x⁻¹ · Res_{ℤ_p^×}(𝒜⁻¹(∂log f_u))`.
- How: Definition: take `𝓐⁻¹(∂log f_u)`, precompose with `extendByZero` (restriction to `ℤ_p^×`), multiply by `invCM = x⁻¹` (`unitsCmul`).
- Hypotheses: none beyond `p` prime.
- Uses from project: [`NormCompatUnits`, `PadicMeasure.unitsCmul`, `PadicMeasure.invCM`, `PadicMeasure.mahlerLinearEquiv`, `dlog`, `colemanSeries`, `PadicMeasure.extendByZero`]
- Used by: `Col_cyclo`, `coleman_to_kl`
- Visibility: public
- Lines: 393–396 (def)
- Notes: noncomputable; none.

### theorem dlog_geomSum
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) : dlog p (PadicMeasure.geomSum p a) = ((a : PowerSeries ℤ_[p]) - 1) - PadicMeasure.Fa p a`
- What: `∂log (geomSum a) = (a−1) − F_a` (RJW prop:coleman zetap, TeX 2595–2608).
- How: Unfold `dlog`, apply `one_add_mul_derivative_log_geomSum`, then cancel `geomSum a` by `Ring.mul_inverse_cancel` (it is a unit, `isUnit_geomSum`); `mul_one`. (`a ≠ 0` derived from `ha`.)
- Hypotheses: `p ∤ a`; `p` prime.
- Uses from project: [`dlog`, `PadicMeasure.geomSum`, `PadicMeasure.Fa`, `one_add_mul_derivative_log_geomSum`, `PadicMeasure.isUnit_geomSum`]
- Used by: `Col_cyclo`
- Visibility: public
- Lines: 402–407 (proof ~3 lines)
- Notes: none.

### theorem unitsCmul_neg
- Type: `(g : C(ℤ_[p]ˣ, ℤ_[p])) (μ : PadicMeasure p ℤ_[p]ˣ) : PadicMeasure.unitsCmul p g (-μ) = -PadicMeasure.unitsCmul p g μ`
- What: `x⁻¹`-multiplication (`unitsCmul`) is additive in the measure: it negates a negated measure.
- How: `LinearMap.ext fun _ => rfl` (precomposition `μ ↦ μ.comp L` is `ℤ_p`-linear, so definitional).
- Hypotheses: `p` prime.
- Uses from project: [`PadicMeasure.unitsCmul`]
- Used by: `Col_cyclo`
- Visibility: private
- Lines: 411–413 (proof 1 line)
- Notes: none.

### theorem Col_cyclo
- Type: `{a : ℕ} (ha : ¬ (p : ℕ) ∣ a) (hp2 : p ≠ 2) : Col p (cyclo p ha hp2) = -PadicMeasure.zetaNum p a`
- What: Provable core of RJW thm:coleman to kl: `Col(c(a)) = −zetaNum a`, with `zetaNum a = x⁻¹·Res_{ℤ_p^×}(μ_a)` the numerator of `ζ_p`; the minus is RJW lem:relate cyclo to mua (TeX 2614).
- How: Show `(𝓐⁻¹(∂log f_{c(a)})).comp extendByZero = −muAUnits a` (`hmeasure`) by `iota`-injectivity: `ι` of LHS is `Res(𝓐⁻¹((a−1)−F_a))` (`iota_comp_extendByZero`, `colemanSeries_cyclo`, `dlog_geomSum`) `= −Res(μ_a) = ι(−muAUnits a)` (`res_derivative_log_geomSum`, `map_neg`, `iota_muAUnits`). Then `unitsCmul_neg` gives `Col = −zetaNum a` (`zetaNum` defn).
- Hypotheses: `p ∤ a`, `p ≠ 2`; `p` prime.
- Uses from project: [`Col`, `cyclo`, `PadicMeasure.zetaNum`, `PadicMeasure.mahlerLinearEquiv`, `dlog`, `colemanSeries`, `PadicMeasure.extendByZero`, `PadicMeasure.muAUnits`, `PadicMeasure.iota_injective`, `iota_comp_extendByZero`, `colemanSeries_cyclo`, `dlog_geomSum`, `res_derivative_log_geomSum`, `PadicMeasure.iota_muAUnits`, `unitsCmul_neg`]
- Used by: `coleman_to_kl`
- Visibility: public
- Lines: 423–433 (proof ~8 lines)
- Notes: none. Hinges on `iota_injective`, `iota_muAUnits`, `res_derivative_log_geomSum`.

### theorem coleman_to_kl
- Type: `(hp2 : p ≠ 2) : algebraMap _ (QuotientField p) (dirac p (…topological_generator…choose_spec.choose - 1)) * padicZeta p hp2 = -algebraMap _ _ (Col p (cyclo p (…choose_spec.choose_spec.1) hp2))`
- What: RJW thm:coleman to kl (TeX 2836–2841), honest-sign form: for the chosen integer topological generator `a` of `ℤ_p^×`, `([a]−[1])·ζ_p = −Col(c(a))` in `Q(ℤ_p^×)` (i.e. `ζ_p = −Col(c(a))/θ_a`); the corrected minus addresses RJW errata #12.
- How: The defining relation of `ζ_p = mk'(zetaNum a, [a]−1)` is `([a]−1)·ζ_p = zetaNum a` (`IsLocalization.mk'_spec'`, via `padicZeta` defn); combine with `Col_cyclo` (`Col(c(a)) = −zetaNum a`), `map_neg`, `neg_neg`. The generator data is unpacked from `exists_nat_topological_generator`.
- Hypotheses: `p ≠ 2`; `p` prime; `a` is the chosen nat topological generator (from `exists_nat_topological_generator`).
- Uses from project: [`PadicMeasure.QuotientField`, `PadicMeasure.dirac`, `PadicMeasure.exists_nat_topological_generator`, `PadicMeasure.padicZeta`, `PadicMeasure.zetaNum`, `Col`, `cyclo`, `Col_cyclo`]
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 448–466 (proof ~11 lines)
- Notes: none. Hinges on `IsLocalization.mk'_spec'`, `Col_cyclo`.

---

## File Summary

- **Total declarations: 27** — defs: 4 (`cycloUnit`, `cyclo`, `dlog`, `Col`); lemmas/theorems: 23; instances: 0; structures/classes/abbrevs/inductives: 0. (Note: `cyclo` is a `NormCompatUnits` structure-instance built via `where`, but is a `def`.)
- **Key API (used by ≥3 in this file):**
  - `cycloUnit` (used by 8)
  - `cyclo` (used by 3: `colemanSeries_cyclo`, `Col_cyclo`, `coleman_to_kl`)
  - `dlog` (used by 3: `Col`, `dlog_geomSum`, `Col_cyclo`)
  - `Col` (used by 3: `Col_cyclo`, `coleman_to_kl`; def itself)
  - `norm_cycloUnit` (used by 3: `cycloUnit_ne_zero`, `cycloUnit_mem_O`, `inv_cycloUnit_mem_O`)
- **Unused in file (terminal / exported):** `coleman_to_kl` (the top-level theorem). All others are consumed within the file. `cycloUnit_mem_K`'s direct in-file consumers are `cycloUnit_mem_O`/`inv_cycloUnit_mem_O` (used).
- **Declarations with `sorry`: none.**
- **`set_option`: none.**
- **Proofs > 50 lines (OVER-50): 0.**
- **Proofs 30–50 lines: 1** — `one_add_mul_derivative_log_geomSum` (~35 lines, lines 227–262).
- Near-threshold note: `one_add_X_mul_derivativeFun_one_add_X_pow` (~12), `res_units_dirac_zero` (~10), `res_units_symm_C` (~11), `colemanSeries_cyclo` (~12) are the next-longest but all well under 30.

**Output path:** `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_Coleman_Map.md`
