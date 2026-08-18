# Inventory: PadicLFunctions/ValuesAtOne.lean

File namespace: `PadicLFunctions.MeasureR`. Implements RJW Theorem 6.1(ii) — the p-adic value `L_p(θ,1)` (Leopoldt), via a distribution-free route building an explicit antiderivative power series `F̃_θ`, a genuine measure `ρ_θ`, the T618 boundary p-adic-log layer, a μ_p-collapse trace, and a CRT Gauss-product split.

Variables throughout: `p : ℕ` `[Fact p.Prime]`; `K` a `NormedField`, `NormedAlgebra ℚ_[p] K`, `IsUltrametricDist`, `CompleteSpace`, `CharZero`.

---

### def logSeriesAt
- Type: `(u : K) : PowerSeries K`
- What: The per-root logarithmic series `log((1+T)u − 1) = extLog(u−1) + Σ_{n≥1} ((−1)^{n−1}/n)(u/(u−1))ⁿ Tⁿ` as an explicit `K`-coefficient power series (TeX 2076–2080).
- How: Direct `PowerSeries.mk`; coefficient 0 is `extLog p (u-1)`, coefficient `n≥1` is `(-1)^{n-1}·n⁻¹·(u/(u-1))ⁿ`.
- Hypotheses: none beyond a field element `u`.
- Uses from project: [extLog]
- Used by: Ftilde, one_add_mul_derivative_logSeriesAt, norm_coeff_logSeriesAt_le_of_norm_one, coeff_succ_logSeriesAt, summable_seriesEval_logSeriesAt, seriesEval_logSeriesAt_of_norm, seriesEval_logSeriesAt_eq_extLog, sum_seriesEval_Ftilde
- Visibility: public (noncomputable)
- Lines: 46-49 (def, no proof)
- Notes: none

### def Ftilde
- Type: `{N : ℕ} [NeZero N] (θ : DirichletCharacter K N) {ε : K} (_hε : IsPrimitiveRoot ε N) : PowerSeries K`
- What: The explicit antiderivative `F̃_θ = −Σ_{c<N} C(θ⁻¹(c))·logSeriesAt(ε^c)` of RJW TeX ~2070, stated G-cleared (§5 clearing conventions).
- How: Direct negated finite sum over `Finset.range N`.
- Hypotheses: `θ` a Dirichlet character mod `N`; `ε` a primitive `N`-th root (argument unused in body, only naming).
- Uses from project: [logSeriesAt]
- Used by: one_add_mul_derivative_Ftilde, summable_seriesEval_Ftilde, p_mul_constantCoeff_mahlerK_rhoTheta, sum_seriesEval_Ftilde, LpFunction_one
- Visibility: public (noncomputable)
- Lines: 53-56 (def, no proof)
- Notes: none

### theorem norm_one_sub_pow_eq_one
- Type: `{D : ℕ} [NeZero D] (_hD1 : 1 < D) (hD : ¬ p ∣ D) {ε : K} (hε : IsPrimitiveRoot ε D) {c : ℕ} (hc : ¬ D ∣ c) : ‖1 - ε ^ c‖ = 1`
- What: For tame conductor `D > 1` prime to `p`, the argument `1 − ε_D^c` is a norm-one unit when `D ∤ c`.
- How: Rewrites `1 - ε^c = -(ε^c - 1)` and applies `IsPrimitiveRoot.norm_pow_sub_one_eq_one` with `norm_natCast_eq_one_of_not_dvd`.
- Hypotheses: `D > 1`, `p ∤ D`, `ε` primitive `D`-th root, `D ∤ c`.
- Uses from project: []
- Used by: norm_pow_sub_one_eq_one_of_unit
- Visibility: public; `omit [CompleteSpace K] [CharZero K]`
- Lines: 66-70 (proof ~2 lines)
- Notes: none

### theorem norm_sub_one_eq_one_of_pow
- Type: `{x : K} {m : ℕ} (hpow : ‖x ^ m - 1‖ = 1) (hx : ‖x‖ ≤ 1) : ‖x - 1‖ = 1`
- What: From `‖x^m − 1‖ = 1` and `‖x‖ ≤ 1`, conclude `‖x − 1‖ = 1`.
- How: Upper bound `‖x-1‖ ≤ 1` by the ultrametric inequality; lower bound `≥ 1` via the factorisation `x^m − 1 = (Σ_{i<m} x^i)(x − 1)` (`geom_sum_mul`) where the geometric factor has norm `≤ 1` (`norm_sum_le_of_forall_le_of_nonneg`); `le_antisymm`.
- Hypotheses: `‖x^m − 1‖ = 1`, `‖x‖ ≤ 1`.
- Uses from project: []
- Used by: norm_pow_sub_one_eq_one_of_unit
- Visibility: public; `omit [CompleteSpace K] [CharZero K]`
- Lines: 78-94 (proof ~16 lines)
- Notes: none

### theorem norm_pow_sub_one_eq_one_of_unit
- Type: `{D : ℕ} [NeZero D] (hD1 : 1 < D) (hD : ¬ p ∣ D) {n : ℕ} {ε : K} (hε : IsPrimitiveRoot ε (D * p ^ n)) {c : ℕ} (hcu : IsUnit (c : ZMod (D * p ^ n))) : ‖ε ^ c - 1‖ = 1`
- What: The norm-one discharge for `LpFunction_one`: for `N = D·p^n` with `D > 1` prime to `p`, a primitive `N`-th root `ε` and `c` coprime to `N`, `‖ε^c − 1‖ = 1`.
- How: Coprimality gives `D ∤ c`; `ε^{p^n}` is a primitive `D`-th root (`pow_of_dvd`); then `‖(ε^c)^{p^n} − 1‖ = 1` by `norm_one_sub_pow_eq_one`, lifted via `norm_sub_one_eq_one_of_pow`.
- Hypotheses: `D > 1`, `p ∤ D`, `ε` primitive `(D·p^n)`-th root, `c` a unit mod `D·p^n`.
- Uses from project: [norm_one_sub_pow_eq_one, norm_sub_one_eq_one_of_pow]
- Used by: LpFunction_one (via `hnorm`)
- Visibility: public; `omit [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 104-123 (proof ~17 lines)
- Notes: none

### theorem ring_inverse_eq_of_mul_eq_one
- Type: `{M₀ : Type*} [MonoidWithZero M₀] {a b : M₀} (ha : IsUnit a) (h : a * b = 1) : Ring.inverse a = b`
- What: A unit's `Ring.inverse` is its unique right inverse.
- How: `Ring.inverse a = Ring.inverse a · (a·b) = (Ring.inverse a · a)·b = b` via `Ring.inverse_mul_cancel`.
- Hypotheses: `a` a unit, `a·b = 1`.
- Uses from project: []
- Used by: one_add_mul_derivative_logSeriesAt, norm_coeff_inverse_one_add_X_le_one
- Visibility: private
- Lines: 126-130 (proof ~3 lines)
- Notes: none

### theorem one_add_C_mul_X_mul_geom
- Type: `{R : Type*} [CommRing R] (b : R) : (1 + C b · X) · (mk fun n => (−b)ⁿ) = 1`
- What: The geometric-series inverse `(1 + C b·T)⁻¹ = Σ_n (−b)ⁿ Tⁿ` over any commutative ring.
- How: `ext n`, case split on `n` zero/succ, telescoping `PowerSeries.coeff` of `X`-shifts; `ring`.
- Hypotheses: commutative ring `R`, element `b`.
- Uses from project: []
- Used by: one_add_mul_derivative_logSeriesAt, norm_coeff_inverse_one_add_X_le_one
- Visibility: private
- Lines: 134-146 (proof ~12 lines)
- Notes: none

### theorem one_add_mul_derivative_logSeriesAt
- Type: `{u : K} (hu : IsUnit (u − 1)) : (1 + X) · derivativeFun (logSeriesAt p K u) = 1 + Ring.inverse ((1 + X)·C u − 1)`
- What: The formal logarithmic derivative `∂(logSeriesAt u) = 1 + ((1+T)·u − 1)⁻¹` for `u − 1` a unit (TeX 2102–2105).
- How: Factor `(1+T)·u − 1 = C(u−1)·(1 + C(u/(u−1))·T)`, invert the geometric factor via `one_add_C_mul_X_mul_geom` and `ring_inverse_eq_of_mul_eq_one`, then `ext n` matching coefficients (`coeff_derivativeFun`, `coeff_succ_X_mul`) with `linear_combination`.
- Hypotheses: `u − 1` is a unit.
- Uses from project: [logSeriesAt, ring_inverse_eq_of_mul_eq_one, one_add_C_mul_X_mul_geom]
- Used by: one_add_mul_derivative_Ftilde
- Visibility: public; `omit [IsUltrametricDist K] [CompleteSpace K]`
- Lines: 155-217 (proof ~62 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem one_add_mul_derivative_Ftilde
- Type: `{N : ℕ} [NeZero N] (hN : 1 < N) {θ : DirichletCharacter K N} (hθ1 : θ ≠ 1) {ε : K} (hε : IsPrimitiveRoot ε N) (hunit : ∀ c ∈ range N, ¬ N ∣ c → IsUnit (ε ^ c − 1)) : (1 + X)·∂(Ftilde p K θ hε) = −Σ_c C(θ⁻¹(c))·Ring.inverse((1+X)·C(ε^c) − 1)`
- What: `∂F̃_θ = F_θ` — the explicit-series identity, with constant terms cancelling by `Σ_c θ⁻¹(c) = 0` for `θ ≠ 1` (Lem 6.3 first half).
- How: Push `∂` through the negated sum (linearity, `derivativeFun_smul`); per term kill `c=0` by `θ⁻¹(0)=0` and apply `one_add_mul_derivative_logSeriesAt`; the constant `1`-terms sum to `C(Σ_c θ⁻¹(c)) = 0` via reindexing `range N → ZMod N` (`Finset.sum_nbij'`) and `MulChar.sum_eq_zero_of_ne_one`.
- Hypotheses: `N > 1`, `θ` nontrivial, `ε` primitive `N`-th root, each `ε^c − 1` a unit for `N ∤ c`.
- Uses from project: [Ftilde, logSeriesAt, one_add_mul_derivative_logSeriesAt]
- Used by: p_mul_constantCoeff_mahlerK_rhoTheta
- Visibility: public; `omit [IsUltrametricDist K] [CompleteSpace K]`
- Lines: 223-283 (proof ~60 lines)
- Notes: OVER-50 (needs /decompose-proof)

### def rhoTheta
- Type: `{D : ℕ} [NeZero D] (η : DirichletCharacter (integerRing K) D) {ζ : integerRing K} (hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) {n : ℕ} (χ : DirichletCharacter (integerRing K) (p ^ n)) : MeasureR K ℤ_[p]`
- What: The genuine measure `ρ_θ = x⁻¹·Res_{ℤ_p^×}(μ_θ)` on `ℤ_p` (§5 `zetaEtaCleared` pattern on the χ-twisted `μ̃_η`, pushed forward along the unit inclusion).
- How: Built via `iota` of a composed map: `twist χ̃ (muEtaCleared η)` composed with `extendByZero` composed with `LinearMap.mulLeft (invUnitsCM)`.
- Hypotheses: `η` a character mod `D`, `ζ` primitive `D`-th root, `p ∤ D`, `χ` a character mod `p^n`.
- Uses from project: [iota, twist, muEtaCleared, extendByZero, invUnitsCM] (project measure API)
- Used by: psi_rhoTheta, one_add_mul_derivative_mahlerK_rhoTheta, zetaEtaCleared_one_eq_rhoTheta_mass, p_mul_constantCoeff_mahlerK_rhoTheta, LpFunction_one
- Visibility: public (noncomputable)
- Lines: 290-298 (def, no proof)
- Notes: none

### theorem psi_rhoTheta
- Type: `... (hζ : IsPrimitiveRoot ζ D) (hD : ¬ p ∣ D) (χ : ...) : MeasureR.psi p K (rhoTheta p K η hζ hD χ) = 0`
- What: `ρ_θ` is supported on the units, so `ψ(ρ_θ) = 0`.
- How: `ρ_θ` is in the image of `ι` whose range is `ker ψ` (RJW Rem 3.33); via `mem_range_iota_iff`.
- Hypotheses: same data as `rhoTheta`.
- Uses from project: [MeasureR.psi, rhoTheta, mem_range_iota_iff]
- Used by: p_mul_constantCoeff_mahlerK_rhoTheta
- Visibility: public; `omit [CharZero K]`
- Lines: 304-310 (proof ~1 line term-mode)
- Notes: none

### theorem map_derivativeFun
- Type: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (F : PowerSeries R) : map f (derivativeFun F) = derivativeFun (map f F)`
- What: `PowerSeries.map` commutes with `derivativeFun` (both raise the index and scale by `n+1`).
- How: `ext n`, rewrite both via `coeff_map`/`coeff_derivativeFun` and ring-hom commutation (`map_mul`, `map_natCast`).
- Hypotheses: two commutative rings and a ring hom.
- Uses from project: []
- Used by: map_one_add_mul_derivativeFun
- Visibility: private
- Lines: 314-321 (proof ~4 lines)
- Notes: none

### theorem map_one_add_mul_derivativeFun
- Type: `{R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (F : PowerSeries R) : map f ((1 + X)·derivativeFun F) = (1 + X)·derivativeFun (map f F)`
- What: `PowerSeries.map` commutes with the operator `∂ = (1+T)d/dT`.
- How: Distribute `map` over the product/sum (`map_mul`, `map_add`, `map_X`) and apply `map_derivativeFun`.
- Hypotheses: two commutative rings and a ring hom.
- Uses from project: [map_derivativeFun]
- Used by: one_add_mul_derivative_mahlerK_rhoTheta
- Visibility: private
- Lines: 324-328 (proof ~1 line)
- Notes: none

### theorem one_add_mul_derivative_mahlerK_rhoTheta
- Type: `{D : ℕ} [NeZero D] (_hD1 : 1 < D) {η : ...} (_hη : η.IsPrimitive) {ζ} (hζ) (hD) {n} (χ) : (1 + X)·∂(mahlerK ρ_θ) = mahlerK (res (isClopen_units) (twist χ̃ (muEtaCleared η)))`
- What: `∂𝓐(ρ_θ) = (1−φψ)F_θ` over `K` — multiplication by `x` recovers `Res_{ℤ_p^×}(μ_θ)` and `Res = 1 − φ∘ψ` (Lem 6.3 second half).
- How: Prove the measure-level identity `x·ρ_θ = Res_{ℤ_p^×}(μ_θ)` (`cmul_apply`, unfolding `iota`/`pushforward`, cancelling `invUnitsCM` against the `x`-monomial via `ContinuousMap.ext` and `extendByZero_comp_unitsVal`); transport through `mahlerK` via `mahlerTransform_cmul_X` and `map_one_add_mul_derivativeFun`.
- Hypotheses: `D > 1`, `η` primitive, `ζ` primitive `D`-th root, `p ∤ D`, `χ` character mod `p^n`.
- Uses from project: [mahlerK, rhoTheta, res, twist, muEtaCleared, cmul, mahlerCM, iota, pushforward_apply, cmul_apply, invUnitsCM, mahlerCM_apply, mahler_apply, extendByZero_comp_unitsVal, mahlerTransform_cmul_X, del, mahlerTransform, map_one_add_mul_derivativeFun, PadicMeasure.unitsValCM, PadicMeasure.invCM]
- Used by: p_mul_constantCoeff_mahlerK_rhoTheta
- Visibility: public; `omit [CharZero K]`
- Lines: 335-371 (proof ~36 lines)
- Notes: long(30-50)

### theorem anglePowCM_zero
- Type: `: anglePowCM p K 0 = 1`
- What: `anglePowCM p K 0 = 1` (the 0-th power is the constant 1); the `s=1` specialisation `⟨x⟩^{1−1}` of the `L_p` integrand.
- How: `ext u`, `anglePowCM_apply`, `PadicInt.onePAdicPow_natCast`, `pow_zero`, `map_one`.
- Hypotheses: none.
- Uses from project: [anglePowCM, anglePowCM_apply]
- Used by: zetaEtaCleared_one_eq_rhoTheta_mass
- Visibility: private; `omit [CompleteSpace K] [CharZero K]`
- Lines: 376-380 (proof ~4 lines)
- Notes: none

### theorem zetaEtaCleared_one_eq_rhoTheta_mass
- Type: `... (hζ) (hD) {n} {χ} : zetaEtaCleared η (χ̃∘unitsValCM · anglePowCM (1−1)) = constantCoeff (mahlerTransform ρ_θ)`
- What: P6-p8 step 1 (mass identity): the `L_p`-integrand of `ζ_η` at `s=1` (where `⟨x⟩^0 = 1`) pairs to the constant coefficient of `𝓐_{ρ_θ}`; both reduce to `μ̃_η(χ̃·extendByZero(invU))`.
- How: Rewrite the constant coefficient as the mass `ρ_θ(x^0)` (`apply_powCM`, `iterate_zero_apply`); unfold `ρ_θ` through `iota`/`pushforward`/`twist`; reduce to the integrand identity by `congr` + `ext`, case-splitting unit/non-unit `x` using `extendByZero_coe_unit` and `dif_neg`.
- Hypotheses: same data as `rhoTheta` (with `χ` implicit).
- Uses from project: [zetaEtaCleared, rhoTheta, mahlerTransform, anglePowCM, apply_powCM, powCM, iota, pushforward_apply, twist, muEtaCleared, invUnitsCM, twist_apply, zetaEtaCleared_apply, anglePowCM_zero, extendByZero_coe_unit, extendByZero, powCM_apply, PadicMeasure.unitsValCM]
- Used by: LpFunction_one
- Visibility: private; `omit [CharZero K]`
- Lines: 390-424 (proof ~34 lines)
- Notes: long(30-50)

### theorem norm_natCast_inv_le
- Type: `{n : ℕ} (hn : 1 ≤ n) : ‖(n : K)⁻¹‖ ≤ (n : ℝ)`
- What: `‖(n:K)⁻¹‖ ≤ n` for `n ≥ 1` — the polynomial-growth bound for the `1/n`-coefficients (norm of `(n:K)` is `p^{−v_p(n)}`, inverse `= ordProj[p] n ≤ n`).
- How: Write `(n:K) = algebraMap ℚ_[p] K (n:ℚ_[p])`, compute the norm as `p^{padicValNat p n}` via `Padic.norm_eq_zpow_neg_valuation` and `Padic.valuation_natCast`, then `Nat.ordProj_le`.
- Hypotheses: `n ≥ 1`.
- Uses from project: []
- Used by: norm_coeff_formalLog_le, exists_antideriv_bounded, norm_coeff_logSeriesAt_le_of_norm_one
- Visibility: private; `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 431-439 (proof ~8 lines)
- Notes: none

### theorem boundary_norm_pow_sub_one_lt_one
- Type: `{x : K} (hx : ‖x − 1‖ < 1) (n : ℕ) : ‖x ^ n − 1‖ < 1`
- What: The open unit ball `‖x − 1‖ < 1` is closed under powers, in any ultrametric normed field (no p-adic structure needed).
- How: Induction on `n`; the step bounds `‖x^{k+1} − 1‖ ≤ max ‖x^k − 1‖ ‖x − 1‖` via `x^{k+1} − 1 = (x^k − 1)x + (x − 1)`, `norm_add_le_max`, using `‖x‖ ≤ 1`.
- Hypotheses: `‖x − 1‖ < 1`.
- Uses from project: []
- Used by: padicLog_pow_p_of_norm_lt_one, padicLog_pow_pPow_of_norm_lt_one, padicLog_pow_of_norm_lt_one
- Visibility: public; `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K] [CharZero K]`
- Lines: 454-466 (proof ~12 lines)
- Notes: none

### theorem norm_coeff_formalLog_le
- Type: `(n : ℕ) : ‖coeff n (formalLog K)‖ ≤ (n : ℝ) + 1`
- What: T618 — the coefficients of `formalLog` are linearly bounded `‖coeff n‖ ≤ n + 1`; drives summability of `seriesEval (formalLog K) z` for `‖z‖ < 1`.
- How: Case split `n` zero/succ; for succ use `coeff_succ_formalLog`, `norm_natCast_inv_le`.
- Hypotheses: none.
- Uses from project: [formalLog, coeff_zero_formalLog, coeff_succ_formalLog, norm_natCast_inv_le]
- Used by: summable_seriesEval_formalLog, padicLog_pow_p_of_norm_lt_one
- Visibility: private; `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 473-481 (proof ~9 lines)
- Notes: none

### theorem summable_seriesEval_formalLog
- Type: `{z : K} (hz : ‖z‖ < 1) : Summable fun n => coeff n (formalLog K) * z ^ n`
- What: T618 — `seriesEval (formalLog K) z` converges for `‖z‖ < 1`.
- How: `summable_seriesEval_of_norm_coeff_le_linear` with `C = 1` and `norm_coeff_formalLog_le`.
- Hypotheses: `‖z‖ < 1`.
- Uses from project: [formalLog, summable_seriesEval_of_norm_coeff_le_linear, norm_coeff_formalLog_le]
- Used by: seriesEval_formalLog, seriesEval_logSeriesAt_of_norm
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 487-490 (proof ~2 lines term-mode)
- Notes: none

### theorem seriesEval_formalLog
- Type: `{z : K} (hz : ‖z − 1‖ < 1) : seriesEval (formalLog K) (z − 1) = padicLog p z`
- What: T618 eval-alignment — `seriesEval (formalLog K) (z − 1) = padicLog p z` for `‖z−1‖ < 1`.
- How: Reindex by one (`coeff 0 = 0`, `tsum_eq_zero_add`) and match the scalar `((n:ℚ_[p])+1)⁻¹` against `((n:K)+1)⁻¹` through `algebraMap`; `tsum_congr` + `ring`.
- Hypotheses: `‖z − 1‖ < 1`.
- Uses from project: [formalLog, seriesEval, coeff_zero_formalLog, coeff_succ_formalLog, padicLog, summable_seriesEval_formalLog]
- Used by: padicLog_pow_p_of_norm_lt_one, seriesEval_logSeriesAt_of_norm
- Visibility: public; `omit [CharZero K]`, `include hp`
- Lines: 497-505 (proof ~8 lines)
- Notes: none

### theorem padicLog_pow_p_of_norm_lt_one
- Type: `{z : K} (hz : ‖z − 1‖ < 1) : padicLog p (z ^ p) = (p : K) • padicLog p z`
- What: T618 — the boundary `p`-power law for `padicLog` on the whole open unit ball.
- How: Evaluate `phiSeries_formalLog` at `z − 1` through the `seriesEval` bridge (`seriesEval_phi_of_summable_prod`, `summable_prod_of_norm_coeff_le_linear`), chaining `padicLog(z^p) = seriesEval(φ formalLog)(z−1) = seriesEval(p·formalLog)(z−1) = p·padicLog z` with `boundary_norm_pow_sub_one_lt_one`, `seriesEval_C_mul`.
- Hypotheses: `‖z − 1‖ < 1`.
- Uses from project: [padicLog, formalLog, phiSeries, boundary_norm_pow_sub_one_lt_one, summable_prod_of_norm_coeff_le_linear, norm_coeff_formalLog_le, seriesEval, seriesEval_phi_of_summable_prod, seriesEval_formalLog, phiSeries_formalLog, seriesEval_C_mul]
- Used by: padicLog_pow_pPow_of_norm_lt_one
- Visibility: public; `omit [CharZero K]`, `include hp`
- Lines: 514-526 (proof ~12 lines)
- Notes: none

### theorem padicLog_pow_pPow_of_norm_lt_one
- Type: `{z : K} (hz : ‖z − 1‖ < 1) (N : ℕ) : padicLog p (z ^ (p ^ N)) = ((p : K) ^ N) • padicLog p z`
- What: T618 — `padicLog p (z^{p^N}) = (p^N)·padicLog p z` for `‖z−1‖ < 1` (iterate the `p`-power law).
- How: Induction on `N`; the step uses `padicLog_pow_p_of_norm_lt_one` on `z^{p^M}` (staying in the ball via `boundary_norm_pow_sub_one_lt_one`), `smul_smul`.
- Hypotheses: `‖z − 1‖ < 1`.
- Uses from project: [padicLog, padicLog_pow_p_of_norm_lt_one, boundary_norm_pow_sub_one_lt_one]
- Used by: padicLog_mul_of_norm_lt_one, extLog_eq_padicLog_of_norm_lt_one
- Visibility: public; `omit [CharZero K]`, `include hp`
- Lines: 532-538 (proof ~6 lines)
- Notes: none

### theorem padicLog_mul_of_norm_lt_one
- Type: `{x y : K} (hx : ‖x − 1‖ < 1) (hy : ‖y − 1‖ < 1) : padicLog p (x * y) = padicLog p x + padicLog p y`
- What: T618 — multiplicativity of `padicLog` on the whole open unit ball.
- How: Show `‖xy − 1‖ < 1`; raise `x`, `y` to a common `p^N` landing both in the exp ball (`exists_pPow_pow_inExpBall`, `pow_mem_expBall`); apply mathlib `padicLog_mul` there; descend via `padicLog_pow_pPow_of_norm_lt_one` and `smul_right_injective`.
- Hypotheses: `‖x − 1‖ < 1`, `‖y − 1‖ < 1`.
- Uses from project: [padicLog, padicLog_mul, exists_pPow_pow_inExpBall, InExpBall, pow_mem_expBall, padicLog_pow_pPow_of_norm_lt_one, natCast_p_ne_zero]
- Used by: padicLog_pow_of_norm_lt_one
- Visibility: public; `omit [CharZero K]`, `include hp`
- Lines: 544-572 (proof ~28 lines)
- Notes: none

### theorem padicLog_pow_of_norm_lt_one
- Type: `{x : K} (hx : ‖x − 1‖ < 1) (n : ℕ) : padicLog p (x ^ n) = n • padicLog p x`
- What: T618 — `padicLog p (x^n) = n·padicLog p x` on the whole open unit ball.
- How: Induction on `n` via `padicLog_mul_of_norm_lt_one` (with `boundary_norm_pow_sub_one_lt_one`), `succ_nsmul`.
- Hypotheses: `‖x − 1‖ < 1`.
- Uses from project: [padicLog, padicLog_mul_of_norm_lt_one, boundary_norm_pow_sub_one_lt_one]
- Used by: unused in file
- Visibility: public; `omit [CharZero K]`, `include hp`
- Lines: 578-584 (proof ~6 lines)
- Notes: none

### theorem extLog_eq_padicLog_of_norm_lt_one
- Type: `{x : K} (hx : ‖x − 1‖ < 1) : extLog p x = padicLog p x`
- What: T618 — `extLog p x = padicLog p x` on the whole open unit ball `‖x−1‖ < 1`.
- How: Use witness `(p^j, 0, x^{p^j})` with `x^{p^j}` in the exp ball (`exists_pPow_pow_inExpBall`); `extLog_eq_of_witness`, then `padicLog_pow_pPow_of_norm_lt_one` cancels the `(p^j)⁻¹`-scalar via `inv_mul_cancel₀`.
- Hypotheses: `‖x − 1‖ < 1`.
- Uses from project: [extLog, padicLog, exists_pPow_pow_inExpBall, extLog_eq_of_witness, padicLog_pow_pPow_of_norm_lt_one]
- Used by: seriesEval_logSeriesAt_eq_extLog
- Visibility: public; `omit [CharZero K]`, `include hp`
- Lines: 591-601 (proof ~10 lines)
- Notes: none

### theorem norm_dirichletChar_le_one
- Type: `{N : ℕ} [NeZero N] (ψ : DirichletCharacter K N) (c : ZMod N) : ‖ψ c‖ ≤ 1`
- What: Character values into `K` have norm `≤ 1` (units map to roots of unity of norm one, non-units to 0).
- How: Case split on `ψ c = 0`; otherwise `c` is a unit, `ψ(u)^{totient N} = 1` (`ZMod.pow_totient`), so `norm_eq_one_of_pow_eq_one`.
- Hypotheses: `ψ` a Dirichlet character mod `N`.
- Uses from project: [norm_eq_one_of_pow_eq_one]
- Used by: summable_seriesEval_Ftilde
- Visibility: private
- Lines: 606-615 (proof ~9 lines)
- Notes: none

### theorem norm_coeff_inverse_one_add_X_le_one
- Type: `(n : ℕ) : ‖coeff n (Ring.inverse (1 + X : PowerSeries K))‖ ≤ 1`
- What: `Ring.inverse (1 + X) = Σ (−1)ⁿ Xⁿ`, hence has integral coefficients.
- How: Identify the inverse via `one_add_C_mul_X_mul_geom` (with `b=1`) and `ring_inverse_eq_of_mul_eq_one`; coefficient is `(−1)^n`, norm 1.
- Hypotheses: none.
- Uses from project: [ring_inverse_eq_of_mul_eq_one, one_add_C_mul_X_mul_geom]
- Used by: exists_antideriv_bounded
- Visibility: private; `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
- Lines: 619-628 (proof ~9 lines)
- Notes: none

### theorem exists_antideriv_bounded
- Type: `(B : PowerSeries K) (hB : ∀ n, ‖coeff n B‖ ≤ 1) : ∃ C, constantCoeff C = 0 ∧ (p:K)•((1+X)·∂C) = B ∧ ∀ m, ‖coeff m C‖ ≤ (p:ℝ)·((m:ℝ)+1)`
- What: Bounded antiderivative (c₀-design): when `B` has integral coefficients, the antiderivative `C` has linearly bounded coefficients `‖coeff m C‖ ≤ p·(m+1)`. Feeds convergence of `seriesEval(φ C₁)` in the constant pin.
- How: Set `E := (p:K)⁻¹·(B·Ring.inverse(1+X))`, bound `‖coeff k E‖ ≤ p` via the ultrametric sum bound (`exists_norm_finsetSum_le_of_nonempty`) on `coeff_mul`, integral inverse coefficients, and `norm_natCast_inv_le`; the antiderivative is the index-shifted division by `n`, with `derivativeFun` recovering `E` (`div_mul_cancel₀`), then `Ring.inverse_mul_cancel`.
- Hypotheses: all coefficients of `B` have norm `≤ 1`.
- Uses from project: [norm_natCast_inv_le, norm_coeff_inverse_one_add_X_le_one, charZero_of_qpAlgebra]
- Used by: p_mul_constantCoeff_mahlerK_rhoTheta
- Visibility: public; `omit [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 636-682 (proof ~46 lines)
- Notes: long(30-50)

### theorem norm_coeff_logSeriesAt_le_of_norm_one
- Type: `{u : K} (hu1 : ‖u − 1‖ = 1) {n : ℕ} (hn : 1 ≤ n) : ‖coeff n (logSeriesAt p K u)‖ ≤ (n : ℝ)`
- What: For a norm-one argument `‖u−1‖ = 1`, the positive-degree coefficients of `logSeriesAt u` are bounded `‖coeff n‖ ≤ n` for `n ≥ 1`.
- How: `‖u‖ ≤ 1` and `‖u/(u−1)‖ ≤ 1`; the coefficient norm is `‖(n:K)⁻¹‖·‖u/(u−1)‖ⁿ ≤ ‖(n:K)⁻¹‖ ≤ n` via `norm_natCast_inv_le`, `pow_le_one₀`.
- Hypotheses: `‖u − 1‖ = 1`, `n ≥ 1`.
- Uses from project: [logSeriesAt, norm_natCast_inv_le]
- Used by: summable_seriesEval_Ftilde, summable_seriesEval_logSeriesAt
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 689-704 (proof ~15 lines)
- Notes: none

### theorem summable_seriesEval_Ftilde
- Type: `{N : ℕ} [NeZero N] (_hN : 1 < N) {θ : ...} {ε : K} (hε : IsPrimitiveRoot ε N) (hnorm : ∀ c ∈ range N, IsUnit (c : ZMod N) → ‖ε^c − 1‖ = 1) {z : K} (hz : ‖z‖ < 1) : Summable fun n => coeff n (Ftilde p K θ hε) * z ^ n`
- What: Lem 6.2 as a coefficient bound: `‖coeff n F̃‖ ≤ C·(n+1)` uniformly, so `seriesEval F̃ z` converges for `‖z‖ < 1`.
- How: `summable_seriesEval_of_norm_coeff_le_linear` with `C = max ‖coeff 0 F̃‖ 1`; constant term `≤ C`, positive degree bounded `≤ n` via ultrametric sum bound (`norm_sum_le_of_forall_le_of_nonneg`), `norm_dirichletChar_le_one`, `norm_coeff_logSeriesAt_le_of_norm_one`, non-unit terms vanishing.
- Hypotheses: `N > 1`, `ε` primitive `N`-th root, norm-one for unit-`c` shifted roots, `‖z‖ < 1`.
- Uses from project: [Ftilde, logSeriesAt, summable_seriesEval_of_norm_coeff_le_linear, norm_dirichletChar_le_one, norm_coeff_logSeriesAt_le_of_norm_one]
- Used by: p_mul_constantCoeff_mahlerK_rhoTheta
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 712-742 (proof ~30 lines)
- Notes: long(30-50)

### theorem p_mul_constantCoeff_mahlerK_rhoTheta
- Type: long (~20-line signature). `{D} [NeZero D] (hD1) {η} (hη) {ζ} (hζ) (hD) {n} {χ} (_hχ) {θK} (hN) (hθ1) (_hθK) {ε} (hε) {ξ} (hξ) (hnorm) {G} (_hG) (hGtwist) : (p:K)·constantCoeff(mahlerK ρ_θ) = G⁻¹·((p:K)·constantCoeff(F̃) − Σ_{i:Fin p} seriesEval(F̃)(ξ^i − 1))`
- What: P6-p6' (the constant pin, c₀-design, ψ-free): the cleared mass identity `p·𝓐_ρ(0)·G = p·F̃(0) − Σ_{i<p} F̃(ξ^i−1)`.
- How: Build `W := C G⁻¹·F̃ − 𝓐_ρ`, show `∂W = φ(B)` for bounded `B` (the ψ-part) using `one_add_mul_derivative_Ftilde`, `one_add_mul_derivative_mahlerK_rhoTheta`, `res_units_eq`; antiderivative `C₁` from `exists_antideriv_bounded` gives `∂(φC₁) = φB` (`one_add_mul_derivative_phiSeries`); so `W − φC₁` is `∂`-killed hence `C c₀` (`eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`); evaluate at `0` and at each `ξ^i − 1` where the `𝓐_ρ`-sum vanishes (`sum_seriesEval_mahlerK` + `psi_rhoTheta`) and `φ`-images collapse (`seriesEval_phi_at_root_of_summable`); `linear_combination`.
- Hypotheses: `D > 1`, `η`/`χ` primitive, `p ∤ D`, `θK ≠ 1`, `θK` the product character, `ε` primitive `(D·p^n)`-th root, `ξ` primitive `p`-th root, `hnorm` (unit-`c` norm-one), `G` a unit, `hGtwist` the G-cleared closed form of the twist.
- Uses from project: [mahlerK, rhoTheta, Ftilde, twist, muEtaCleared, MeasureR.psi, toFieldChar, exists_antideriv_bounded, norm_coeff_mahlerK_le_one, one_add_mul_derivative_Ftilde, one_add_mul_derivative_mahlerK_rhoTheta, res_units_eq, mahlerK_sub, mahlerK_phi, phiSeries, one_add_mul_derivative_phiSeries, phiSeries_C_mul, eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero, constantCoeff_phiSeries, summable_seriesEval_Ftilde, summable_seriesEval_of_norm_coeff_le_one, norm_coeff_phiSeries_le_linear, summable_seriesEval_of_norm_coeff_le_linear, summable_prod_of_norm_coeff_le_linear, seriesEval, seriesEval_sub, seriesEval_C_mul, seriesEval_add, seriesEval_phi_at_root_of_summable, seriesEval_C, sum_seriesEval_mahlerK, psi_rhoTheta]
- Used by: LpFunction_one
- Visibility: public
- Lines: 768-937 (proof ~145 lines); `set_option maxHeartbeats 800000`
- Notes: OVER-50 (needs /decompose-proof); set_option maxHeartbeats 800000

### theorem isIntegral_of_pow_eq_one
- Type: `{x : K} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) : IsIntegral ℤ x`
- What: A root of unity is integral over `ℤ` (witnessed by monic `Xⁿ − C 1`).
- How: Provide `Polynomial.X^n − C 1`, `monic_X_pow_sub_C`, `simp [hx]`.
- Hypotheses: `n > 0`, `x^n = 1`.
- Uses from project: []
- Used by: extLogDomain_pow_mul_pow_sub_one, seriesEval_logSeriesAt_eq_extLog (indirectly via callers), sum_extLog_pow_mul_collapse, sum_seriesEval_Ftilde, LpFunction_one
- Visibility: private; `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
- Lines: 950-952 (proof ~1 line term-mode)
- Notes: none

### theorem norm_pow_mul_pow_sub_one_eq_one
- Type: `{ε ξ : K} {N : ℕ} (hN0 : 0 < N) (hε : IsPrimitiveRoot ε N) {c i : ℕ} (hc1 : ‖ε^c − 1‖ = 1) (hil : ‖ξ^i − 1‖ < 1) : ‖ξ^i · ε^c − 1‖ = 1`
- What: The shifted root `ξ^i·ε^c − 1` has norm one (isoceles: `‖ξ^i ε^c − ε^c‖ = ‖ξ^i − 1‖ < 1 = ‖ε^c − 1‖`).
- How: `‖ε^c‖ = 1`; `‖ξ^i ε^c − ε^c‖ = ‖ξ^i − 1‖·‖ε^c‖ < ‖ε^c − 1‖`; then `norm_add_eq_max_of_norm_ne_norm` with the decomposition `(ξ^i ε^c − ε^c) + (ε^c − 1) = ξ^i ε^c − 1`.
- Hypotheses: `N > 0`, `ε` primitive `N`-th root, `‖ε^c − 1‖ = 1`, `‖ξ^i − 1‖ < 1`.
- Uses from project: [norm_eq_one_of_pow_eq_one]
- Used by: extLogDomain_pow_mul_pow_sub_one, sum_extLog_pow_mul_collapse
- Visibility: private; `omit [CompleteSpace K] [CharZero K]`
- Lines: 957-970 (proof ~13 lines)
- Notes: none

### theorem extLogDomain_pow_mul_pow_sub_one
- Type: `{ε ξ : K} {N : ℕ} (hN0 : 0 < N) (hε : IsPrimitiveRoot ε N) (hξ : IsPrimitiveRoot ξ p) {c i : ℕ} (hc1 : ‖ε^c − 1‖ = 1) (hil : ‖ξ^i − 1‖ < 1) : ExtLogDomain p (ξ^i · ε^c − 1)`
- What: T616 step 3 (domain engine): the shifted root `ξ^i·ε^c − 1` lies in the extended-log domain (integral, norm one).
- How: `extLogDomain_of_integral_norm_one` from integrality (`isIntegral_of_pow_eq_one` on `ξ`, `ε`, products/powers/sub) and `norm_pow_mul_pow_sub_one_eq_one`.
- Hypotheses: `N > 0`, `ε`/`ξ` primitive roots (orders `N`, `p`), `‖ε^c − 1‖ = 1`, `‖ξ^i − 1‖ < 1`.
- Uses from project: [ExtLogDomain, extLogDomain_of_integral_norm_one, isIntegral_of_pow_eq_one, norm_pow_mul_pow_sub_one_eq_one]
- Used by: sum_extLog_pow_mul_collapse
- Visibility: private; `omit [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 976-983 (proof ~3 lines term-mode)
- Notes: none

### theorem coeff_succ_logSeriesAt
- Type: `(u : K) (n : ℕ) : coeff (n+1) (logSeriesAt p K u) = coeff (n+1) (formalLog K) * (u/(u−1))^{n+1}`
- What: The positive-degree coefficients of `logSeriesAt u` factor through `formalLog`.
- How: Unfold `logSeriesAt`/`coeff_mk` and `coeff_succ_formalLog`.
- Hypotheses: field element `u`, index `n`.
- Uses from project: [logSeriesAt, formalLog, coeff_succ_formalLog]
- Used by: seriesEval_logSeriesAt_of_norm
- Visibility: private; `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
- Lines: 988-992 (proof ~2 lines)
- Notes: none

### theorem summable_seriesEval_logSeriesAt
- Type: `{u z : K} (hu1 : ‖u − 1‖ = 1) (hz : ‖z‖ < 1) : Summable fun n => coeff n (logSeriesAt p K u) * z ^ n`
- What: Summability of `seriesEval (logSeriesAt u) z` for `‖u−1‖ = 1`, `‖z‖ < 1`.
- How: `summable_seriesEval_of_norm_coeff_le_linear` with `C = max ‖extLog(u−1)‖ 1`; positive coeffs `≤ n` via `norm_coeff_logSeriesAt_le_of_norm_one`.
- Hypotheses: `‖u − 1‖ = 1`, `‖z‖ < 1`.
- Uses from project: [logSeriesAt, extLog, summable_seriesEval_of_norm_coeff_le_linear, norm_coeff_logSeriesAt_le_of_norm_one]
- Used by: seriesEval_logSeriesAt_of_norm, sum_seriesEval_Ftilde
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 998-1008 (proof ~10 lines)
- Notes: none

### theorem seriesEval_logSeriesAt_of_norm
- Type: `{u z : K} (hu1 : ‖u − 1‖ = 1) (hz : ‖z‖ < 1) : seriesEval (logSeriesAt p K u) z = extLog p (u − 1) + padicLog p (1 + u·z/(u−1))`
- What: T616 step 1 (per-term resummation half-a): split the constant `extLog(u−1)` off and identify the tail with `padicLog(1 + u·z/(u−1))`.
- How: `‖w := u z/(u−1)‖ = ‖z‖ < 1`; split via `tsum_eq_zero_add`; identify tail with `seriesEval (formalLog) w` (`seriesEval_formalLog`, `summable_seriesEval_formalLog`); `tsum_congr` + `coeff_succ_logSeriesAt`/`coeff_succ_formalLog`.
- Hypotheses: `‖u − 1‖ = 1`, `‖z‖ < 1`.
- Uses from project: [logSeriesAt, extLog, padicLog, formalLog, seriesEval, summable_seriesEval_logSeriesAt, seriesEval_formalLog, summable_seriesEval_formalLog, coeff_zero_formalLog, coeff_succ_logSeriesAt, coeff_succ_formalLog]
- Used by: seriesEval_logSeriesAt_eq_extLog
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 1016-1042 (proof ~26 lines)
- Notes: none

### theorem extLogDomain_of_norm_sub_one_lt_one
- Type: `{x : K} (hx : ‖x − 1‖ < 1) : ExtLogDomain p x`
- What: T616 — any element of the open unit ball `‖x−1‖ < 1` lies in the extended-log domain.
- How: Witness `(p^j, 0, x^{p^j})` with `x^{p^j}` in the exp ball (`exists_pPow_pow_inExpBall`).
- Hypotheses: `‖x − 1‖ < 1`.
- Uses from project: [ExtLogDomain, exists_pPow_pow_inExpBall]
- Used by: seriesEval_logSeriesAt_eq_extLog
- Visibility: private; `omit [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 1048-1051 (proof ~2 lines term-mode)
- Notes: none

### theorem seriesEval_logSeriesAt_eq_extLog
- Type: `{ε ξ : K} (hεint : IsIntegral ℤ ε) {c i : ℕ} (hc1 : ‖ε^c − 1‖ = 1) (hil : ‖ξ^i − 1‖ < 1) : seriesEval (logSeriesAt p K (ε^c)) (ξ^i − 1) = extLog p (ξ^i · ε^c − 1)`
- What: T616 step 1 (the per-term identity): the evaluated per-root series equals `extLog(ξ^i·ε^c − 1)`.
- How: Combine `seriesEval_logSeriesAt_of_norm` with the factorisation `ξ^i ε^c − 1 = (ε^c − 1)(1 + ε^c(ξ^i−1)/(ε^c−1))` and `extLog_mul`/`extLog_eq_padicLog_of_norm_lt_one`.
- Hypotheses: `ε` integral over `ℤ`, `‖ε^c − 1‖ = 1`, `‖ξ^i − 1‖ < 1`.
- Uses from project: [logSeriesAt, extLog, seriesEval, seriesEval_logSeriesAt_of_norm, extLog_mul, extLogDomain_of_integral_norm_one, extLogDomain_of_norm_sub_one_lt_one, extLog_eq_padicLog_of_norm_lt_one]
- Used by: sum_seriesEval_Ftilde
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 1060-1084 (proof ~24 lines)
- Notes: none

### theorem extLog_neg_one_pow_mul
- Type: `{x : K} (hx : ExtLogDomain p x) (m : ℕ) : extLog p ((−1)^m · x) = extLog p x`
- What: A `±1` sign is invisible to `extLog`: `extLog((−1)^m·x) = extLog x`.
- How: Induction on `m` via `extLog_neg` (with the domain closure `ExtLogDomain.mul` and integrality of `(−1)^k`).
- Hypotheses: `x` in the extended-log domain.
- Uses from project: [extLog, ExtLogDomain, ExtLogDomain.mul, extLogDomain_of_integral_norm_one, extLog_neg]
- Used by: sum_extLog_pow_mul_collapse
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 1090-1100 (proof ~11 lines)
- Notes: none

### theorem sum_fin_pow_eq_sum_nthRootsFinset
- Type: `{ξ : K} (hξ : IsPrimitiveRoot ξ p) (f : K → K) : Σ_{i:Fin p} f(ξ^i) = Σ_{ζ ∈ nthRootsFinset p 1} f ζ`
- What: Reindex a `Fin p`-sum over powers of a primitive `p`-th root as a sum over `nthRootsFinset p 1` (`i ↦ ξ^i` bijection).
- How: `Finset.sum_nbij` with membership via `mem_nthRootsFinset`, injectivity via `IsPrimitiveRoot.pow_inj`, surjectivity via `eq_pow_of_pow_eq_one`.
- Hypotheses: `ξ` a primitive `p`-th root.
- Uses from project: []
- Used by: sum_extLog_pow_mul_collapse
- Visibility: private; `omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 1106-1117 (proof ~11 lines)
- Notes: none

### theorem sum_extLog_pow_mul_collapse
- Type: `{ε ξ : K} {N : ℕ} (hN0 : 0 < N) (hε : IsPrimitiveRoot ε N) (hεint : IsIntegral ℤ ε) (hξ : IsPrimitiveRoot ξ p) {c : ℕ} (hc1 : ‖ε^c − 1‖ = 1) (hil : ∀ i : Fin p, ‖ξ^i − 1‖ < 1) : Σ_{i:Fin p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)`
- What: T616 step 3 (the μ_p-collapse): `Σ_{i<p} extLog(ξ^i·ε^c − 1) = extLog(ε^{pc} − 1)`.
- How: Each factor is in the domain (`extLogDomain_pow_mul_pow_sub_one`); the product identity `∏_ζ(ζ·ε^c − 1) = (−1)^p·(1 − ε^{pc})` (`IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`, `card_nthRootsFinset`); `‖ε^{pc} − 1‖ = 1`; then `sum_fin_pow_eq_sum_nthRootsFinset`, `extLog_prod`, and the sign-stripping `extLog_neg_one_pow_mul`.
- Hypotheses: `N > 0`, `ε`/`ξ` primitive roots, `ε` integral, `‖ε^c − 1‖ = 1`, all `‖ξ^i − 1‖ < 1`.
- Uses from project: [extLog, ExtLogDomain, extLogDomain_pow_mul_pow_sub_one, norm_pow_mul_pow_sub_one_eq_one, sum_fin_pow_eq_sum_nthRootsFinset, extLog_prod, extLog_neg_one_pow_mul, extLogDomain_of_integral_norm_one]
- Used by: sum_seriesEval_Ftilde
- Visibility: private; `omit [CharZero K]`, `include hp`
- Lines: 1127-1164 (proof ~37 lines)
- Notes: long(30-50)

### theorem sum_dirichlet_fiber_eq_zero
- Type: `{N M : ℕ} [NeZero N] (hMN : M ∣ N) {ψ : DirichletCharacter K N} (hψ : ¬ ψ.FactorsThrough M) (r : ZMod M) : Σ_{c : castHom c = r} ψ c = 0`
- What: T616 step 4 (the `p∣N` fiber sum): for primitive `ψ` not factoring through `M ∣ N`, `ψ` summed over any residue fibre mod `M` vanishes.
- How: Pick a unit `v ≡ 1 mod M` with `ψ v ≠ 1` (failure of factoring, `factorsThrough_iff_ker_unitsMap`); `c ↦ v·c` permutes the fibre (fixes residues mod `M`) so `S = ψ(v)·S`, forcing `(1 − ψ v)·S = 0` hence `S = 0`.
- Hypotheses: `M ∣ N`, `ψ` does not factor through `M`, a residue `r`.
- Uses from project: []
- Used by: sum_theta_inv_mul_extLog_pc
- Visibility: private; `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
- Lines: 1172-1213 (proof ~41 lines)
- Notes: long(30-50)

### theorem sum_theta_inv_mul_extLog_pc
- Type: `{N : ℕ} [NeZero N] (hN : 1 < N) {θ : DirichletCharacter K N} (hprim : θ.IsPrimitive) {ε : K} (hε : IsPrimitiveRoot ε N) : Σ_{c<N} θ⁻¹(c)·extLog(ε^{pc} − 1) = θ(p)·Σ_{c<N} θ⁻¹(c)·extLog(ε^c − 1)`
- What: T616 step 4 (the `c ↦ pc` bookkeeping, both cases): the `pc`-shifted trace equals `θ(p)` times the unshifted trace.
- How: Reindex both sums over `ZMod N` (`ε`-cyclicity); case split `p∣N` vs `¬p∣N`. For `¬p∣N`: `p` is a unit, substitute `a ↦ p·a` with `θ⁻¹(p⁻¹) = θ(p)` (`Finset.sum_nbij'`). For `p∣N` (`N = p·M`): both sides vanish — `θ(p) = 0` and the LHS groups along `a ↦ p·a` into fibres mod `M` killed by `sum_dirichlet_fiber_eq_zero` (`θ⁻¹` not factoring through `M` by primitivity, `conductor_inv`), using `Finset.sum_fiberwise_of_maps_to`.
- Hypotheses: `N > 1`, `θ` primitive, `ε` primitive `N`-th root.
- Uses from project: [extLog, sum_dirichlet_fiber_eq_zero]
- Used by: sum_seriesEval_Ftilde
- Visibility: private; `omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`, `include hp`
- Lines: 1224-1320 (proof ~96 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem sum_seriesEval_Ftilde
- Type: `{N : ℕ} [NeZero N] (hN : 1 < N) {θ : ...} (hprim : θ.IsPrimitive) (_hθ1 : θ ≠ 1) {ε : K} (hε : IsPrimitiveRoot ε N) {ξ : K} (hξ : IsPrimitiveRoot ξ p) (hnorm : ∀ c ∈ range N, IsUnit (c : ZMod N) → ‖ε^c − 1‖ = 1) : Σ_{i:Fin p} seriesEval(F̃)(ξ^i − 1) = θ(p)·constantCoeff(F̃)`
- What: P6-p7' (the evaluated trace, ψ-free): `Σ_{i<p} F̃(ξ^i−1) = θ(p)·F̃(0)`.
- How: Step A: `seriesEval F̃ (ξ^i − 1) = −Σ_c θ⁻¹(c)·extLog(ξ^i·ε^c − 1)` (expand the sum, `Summable.tsum_finsetSum`, `seriesEval_logSeriesAt_eq_extLog`, non-unit terms vanish). Step B: sum over `i`, swap (`Finset.sum_comm`), apply the μ_p-collapse `sum_extLog_pow_mul_collapse` per contributing `c`, then `sum_theta_inv_mul_extLog_pc` and the constant-coefficient identity `constantCoeff F̃ = −Σ_c θ⁻¹(c)·extLog(ε^c − 1)`; `ring`.
- Hypotheses: `N > 1`, `θ` primitive nontrivial, `ε`/`ξ` primitive roots, `hnorm` (unit-`c` norm-one).
- Uses from project: [Ftilde, logSeriesAt, extLog, seriesEval, isIntegral_of_pow_eq_one, summable_seriesEval_logSeriesAt, seriesEval_logSeriesAt_eq_extLog, sum_extLog_pow_mul_collapse, sum_theta_inv_mul_extLog_pc]
- Used by: LpFunction_one
- Visibility: public; `omit [CharZero K]`
- Lines: 1354-1444 (proof ~90 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem toFieldChar_changeLevel
- Type: `{D N : ℕ} [NeZero N] (h : D ∣ N) (η : DirichletCharacter (integerRing K) D) : toFieldChar (changeLevel h η) = changeLevel h (toFieldChar η)`
- What: `toFieldChar` commutes with `changeLevel`.
- How: `ext u`, both reduce to casts of `changeLevel h η ((u:ZMod N))` via `changeLevel_eq_cast_of_dvd`.
- Hypotheses: `D ∣ N`, `η` a character mod `D`.
- Uses from project: [toFieldChar]
- Used by: LpFunction_one (via `hθKfac`)
- Visibility: private; `omit [CompleteSpace K] [CharZero K]`
- Lines: 1458-1466 (proof ~5 lines)
- Notes: none

### theorem crt_collapse
- Type: `{D : ℕ} [NeZero D] {n : ℕ} (hco : Coprime D (p^n)) {ηK} {χK} {θK} (hθ : θK = changeLevel ηK · changeLevel χK) {ζK εpK : K} (hζK : IsPrimitiveRoot ζK D) (hεpK : IsPrimitiveRoot εpK (p^n)) : (double sum over range p^n × range D of θ⁻¹-weighted inverse-denominators at ζ^c·εp^b) = (single range (D·p^n)-sum at the glued root ζ·εp)`
- What: The CRT collapse (P6-p8 step 3c): the `η⊗χ` double sum reindexes via `ZMod (D·p^n) ≃ ZMod D × ZMod (p^n)` to a single `range N`-sum at `ε = ζ·εp`.
- How: Reindex both sides over the respective `ZMod`s (cyclicity of `ζK`, `εpK`, `ζK·εpK`); per-element the character factorises (`θ⁻¹ = changeLevel η⁻¹·changeLevel χ⁻¹`, both `map_nonunit`-killed off the unit CRT dichotomy `Prod.isUnit_iff`/`MulEquiv.isUnit_map`) and the root period-splits; finally `Equiv.sum_comp` over `chineseRemainder`, `Finset.sum_product`, `Finset.sum_comm`.
- Hypotheses: `D` coprime to `p^n`, `θK` the product character, `ζK`/`εpK` primitive roots.
- Uses from project: []
- Used by: LpFunction_one (via `hGtwistK`)
- Visibility: private; `omit [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]`
- Lines: 1476-1581 (proof ~105 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem LpFunction_one
- Type: long (~13-line signature). `{D} [NeZero D] (hD1) {η} (hη) {ζ} (hζ) (hD) {n} {χ} (hχ) {θK} (hθ1) (hθK) (hprim) {ε} (hε) {εp} (hεp) (hsplit : ε = ζ·εp) {ξ} (hξ) : LpFunction p K η hζ hD χ 1 = −(1 − θK(p)·p⁻¹)·(gaussSum θK⁻¹ ...)⁻¹·Σ_{c<D·p^n} θK⁻¹(c)·extLog(1 − ε^c)`
- What: **RJW Theorem 6.1(ii)** (Leopoldt): `L_p(θ,1) = −(1 − θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·log_p(1−ε_N^c)` for tame conductor `D > 1`, with `log_p = extLog`.
- How: STEP 3a build the `G_χ`-smeared closed form of the twist over `integerRing K` (`mahler_twist_formula`, `mahlerTransform_charTwist_muEtaCleared`); STEP 3b map to `K` and CRT-collapse via `crt_collapse` (using `isUnit_root_mul_pow_one_add_X_sub_one`, `map_ring_inverse_of_isUnit`) to get `hGtwist`; the norm-one discharge `hnorm` via `norm_pow_sub_one_eq_one_of_unit`; STEP 1 apply `p_mul_constantCoeff_mahlerK_rhoTheta` (T615) and the mass identity `L_p = G_η⁻¹·𝓐_ρ(0)` (`zetaEtaCleared_one_eq_rhoTheta_mass`); STEP 2 the evaluated trace `sum_seriesEval_Ftilde` (T616); Gauss-product split `G = G_η·G_χ` (`gaussSum_mul_coprime`); STEP 4 final algebra solving `𝓐_ρ(0) = G_χ⁻¹(1 − θK(p)p⁻¹)F̃(0)` by `field_simp`/`linear_combination`.
- Hypotheses: `D > 1`, `η`/`χ`/`θK` primitive, `p ∤ D`, `θK ≠ 1`, `θK` the product `toFieldChar` character, `ε` primitive `(D·p^n)`-th root split as `ε = ζ·εp` (tame `ζ` order `D`, wild `εp` order `p^n`), `ξ` primitive `p`-th root.
- Uses from project: [LpFunction, rhoTheta, Ftilde, twist, muEtaCleared, mahlerK, mahlerTransform, mahlerTransformₗ, toFieldChar, extLog, gaussSum (project coe lemmas), coe_gaussSum_zmodChar, gaussSum_inv_ne_zero, gaussSum_isUnit_of_coprime, mahler_twist_formula, charCM, tendsto_pow_pow_sub_one, mahlerTransform_charTwist_muEtaCleared, norm_pow_sub_one_lt_one, isUnit_root_mul_pow_one_add_X_sub_one, map_ring_inverse_of_isUnit, crt_collapse, toFieldChar_changeLevel, norm_pow_sub_one_eq_one_of_unit, p_mul_constantCoeff_mahlerK_rhoTheta, sum_seriesEval_Ftilde, zetaEtaCleared_one_eq_rhoTheta_mass, anglePowCM, extLog_neg, extLogDomain_of_integral_norm_one, isIntegral_of_pow_eq_one, ValuesAtOneComplex.gaussSum_mul_coprime, PadicMeasure.unitsValCM]
- Used by: unused in file (top-level result)
- Visibility: public
- Lines: 1595-1799 (proof ~205 lines)
- Notes: OVER-50 (needs /decompose-proof)

---

## File Summary

**Total declarations: 35** (defs: 2 [logSeriesAt, Ftilde] + rhoTheta = 3 defs; lemmas/theorems: 32; instances: 0).
Precisely: **3 defs / 32 theorems / 0 instances**.

**Key API (used by ≥3 in this file):**
- `logSeriesAt` (used by 8)
- `Ftilde` (used by 5)
- `rhoTheta` (used by 5)
- `norm_natCast_inv_le` (used by 3)
- `boundary_norm_pow_sub_one_lt_one` (used by 3)
- `isIntegral_of_pow_eq_one` (used by ~5)

**Unused in file:** `padicLog_pow_of_norm_lt_one` (T618 multiplicativity corollary, no in-file consumer); `LpFunction_one` (top-level theorem, consumed downstream).

**Declarations with `sorry`:** none.

**`set_option`:** `p_mul_constantCoeff_mahlerK_rhoTheta` — `set_option maxHeartbeats 800000` (lines 744-746).

**Proofs > 50 lines (OVER-50) — count: 7**
- `one_add_mul_derivative_logSeriesAt` (~62)
- `one_add_mul_derivative_Ftilde` (~60)
- `p_mul_constantCoeff_mahlerK_rhoTheta` (~145)
- `sum_theta_inv_mul_extLog_pc` (~96)
- `sum_seriesEval_Ftilde` (~90)
- `crt_collapse` (~105)
- `LpFunction_one` (~205)

**Proofs 30–50 lines (long) — count: 5**
- `one_add_mul_derivative_mahlerK_rhoTheta` (~36)
- `zetaEtaCleared_one_eq_rhoTheta_mass` (~34)
- `exists_antideriv_bounded` (~46)
- `summable_seriesEval_Ftilde` (~30)
- `sum_extLog_pow_mul_collapse` (~37)
- `sum_dirichlet_fiber_eq_zero` (~41)

(Note: 6 proofs fall in the 30–50 band; count corrected to 6.)

No `TODO`/`admit`. The file is sorry-free.
