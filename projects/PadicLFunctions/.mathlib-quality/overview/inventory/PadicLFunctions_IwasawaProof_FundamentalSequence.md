# Inventory: PadicLFunctions/IwasawaProof/FundamentalSequence.lean

File header: RJW §12.2.2 — the fundamental exact sequence E12.3, `0 → ℤ_p(1) → 𝒰_{∞,1} →[Col] Λ(𝒢) → ℤ_p(1) → 0`. Status: sorry-free. Namespace `PadicLFunctions.Coleman`; `noncomputable section`; `variable (p : ℕ) [hp : Fact p.Prime]`.

---

### theorem norm_zetaSys_sub_one_lt_one
- Type: `{n : ℕ} (hn : 1 ≤ n) : ‖zetaSys p n - 1‖ < 1`
- What: The cyclotomic generator `ξ_n` is a 1-unit for `n ≥ 1`, i.e. `‖ξ_n − 1‖ < 1`.
- How: Rewrites `ξ_n − 1 = π_n` (the uniformiser) and applies `norm_pi_lt_one`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [`zetaSys`, `norm_pi_lt_one`, `pi`]
- Used by: `zpPow_zetaSys'`, `ZpOne` (mul/one/inv_mem'), `evalPi_binomialSeries` (indirectly via callers)
- Visibility: private
- Lines: 39–41 (proof 2 lines)
- Notes: none

### theorem mahlerTransform_phiSeries
- Type: `(μ : PadicMeasure p ℤ_[p]) : mahlerTransform p (phi p μ) = phiSeries p (mahlerTransform p μ)`
- What: The Mahler transform of `φμ` equals `phiSeries` applied to `𝓐μ` over `ℤ_[p]` (both are `subst((1+T)^p − 1)`).
- How: Direct application of `PadicMeasure.mahlerTransform_phi`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.mahlerTransform`, `PadicMeasure.phi`, `phiSeries`, `PadicMeasure.mahlerTransform_phi`]
- Used by: `existsUnique_measure_digits`, `mahlerTransform_psi`, `mahlerTransform_res_units`
- Visibility: private
- Lines: 55–58 (proof 1 line)
- Notes: none

### theorem mahlerTransform_dirac_natCast
- Type: `(i : ℕ) : mahlerTransform p (dirac p ((i:ℕ):ℤ_[p])) = (1 + PowerSeries.X) ^ i`
- What: The Mahler transform of the Dirac measure at a natural `i` is `(1+T)^i`.
- How: `mahlerTransform_dirac` then `binomialSeries_nat`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.mahlerTransform`, `PadicMeasure.dirac`, `PadicMeasure.mahlerTransform_dirac`]
- Used by: `existsUnique_measure_digits`, `mahlerTransform_psi`
- Visibility: private
- Lines: 61–64 (proof 1 line)
- Notes: none

### theorem mahlerTransform_sum
- Type: `{ι} (s : Finset ι) (m : ι → PadicMeasure p ℤ_[p]) : mahlerTransform p (∑ i ∈ s, m i) = ∑ i ∈ s, mahlerTransform p (m i)`
- What: The Mahler transform is additive over finite sums.
- How: `map_sum` on the linear-map form `mahlerTransformₗ`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.mahlerTransform`, `PadicMeasure.mahlerTransformₗ`]
- Used by: `existsUnique_measure_digits`, `mahlerTransform_psi`
- Visibility: private
- Lines: 67–71 (proof 1 line)
- Notes: none

### theorem psi_add
- Type: `(μ ν : PadicMeasure p ℤ_[p]) : psi p (μ + ν) = psi p μ + psi p ν`
- What: The operator `ψ` is additive in its measure argument.
- How: `LinearMap.ext`, unfold to underlying measure addition via `LinearMap.add_apply`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.psi`]
- Used by: `psi_sum`
- Visibility: private
- Lines: 74–78 (proof 3 lines)
- Notes: none

### theorem psi_zero
- Type: `psi p (0 : PadicMeasure p ℤ_[p]) = 0`
- What: `ψ` of the zero measure is zero.
- How: `LinearMap.ext` + `LinearMap.zero_apply`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.psi`]
- Used by: `psi_sum`
- Visibility: private
- Lines: 81–82 (proof 1 line)
- Notes: none

### theorem psi_sum
- Type: `{ι} (s : Finset ι) (m : ι → PadicMeasure p ℤ_[p]) : psi p (∑ i ∈ s, m i) = ∑ i ∈ s, psi p (m i)`
- What: `ψ` is additive over a finite sum.
- How: `Finset.induction_on` with `psi_zero` (base) and `psi_add` (step).
- Hypotheses: none.
- Uses from project: [`PadicMeasure.psi`, `psi_zero`, `psi_add`]
- Used by: `psi_dirac_neg_mul_sum`
- Visibility: private
- Lines: 85–90 (proof 4 lines)
- Notes: none

### theorem psi_dirac_mul_phi_eq_zero
- Type: `{a : ℤ_[p]} (ha : ‖a‖ = 1) (ν : PadicMeasure p ℤ_[p]) : psi p (dirac p a * phi p ν) = 0`
- What: A unit-translate of a `φ`-image is supported off `pℤ_p`, hence killed by `ψ`: `ψ(δ_a · φν) = 0` when `‖a‖ = 1`.
- How: Unfolds `psi`/`phi`/pushforward and shows the relevant continuous function is `0` because `a + pz ∉ {y : ‖y‖ < 1}`; hinges on the ultrametric inequality `IsUltrametricDist.norm_add_le_max` and `Set.indicator_of_notMem`.
- Hypotheses: `‖a‖ = 1` (`a` a unit).
- Uses from project: [`PadicMeasure.psi`, `PadicMeasure.dirac`, `PadicMeasure.phi`, `PadicMeasure.dirac_apply`, `PadicMeasure.convInner_apply`, `PadicMeasure.mul_apply`, `PadicMeasure.pushforward_apply`, `PadicMeasure.isClopen_pZp`, `PadicMeasure.shiftDiv`, `PadicMeasure.mulCM`, `PadicMeasure.mem_pZp_of_mul`]
- Used by: `psi_dirac_neg_mul_sum`
- Visibility: private
- Lines: 94–124 (proof ~28 lines)
- Notes: none

### theorem norm_natCast_sub_natCast_eq_one
- Type: `{i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) : ‖((i:ℕ):ℤ_[p]) - ((j:ℕ):ℤ_[p])‖ = 1`
- What: For distinct `i, j < p`, the difference of their `ℤ_[p]`-casts is a unit (norm 1).
- How: Reduces to `‖(m:ℤ_[p])‖ = 1` for `0 < m < p` via `PadicInt.norm_natCast_eq_one_iff` + `coprime_iff_not_dvd`; case-splits on `j ≤ i` vs `i ≤ j` using `Nat.cast_sub`.
- Hypotheses: `i < p`, `j < p`, `i ≠ j`.
- Uses from project: []
- Used by: `psi_dirac_neg_mul_sum`
- Visibility: private
- Lines: 128–138 (proof ~9 lines)
- Notes: none

### theorem psi_dirac_neg_mul_sum
- Type: `(ν : Fin p → PadicMeasure p ℤ_[p]) (j : Fin p) : psi p (dirac p (-((j:ℕ):ℤ_[p])) * ∑ i, dirac p ((i:ℕ):ℤ_[p]) * phi p (ν i)) = ν j`
- What: Digit extraction — applying `ψ(δ_{-j} · ·)` to the digit decomposition recovers the `j`-th digit `ν j`.
- How: `Finset.mul_sum` + `psi_sum` + `Finset.sum_eq_single j`; the `i = j` term gives `ψφ = id` (`psi_phi`, `dirac_mul_dirac`), the others vanish by `psi_dirac_mul_phi_eq_zero` with `norm_natCast_sub_natCast_eq_one`.
- Hypotheses: none beyond a family `ν : Fin p → ...` and index `j`.
- Uses from project: [`PadicMeasure.psi`, `PadicMeasure.dirac`, `PadicMeasure.phi`, `PadicMeasure.dirac_mul_dirac`, `PadicMeasure.one_def`, `PadicMeasure.psi_phi`, `psi_sum`, `psi_dirac_mul_phi_eq_zero`, `norm_natCast_sub_natCast_eq_one`]
- Used by: `mahlerTransform_psi`
- Visibility: private
- Lines: 142–155 (proof ~10 lines)
- Notes: none

### theorem existsUnique_measure_digits
- Type: `(μ : PadicMeasure p ℤ_[p]) : ∃! ν : Fin p → PadicMeasure p ℤ_[p], μ = ∑ i, dirac p ((i:ℕ):ℤ_[p]) * phi p (ν i)`
- What: The measure-level `p`-residue digit decomposition: every measure is uniquely `Σ_{i<p} δ_i · φ(ν_i)`.
- How: Transports the series-side `existsUnique_digits_padicInt` through `mahlerLinearEquiv`; existence by `mahlerTransform_injective` matching `𝓐` of the assembled measure, uniqueness via `IsDigitDecomp` + `hGuniq`. Hinges on `existsUnique_digits_padicInt` and `mahlerTransform_injective`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.mahlerTransform`, `PadicMeasure.dirac`, `PadicMeasure.phi`, `existsUnique_digits_padicInt`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.mahlerTransform_injective`, `mahlerTransform_sum`, `mahlerTransform_dirac_natCast`, `mahlerTransform_phiSeries`, `PadicMeasure.mahlerTransform_mul`, `PadicMeasure.mahlerLinearEquiv_symm_apply`, `PadicMeasure.mahlerTransform_ofPowerSeries`, `IsDigitDecomp`]
- Used by: `mahlerTransform_psi`
- Visibility: private
- Lines: 159–186 (proof ~24 lines)
- Notes: none

### theorem mahlerTransform_psi
- Type: `(μ : PadicMeasure p ℤ_[p]) : mahlerTransform p (psi p μ) = psiSeries p (mahlerTransform p μ)`
- What: Substrate (I) — the `ψ ↔ psiSeries` Mahler bridge for `PadicMeasure p ℤ_[p]`: `𝓐_{ψμ} = psiSeries 𝓐_μ`.
- How: Takes the unique digit family `ν` of `μ` (`existsUnique_measure_digits`); shows `ν 0 = ψ μ` via `psi_dirac_neg_mul_sum` at `j=0`, and that `(𝓐(ν i))` is the series digit decomposition of `𝓐μ`, then `psiSeries_eq_of_isDigitDecomp_padicInt`. Hinges on `existsUnique_measure_digits` and `psiSeries_eq_of_isDigitDecomp_padicInt`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.mahlerTransform`, `PadicMeasure.psi`, `psiSeries`, `existsUnique_measure_digits`, `psi_dirac_neg_mul_sum`, `PadicMeasure.one_def`, `mahlerTransform_sum`, `PadicMeasure.mahlerTransform_mul`, `mahlerTransform_dirac_natCast`, `mahlerTransform_phiSeries`, `IsDigitDecomp`, `psiSeries_eq_of_isDigitDecomp_padicInt`]
- Used by: `mahlerTransform_res_units`, `exists_invColeman_Col_eq`
- Visibility: public
- Lines: 192–210 (proof ~16 lines)
- Notes: none

### theorem evalPi_binomialSeries
- Type: `(a : ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) : evalPi p (binomialSeries ℤ_[p] a) n = zpPow p (zetaSys p n) a`
- What: The binomial series evaluated at `π_n` gives `ξ_n^a` for `n ≥ 1` (`(1+π_n)^a = ξ_n^a`).
- How: Unfolds `evalPi`, applies `seriesEval_map_binomialSeries` at `z = π_n` (using `norm_pi_lt_one`), and rewrites `1 + π_n = ξ_n`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [`evalPi`, `seriesEval_map_binomialSeries`, `norm_pi_lt_one`, `pi`, `zetaSys`, `zpPow`]
- Used by: `normOp_binomialSeries`, `colemanSeries_eq_binomialSeries_of_mem_ZpOne`, `mem_ker_Col_iff_mem_ZpOne`
- Visibility: public
- Lines: 222–225 (proof 2 lines)
- Notes: none

### theorem levelNorm_zetaSys
- Type: `(hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) : levelNorm p n (zetaSys p (n+1)) = zetaSys p n`
- What: The cyclotomic norm of `ξ_{n+1}` (RJW TeX 2581–2585, `b=1`): for `n ≥ 1`, `p` odd, `N_{n+1,n}(ξ_{n+1}) = ξ_n`.
- How: Realises `ξ_{n+1}` as `extendScalars` generator `W` with `W^p = ξ_n`; minimal polynomial `X^p − C(ξ_n)` (`minpoly_extendScalars_of_pow`), generator-norm `= (−1)^p·coeff₀ = (−1)^p·(−ξ_n) = ξ_n` for `p` odd via `Algebra.norm_eq_norm_adjoin`, `Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly`, `odd_of_ne_two`.
- Hypotheses: `p ≠ 2` (false at `p=2`, errata #14); `n ≥ 1`.
- Uses from project: [`levelNorm`, `zetaSys`, `K`, `K_le_succ`, `zetaSys_mem_K`, `primitiveRoot_notMem_K`, `extendScalars_adjoin_eq_top`, `zetaSys_primitiveRoot`, `minpoly_extendScalars_of_pow`, `zetaSys_pow_p`, `levelNorm_apply`]
- Used by: `levelNorm_zetaSys_pow`
- Visibility: private
- Lines: 243–290 (proof ~46 lines)
- Notes: long(30–50); `set_option synthInstance.maxHeartbeats 1000000`, `set_option maxHeartbeats 1000000` (nested IntermediateField synthesis)

### theorem levelNorm_zetaSys_pow
- Type: `(hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : levelNorm p n (zetaSys p (n+1) ^ k) = zetaSys p n ^ k`
- What: The ℕ-power form of the cyclotomic norm: `N_{n+1,n}(ξ_{n+1}^k) = ξ_n^k`.
- How: Induction on `k` using `levelNorm` multiplicativity (`levelNorm_mul`, `levelNorm_one`) and the base case `levelNorm_zetaSys`.
- Hypotheses: `p ≠ 2`; `n ≥ 1`.
- Uses from project: [`levelNorm`, `zetaSys`, `levelNorm_one`, `levelNorm_mul`, `zetaSys_mem_K`, `levelNorm_zetaSys`]
- Used by: `levelNorm_zpPow_zetaSys`
- Visibility: private
- Lines: 294–301 (proof ~6 lines)
- Notes: none

### theorem zpPow_zetaSys'
- Type: `{n : ℕ} (hn : 1 ≤ n) (c : ℤ_[p]) : zpPow p (zetaSys p n) c = zetaSys p n ^ ((toZModPow n c : ZMod (p^n)).val)`
- What: The `ℤ_p`-power `ξ_n^c` equals the integer power `ξ_n^{(toZModPow n c).val}` (the `p^n`-periodicity of `ξ_n^·`). Un-`private` re-derivation of `GaloisAction.zpPow_zetaSys`.
- How: Both sides continuous in `c` and agree on `c ∈ ℕ`; uses `addChar_of_value_at_one` continuity for the LHS, local-constancy of `toZModPow` for the RHS, `zetaSys_pow_eq_pow_of_modEq` for naturals, then `denseRange_natCast.equalizer`. Hinges on `PadicInt.denseRange_natCast.equalizer` and `zetaSys_pow_eq_pow_of_modEq`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [`zpPow`, `zetaSys`, `norm_zetaSys_sub_one_lt_one`, `zpPow_natCast`, `zetaSys_pow_eq_pow_of_modEq`, `PadicMeasure.isOpen_toZModPow_fiber`]
- Used by: `levelNorm_zpPow_zetaSys`
- Visibility: private
- Lines: 306–328 (proof ~22 lines)
- Notes: none

### theorem levelNorm_zpPow_zetaSys
- Type: `(hp2 : p ≠ 2) (a : ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) : levelNorm p n (zpPow p (zetaSys p (n+1)) a) = zpPow p (zetaSys p n) a`
- What: The cyclotomic norm of `zpPow` (RJW TeX 2581–2585, generalised to `ℤ_p`-exponents): `N_{n+1,n}(ξ_{n+1}^a) = ξ_n^a`, norm-compatibility of the Tate-twist tower.
- How: Reduces to the ℕ-power case via `zpPow_zetaSys'` at both levels, applies `levelNorm_zetaSys_pow`, then matches exponents using `zetaSys_pow_eq_pow_of_modEq` and `PadicInt.cast_toZModPow` (`toZModPow (n+1) a ≡ toZModPow n a mod p^n`).
- Hypotheses: `p ≠ 2` (false at `p=2`, errata #14); `n ≥ 1`.
- Uses from project: [`levelNorm`, `zpPow`, `zetaSys`, `zpPow_zetaSys'`, `levelNorm_zetaSys_pow`, `zetaSys_pow_eq_pow_of_modEq`]
- Used by: `normOp_binomialSeries`
- Visibility: private
- Lines: 341–353 (proof ~11 lines)
- Notes: none

### theorem normOp_binomialSeries
- Type: `(hp2 : p ≠ 2) (a : ℤ_[p]) : normOp (binomialSeries ℤ_[p] a) = binomialSeries ℤ_[p] a`
- What: Substrate (II) — the binomial series is `𝒩`-fixed: `𝒩(binomialSeries a) = binomialSeries a`.
- How: By `evalPi_injective` reduces to the evaluation/norm square `evalPi_normOp`, which reads `levelNorm(ξ_{n+1}^a) = ξ_n^a` (`levelNorm_zpPow_zetaSys`) via `evalPi_binomialSeries`.
- Hypotheses: `p ≠ 2` (inherited from `levelNorm_zpPow_zetaSys`, errata #14).
- Uses from project: [`normOp`, `evalPi_injective`, `evalPi_normOp`, `evalPi_binomialSeries`, `levelNorm_zpPow_zetaSys`]
- Used by: `mem_ker_Col_iff_mem_ZpOne`
- Visibility: public
- Lines: 359–363 (proof ~4 lines)
- Notes: none

### theorem colemanSeries_eq_binomialSeries_of_mem_ZpOne
- Type: `{u : NormCompatUnits p} {a : ℤ_[p]} (ha : ∀ n, 1 ≤ n → ((u.elems n :ℂ_[p]ˣ):ℂ_[p]) = zpPow p (zetaSys p n) a) : colemanSeries p u = binomialSeries ℤ_[p] a`
- What: For `u ∈ ZpOne` with parameter `a`, the Coleman series is the binomial series.
- How: Both are `𝒩`-fixed units interpolating `ξ_n^a`, so agree by Coleman uniqueness (`evalPi_injective` + `evalPi_colemanSeries` + `evalPi_binomialSeries`); only the interpolation `ha` enters, no `hp2`.
- Hypotheses: `u` interpolates `ξ_n^a` for all `n ≥ 1`.
- Uses from project: [`colemanSeries`, `NormCompatUnits`, `zpPow`, `zetaSys`, `evalPi_injective`, `evalPi_colemanSeries`, `evalPi_binomialSeries`]
- Used by: `mem_ker_Col_iff_mem_ZpOne`
- Visibility: public
- Lines: 370–374 (proof ~2 lines)
- Notes: none

### def ZpOne
- Type: `Subgroup (NormCompatUnits p)` with carrier `{u | ∃ a : ℤ_[p], ∀ n, 1 ≤ n → (u.elems n : ...) = zpPow p (zetaSys p n) a}`
- What: RJW def:Zp(1) (TeX 3407–3409) — the integral Tate twist `ℤ_p(1) = {(ξ_n^a)_n}` as a subgroup of the unit tower; `u ∈ ℤ_p(1)` iff there is a single `a` with `u_n = ξ_n^a` for all `n ≥ 1`.
- How: Subgroup laws are the character laws of `zpPow`: `mul_mem'` uses `zpPow_add` with parameter `a+b`; `one_mem'` uses `zpPow_natCast`/`pow_zero` with `0`; `inv_mem'` uses `zpPow_add`/`add_neg_cancel` with `−a`.
- Hypotheses: membership requires existence of a single exponent `a`.
- Uses from project: [`NormCompatUnits`, `zpPow`, `zetaSys`, `zpPow_add`, `norm_zetaSys_sub_one_lt_one`, `zpPow_natCast`]
- Used by: `mem_ker_Col_iff_mem_ZpOne`
- Visibility: public
- Lines: 382–410 (proof/fields ~28 lines)
- Notes: none

### theorem coeff_S_pow_vanish
- Type: `{d n : ℕ} (hdn : n < d) : coeff n (((1+X)^p - 1)^d) = 0`
- What: `[Tⁿ](Sᵈ) = 0` for `n < d`, where `S = (1+T)^p − 1` has order 1.
- How: Writes `S = X·U` (`X_dvd_iff`), so `S^d = X^d·U^d`; `coeff_X_pow_mul'` with `if_neg`.
- Hypotheses: `n < d`.
- Uses from project: []
- Used by: `coeff_phiSeries_split`
- Visibility: private
- Lines: 420–424 (proof ~3 lines)
- Notes: none

### theorem coeff_phiSeries_split
- Type: `(F : PowerSeries ℤ_[p]) (n : ℕ) : coeff n (phiSeries p F) = ∑ d ∈ range (n+1), (coeff d F) • coeff n (((1+X)^p-1)^d)`
- What: The finite substitution-coefficient formula `[Tⁿ](φF) = Σ_{d≤n} F_d·[Tⁿ](Sᵈ)`.
- How: `coeff_subst'` (using `hasSubst_one_add_X_pow_sub_one`) then `finsum_eq_finsetSum_of_support_subset`, cutting the support to `range(n+1)` via `coeff_S_pow_vanish`.
- Hypotheses: none.
- Uses from project: [`phiSeries`, `hasSubst_one_add_X_pow_sub_one`, `coeff_S_pow_vanish`]
- Used by: `phiHom_fixed_eq_C`
- Visibility: private
- Lines: 427–437 (proof ~7 lines)
- Notes: none

### theorem coeff_one_one_add_X_pow
- Type: `coeff 1 ((1+X : PowerSeries ℤ_[p])^p) = (p : ℤ_[p])`
- What: `[T¹]((1+T)^p) = p`.
- How: Rewrites via `binomialSeries_nat`, `binomialSeries_coeff`, `Ring.choose_one_right`.
- Hypotheses: none.
- Uses from project: []
- Used by: `coeff_S_pow_diag`
- Visibility: private
- Lines: 440–443 (proof ~2 lines)
- Notes: none

### theorem coeff_S_pow_diag
- Type: `{d : ℕ} : coeff d (((1+X)^p - 1)^d) = (p : ℤ_[p])^d`
- What: `[Tⁿ](Sⁿ) = pⁿ` (the leading coefficient of `S = pT + O(T²)`).
- How: Writes `S = X·U` (`X_dvd_iff`), computes `constantCoeff U = p` (via `coeff_one_one_add_X_pow`), then `coeff d (X^d·U^d) = constantCoeff(U^d) = p^d`.
- Hypotheses: none.
- Uses from project: [`coeff_one_one_add_X_pow`]
- Used by: `phiHom_fixed_eq_C`
- Visibility: private
- Lines: 446–461 (proof ~15 lines)
- Notes: none

### theorem isUnit_one_sub_p_pow
- Type: `{n : ℕ} (hn : 1 ≤ n) : IsUnit (1 - (p : ℤ_[p])^n)`
- What: `1 − pⁿ` is a unit of `ℤ_[p]` for `n ≥ 1`.
- How: `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits`; `pⁿ` is a nonunit since `‖p‖ < 1` gives `‖pⁿ‖ < 1`.
- Hypotheses: `n ≥ 1`.
- Uses from project: []
- Used by: `phiHom_fixed_eq_C`
- Visibility: private
- Lines: 464–469 (proof ~5 lines)
- Notes: none

### theorem phiHom_fixed_eq_C
- Type: `{F : PowerSeries ℤ_[p]} (h : F - phiHom p F = 0) : F = C (constantCoeff F)`
- What: Kernel half of `lem:rest zp*` — the `φ`-fixed series are the constants: `(1−φ)F = 0 ⟹ F = C(F₀)`.
- How: Strong induction on coefficient index `n`: from `coeff_phiSeries_split` the diagonal `pⁿ` term (`coeff_S_pow_diag`) and vanishing sub-diagonal give `(1−pⁿ)F_n = 0`, killed by the unit `1−pⁿ` (`isUnit_one_sub_p_pow`). Hinges on `coeff_phiSeries_split`, `coeff_S_pow_diag`, `isUnit_one_sub_p_pow`.
- Hypotheses: `(1−φ)F = 0`.
- Uses from project: [`phiHom`, `phiHom_apply`, `phiSeries`, `coeff_phiSeries_split`, `coeff_S_pow_diag`, `isUnit_one_sub_p_pow`]
- Used by: `mem_ker_Col_iff_mem_ZpOne`
- Visibility: private
- Lines: 474–508 (proof ~34 lines)
- Notes: long(30–50)

### theorem succ_mul_ringChoose
- Type: `(r : ℤ_[p]) (n : ℕ) : ((n:ℤ_[p])+1) * Ring.choose r (n+1) = (r - (n:ℤ_[p])) * Ring.choose r n`
- What: The descending-Pochhammer recursion for `Ring.choose` over `ℤ_[p]` (engine of the binomial-series derivative identity). Re-derivation of a `GaloisAction` private helper.
- How: Expresses both `Ring.choose` via `descPochhammer.smeval` (`descPochhammer_eq_factorial_smul_choose`), uses `descPochhammer_succ_right` + `smeval_mul`, cancels the factorial (`mul_left_cancel₀`), closes with `linear_combination`.
- Hypotheses: none.
- Uses from project: []
- Used by: `one_add_X_mul_derivative_binomialSeries`
- Visibility: private
- Lines: 520–537 (proof ~17 lines)
- Notes: none

### theorem coeff_binomialSeries'
- Type: `(r : ℤ_[p]) (k : ℕ) : coeff k (binomialSeries ℤ_[p] r) = Ring.choose r k`
- What: The `k`-th coefficient of the binomial series is `binom(r,k)`.
- How: `binomialSeries_coeff` + `smul_eq_mul` + `mul_one`.
- Hypotheses: none.
- Uses from project: []
- Used by: `one_add_X_mul_derivative_binomialSeries`, `isUnit_binomialSeries`, `eq_C_mul_binomialSeries_of_dlog_eq_C`
- Visibility: private
- Lines: 540–542 (proof 1 line)
- Notes: none

### theorem one_add_X_mul_derivative_binomialSeries
- Type: `(r : ℤ_[p]) : (1+X) * derivativeFun (binomialSeries ℤ_[p] r) = r • binomialSeries ℤ_[p] r`
- What: The binomial-series derivative identity `(1+T)·(binomialSeries r)′ = r·binomialSeries r`. Re-derivation of a `GaloisAction` private helper.
- How: Coefficient-wise (`ext n`), splits `(1+X)·B′`, uses `coeff_binomialSeries'`, `coeff_derivativeFun`; the `succ m` case closes via `succ_mul_ringChoose` and `linear_combination`.
- Hypotheses: none.
- Uses from project: [`coeff_binomialSeries'`, `succ_mul_ringChoose`]
- Used by: `dlog_binomialSeries`
- Visibility: private
- Lines: 546–567 (proof ~21 lines)
- Notes: none

### theorem isUnit_binomialSeries
- Type: `(c : ℤ_[p]) : IsUnit (binomialSeries ℤ_[p] c)`
- What: The binomial series is a unit (constant coefficient `binom(c,0) = 1`).
- How: `isUnit_iff_constantCoeff` + `coeff_binomialSeries'` + `Ring.choose_zero_right` = 1.
- Hypotheses: none.
- Uses from project: [`coeff_binomialSeries'`]
- Used by: `dlog_binomialSeries`, `eq_C_mul_binomialSeries_of_dlog_eq_C`, `mem_ker_Col_iff_mem_ZpOne`
- Visibility: private
- Lines: 570–574 (proof ~3 lines)
- Notes: none

### theorem dlog_binomialSeries
- Type: `(c : ℤ_[p]) : dlog p (binomialSeries ℤ_[p] c) = C c`
- What: `∂log(binomialSeries c) = C c`.
- How: Unfolds `dlog`, applies `one_add_X_mul_derivative_binomialSeries`, cancels the unit via `Ring.mul_inverse_cancel` (`isUnit_binomialSeries`).
- Hypotheses: none.
- Uses from project: [`dlog`, `one_add_X_mul_derivative_binomialSeries`, `isUnit_binomialSeries`]
- Used by: `eq_C_mul_binomialSeries_of_dlog_eq_C`, `mem_ker_Col_iff_mem_ZpOne`
- Visibility: private
- Lines: 577–580 (proof ~2 lines)
- Notes: none

### theorem dlogMul
- Type: `{g h : PowerSeries ℤ_[p]} (hg : IsUnit g) (hh : IsUnit h) : dlog p (g*h) = dlog p g + dlog p h`
- What: `∂log` is additive on units.
- How: Unfolds the three `dlog`s, uses `derivativeFun_mul` (Leibniz), `Ring.mul_inverse_rev`, and two `ring`-normalised regroupings cancelling `g·g⁻¹` and `h·h⁻¹` via `Ring.mul_inverse_cancel`.
- Hypotheses: `g, h` units.
- Uses from project: [`dlog`]
- Used by: `dlogInverse`, `eq_C_mul_binomialSeries_of_dlog_eq_C`
- Visibility: private
- Lines: 583–594 (proof ~10 lines)
- Notes: none

### theorem dlogOne
- Type: `dlog p (1 : PowerSeries ℤ_[p]) = 0`
- What: `∂log 1 = 0`.
- How: Unfolds `dlog`, uses `derivativeFun_one` = 0.
- Hypotheses: none.
- Uses from project: [`dlog`]
- Used by: `dlogInverse`
- Visibility: private
- Lines: 597–598 (proof 1 line)
- Notes: none

### theorem isUnit_ringInverse
- Type: `{g : PowerSeries ℤ_[p]} (hg : IsUnit g) : IsUnit (Ring.inverse g)`
- What: `Ring.inverse` of a unit is a unit.
- How: Destructs `hg` to a unit `v`, `Ring.inverse_unit` = `v⁻¹`, which is a unit.
- Hypotheses: `g` a unit.
- Uses from project: []
- Used by: `dlogInverse`, `eq_C_mul_binomialSeries_of_dlog_eq_C`
- Visibility: private
- Lines: 601–603 (proof 1 line)
- Notes: none

### theorem dlogInverse
- Type: `{g : PowerSeries ℤ_[p]} (hg : IsUnit g) : dlog p (Ring.inverse g) = - dlog p g`
- What: `∂log(g⁻¹) = −∂log g` for a unit `g`.
- How: From `∂log(g·g⁻¹) = ∂log 1 = 0` (`dlogMul` + `dlogOne` + `mul_inverse_cancel`), so `eq_neg_of_add_eq_zero_right`.
- Hypotheses: `g` a unit.
- Uses from project: [`dlog`, `dlogMul`, `dlogOne`, `isUnit_ringInverse`]
- Used by: `eq_C_mul_binomialSeries_of_dlog_eq_C`
- Visibility: private
- Lines: 606–612 (proof ~5 lines)
- Notes: none

### theorem eq_C_constantCoeff_of_derivativeFun_zero
- Type: `{g : PowerSeries ℤ_[p]} (h : derivativeFun g = 0) : g = C (constantCoeff g)`
- What: A power series with vanishing formal derivative equals its constant coefficient (`ℤ_[p]` is a domain). Re-derivation of a `LogDerivative` private helper.
- How: Coefficient-wise; the `succ m` case uses `coeff_derivativeFun` giving `(m+1)·coeff(m+1) g = 0` and cancels `(m+1) ≠ 0`.
- Hypotheses: `derivativeFun g = 0`.
- Uses from project: []
- Used by: `eq_C_mul_binomialSeries_of_dlog_eq_C`
- Visibility: private
- Lines: 616–629 (proof ~13 lines)
- Notes: none

### theorem eq_C_mul_binomialSeries_of_dlog_eq_C
- Type: `{g : PowerSeries ℤ_[p]} (hg : IsUnit g) {c : ℤ_[p]} (hd : dlog p g = C c) : g = C (constantCoeff g) * binomialSeries ℤ_[p] c`
- What: The `∂log = C c` ODE — a unit `g` with `∂log g = C c` is `C(g₀)·binomialSeries c`.
- How: Sets `h = g·(binomialSeries c)⁻¹`; shows `∂log h = 0` (`dlogMul`, `dlogInverse`, `dlog_binomialSeries`), hence `h′ = 0` (cancel units `1+X` and `h`), so `h = C(h₀)` (`eq_C_constantCoeff_of_derivativeFun_zero`) with `h₀ = g₀` since `B₀=1`. Hinges on `eq_C_constantCoeff_of_derivativeFun_zero`, `dlog_binomialSeries`.
- Hypotheses: `g` a unit; `∂log g = C c`.
- Uses from project: [`dlog`, `binomialSeries`, `isUnit_binomialSeries`, `isUnit_ringInverse`, `dlogMul`, `dlogInverse`, `dlog_binomialSeries`, `eq_C_constantCoeff_of_derivativeFun_zero`, `coeff_binomialSeries'`]
- Used by: `mem_ker_Col_iff_mem_ZpOne`
- Visibility: private
- Lines: 635–673 (proof ~38 lines)
- Notes: long(30–50)

### theorem mahlerTransform_res_units
- Type: `(μ : PadicMeasure p ℤ_[p]) : mahlerTransform p (res p (isClopen_units p) μ) = mahlerTransform p μ - phiSeries p (psiSeries p (mahlerTransform p μ))`
- What: `𝓐(Res_{ℤ_p^×} μ) = 𝓐μ − φ(ψ 𝓐μ)`, the restriction `Res = 1 − φψ` transported through `𝓐`.
- How: `res_units_eq` (`Res = 1 − φψ`) then `map_sub` of `mahlerTransformₗ` and the two Mahler bridges `mahlerTransform_phiSeries`, `mahlerTransform_psi`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.mahlerTransform`, `PadicMeasure.res`, `PadicMeasure.isClopen_units`, `PadicMeasure.res_units_eq`, `PadicMeasure.phi`, `PadicMeasure.psi`, `PadicMeasure.mahlerTransformₗ`, `phiSeries`, `psiSeries`, `mahlerTransform_phiSeries`, `mahlerTransform_psi`]
- Used by: `Col_eq_zero_iff`, `Col_apply_unitsPowCM_one_eq_zero`, `exists_invColeman_Col_eq`
- Visibility: private
- Lines: 685–694 (proof ~6 lines)
- Notes: none

### theorem unitsCmul_invCM_eq_zero_iff
- Type: `(ν : PadicMeasure p ℤ_[p]ˣ) : unitsCmul p (invCM p) ν = 0 ↔ ν = 0`
- What: Multiplication by the unit-valued `x⁻¹` is injective on measures: `unitsCmul invCM ν = 0 ↔ ν = 0`.
- How: Forward: cancel by multiplying back by `x = unitsPowCM 1`, using `invCM · unitsPowCM 1 = 1` pointwise (`inv_mul_cancel`).
- Hypotheses: none.
- Uses from project: [`PadicMeasure.unitsCmul`, `PadicMeasure.invCM`, `PadicMeasure.unitsPowCM`, `PadicMeasure.unitsCmul_apply`]
- Used by: `Col_eq_zero_iff`
- Visibility: private
- Lines: 698–710 (proof ~10 lines)
- Notes: none

### theorem Col_eq_zero_iff
- Type: `(u : NormCompatUnits p) : Col p u = 0 ↔ dlog p (colemanSeries p u) - phiHom p (dlog p (colemanSeries p u)) = 0`
- What: The kernel transport: `Col u = 0 ↔ (1−φ)(∂log f_u) = 0`.
- How: Peels `unitsCmul invCM` (`unitsCmul_invCM_eq_zero_iff`), then `(·).comp extendByZero` through `ι` injective (`iota_comp_extendByZero`, `iota_injective`), lands on `Res_{ℤ_p^×}(𝓐⁻¹(∂log f_u)) = 0`; `𝓐` injective + `mahlerTransform_res_units` give the result using `dlog_mem_psiIdSeries`. Hinges on `mahlerTransform_res_units`, `dlog_mem_psiIdSeries`.
- Hypotheses: none.
- Uses from project: [`Col`, `colemanSeries`, `dlog`, `phiHom`, `phiHom_apply`, `psiSeries`, `dlog_mem_psiIdSeries`, `colemanSeries_isUnit`, `normOp_colemanSeries`, `unitsCmul_invCM_eq_zero_iff`, `PadicMeasure.iota`, `PadicMeasure.iota_injective`, `iota_comp_extendByZero`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.mahlerLinearEquiv_apply`, `mahlerTransform_res_units`, `PadicMeasure.mahlerLinearEquiv_symm_apply`, `PadicMeasure.mahlerTransform_ofPowerSeries`]
- Used by: `mem_ker_Col_iff_mem_ZpOne`
- Visibility: private
- Lines: 717–729 (proof ~12 lines)
- Notes: none

### theorem oneUnit_pow_p_sub_one_eq_one
- Type: `{x : ℤ_[p]} (hx : ‖x - 1‖ < 1) (hpow : x^(p-1) = 1) : x = 1`
- What: A principal unit (`‖x − 1‖ < 1`) that is a `(p−1)`-th root of unity is `1`.
- How: Factors `x^{p−1} − 1 = S·(x − 1)` (`geom_sum_mul`); the geometric sum `S = ∑ xⁱ ≡ p−1 mod (x−1)` is a unit (`‖p−1‖=1`, ultrametric), so `x − 1 = 0` (`IsUnit.mul_left_cancel`). Hinges on the ultrametric norm lemmas and `geom_sum_mul`.
- Hypotheses: `‖x − 1‖ < 1`; `x^{p−1} = 1`.
- Uses from project: []
- Used by: `mem_ker_Col_iff_mem_ZpOne`
- Visibility: private
- Lines: 734–772 (proof ~38 lines)
- Notes: long(30–50)

### theorem mem_ker_Col_iff_mem_ZpOne
- Type: `(hp2 : p ≠ 2) {u : NormCompatUnits p} (hu : u ∈ unitsTower1 p) : Col p u = 0 ↔ u ∈ ZpOne p`
- What: RJW thm:fund exact seq, left-exactness — the kernel of `Col` on `𝒰_{∞,1}` is `ℤ_p(1)`.
- How: `Col_eq_zero_iff` reduces to `(1−φ)(∂log g)=0`; forward then runs `phiHom_fixed_eq_C` (`∂log g = C c`), the ODE `eq_C_mul_binomialSeries_of_dlog_eq_C`, `𝒩`-fixedness (`normOp_binomialSeries`, `normOp_mul`, `normOp_C`) forcing `g₀^p = g₀`, with `g₀` a principal unit (interpolation `evalPi_colemanSeries`/`evalPi_binomialSeries`), so `g₀=1` (`oneUnit_pow_p_sub_one_eq_one`); backward uses `colemanSeries_eq_binomialSeries_of_mem_ZpOne` + `subst_C`. Hinges on `phiHom_fixed_eq_C`, `eq_C_mul_binomialSeries_of_dlog_eq_C`, `normOp_binomialSeries`, `oneUnit_pow_p_sub_one_eq_one`.
- Hypotheses: `p ≠ 2` (forward uses `normOp_binomialSeries`, false at `p=2`, errata #14); `u ∈ 𝒰_{∞,1}`.
- Uses from project: [`Col`, `colemanSeries`, `colemanSeries_isUnit`, `ZpOne`, `unitsTower1`, `Col_eq_zero_iff`, `dlog`, `phiHom_fixed_eq_C`, `eq_C_mul_binomialSeries_of_dlog_eq_C`, `evalPi_colemanSeries`, `evalPi_mul`, `evalPi_binomialSeries`, `evalPi_C`, `mem_localUnitsOne_iff`, `zpPow`, `zetaSys`, `norm_zpPow_sub_one_lt_one`, `norm_zetaSys_sub_one_lt_one`, `toCp`, `norm_toCp`, `normOp_colemanSeries`, `normOp`, `normOp_mul`, `normOp_C`, `normOp_binomialSeries`, `isUnit_binomialSeries`, `oneUnit_pow_p_sub_one_eq_one`, `binomialSeries`]
- Used by: unused in file
- Visibility: public
- Lines: 791–864 (proof ~72 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem invCM_mul_unitsPowCM_one
- Type: `invCM p * unitsPowCM p 1 = 1`
- What: `x⁻¹ · x = 1` on `ℤ_p^×` pointwise (`invCM · unitsPowCM 1 = 1`).
- How: `ContinuousMap.ext`, simp the products, `inv_mul_cancel` on units.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.invCM`, `PadicMeasure.unitsPowCM`]
- Used by: `Col_apply_unitsPowCM_one_eq_zero`, `exists_invColeman_Col_eq`
- Visibility: private
- Lines: 867–872 (proof ~5 lines)
- Notes: none

### theorem mahler_zero_eq_one
- Type: `(mahler 0 : C(ℤ_[p], ℤ_[p])) = 1`
- What: The 0-th Mahler basis function is constant 1 (`mahler 0 x = binom(x,0) = 1`).
- How: `ContinuousMap.ext`, `mahler_apply` + `Ring.choose_zero_right`.
- Hypotheses: none.
- Uses from project: [`mahler`, `mahler_apply`]
- Used by: `Col_apply_unitsPowCM_one_eq_zero`, `exists_invColeman_Col_eq`
- Visibility: private
- Lines: 875–877 (proof ~2 lines)
- Notes: none

### theorem Col_apply_unitsPowCM_one_eq_zero
- Type: `(u : NormCompatUnits p) : Col p u (unitsPowCM p 1) = 0`
- What: Forward inclusion of the cokernel (image ⊆ ker χ-moment): `Col u (unitsPowCM 1) = 0`.
- How: The `x⁻¹`-multiplication cancels (`invCM_mul_unitsPowCM_one`), `extendByZero 1 = 𝟙_{ℤ_p^×}`, reducing to `constantCoeff((1−φψ)(∂log f_u))`, which vanishes since `φ`, `ψ` fix constant coefficients (`constantCoeff_phiSeries`) and `∂log f_u ∈ ψ=id` (`dlog_mem_psiIdSeries`). Hinges on `mahlerTransform_res_units`, `dlog_mem_psiIdSeries`.
- Hypotheses: none.
- Uses from project: [`Col`, `colemanSeries`, `colemanSeries_isUnit`, `dlog`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.extendByZero`, `PadicMeasure.unitsValCM`, `PadicMeasure.extendByZero_comp_unitsVal`, `PadicMeasure.unitsCmul_apply`, `invCM_mul_unitsPowCM_one`, `mahler`, `mahler_zero_eq_one`, `PadicMeasure.res`, `PadicMeasure.isClopen_units`, `PadicMeasure.coeff_mahlerTransform`, `mahlerTransform_res_units`, `constantCoeff_phiSeries`, `PadicMeasure.mahlerLinearEquiv_symm_apply`, `PadicMeasure.mahlerTransform_ofPowerSeries`, `psiSeries`, `dlog_mem_psiIdSeries`, `normOp_colemanSeries`]
- Used by: `range_Col_eq_ker_chiMoment`
- Visibility: public
- Lines: 883–904 (proof ~22 lines)
- Notes: none

### theorem evalPi_unit_ne_zero
- Type: `{g : PowerSeries ℤ_[p]} (hg : IsUnit g) {n : ℕ} (hn : 1 ≤ n) : evalPi p g n ≠ 0`
- What: For a unit series `g` and `n ≥ 1`, the value `g(π_n) = evalPi g n` is nonzero.
- How: `evalPi(·) n` is a ring hom, so sends the unit `g` to a unit of `ℂ_[p]`; `left_ne_zero_of_mul_eq_one` on `evalPi g · evalPi g⁻¹ = 1`.
- Hypotheses: `g` a unit; `n ≥ 1`.
- Uses from project: [`evalPi`, `evalPi_mul`, `evalPi_one`]
- Used by: `invColeman`, `colemanSeries_invColeman`, `exists_invColeman_Col_eq`
- Visibility: private
- Lines: 919–924 (proof ~4 lines)
- Notes: none

### def invColeman
- Type: `(g : PowerSeries ℤ_[p]) (hg : IsUnit g) (hN : normOp g = g) : NormCompatUnits p`
- What: The inverse Coleman map (core) — from a `𝒩`-fixed unit `g`, the norm-compatible system `u` with `u_n = g(π_n)` for `n ≥ 1` (junk `1` at level 0).
- How: `elems n = mk0 (evalPi g n)` for `n≥1`; `mem`/`inv_mem` are `evalPi_mem_O` (value and ring-hom inverse lie in `𝒪_n`); `compat` is `evalPi_normOp` + `𝒩 g = g`.
- Hypotheses: `g` a unit; `normOp g = g`.
- Uses from project: [`NormCompatUnits`, `evalPi`, `evalPi_unit_ne_zero`, `evalPi_mem_O`, `O`, `evalPi_mul`, `evalPi_one`, `evalPi_normOp`, `normOp`]
- Used by: `colemanSeries_invColeman`, `exists_invColeman_Col_eq`, `range_Col_eq_ker_chiMoment`
- Visibility: public
- Lines: 930–952 (fields/proof ~22 lines)
- Notes: none

### theorem colemanSeries_invColeman
- Type: `(g : PowerSeries ℤ_[p]) (hg : IsUnit g) (hN : normOp g = g) : colemanSeries p (invColeman p g hg hN) = g`
- What: `colemanSeries (invColeman g) = g` — surjectivity of `colemanSeries` onto the `𝒩`-fixed units.
- How: Both are `𝒩`-fixed units interpolating `invColeman g`, so agree by Coleman uniqueness (`evalPi_injective` + `evalPi_colemanSeries`); unfolds `invColeman.elems` at `n≥1`.
- Hypotheses: `g` a unit; `normOp g = g`.
- Uses from project: [`colemanSeries`, `invColeman`, `evalPi_injective`, `evalPi_colemanSeries`, `evalPi`, `evalPi_unit_ne_zero`]
- Used by: `exists_invColeman_Col_eq`
- Visibility: public
- Lines: 958–964 (proof ~4 lines)
- Notes: none

### theorem unitsCmul_add
- Type: `(g : C(ℤ_[p]ˣ, ℤ_[p])) (μ ν : PadicMeasure p ℤ_[p]ˣ) : unitsCmul p g (μ + ν) = unitsCmul p g μ + unitsCmul p g ν`
- What: `unitsCmul g` is additive in the measure argument.
- How: `LinearMap.ext` + `unitsCmul_apply` + `LinearMap.add_apply`.
- Hypotheses: none.
- Uses from project: [`PadicMeasure.unitsCmul`, `PadicMeasure.unitsCmul_apply`]
- Used by: `Col_add`
- Visibility: private
- Lines: 967–972 (proof ~3 lines)
- Notes: none

### theorem Col_add
- Type: `(u v : NormCompatUnits p) : Col p (u * v) = Col p u + Col p v`
- What: `Col` is a homomorphism `(𝒰_∞, ·) → (Λ(ℤ_p^×), +)`.
- How: `colemanSeries_mul` (multiplicativity) + `dlog_mul` (product→sum) + additivity of the tail `𝓐⁻¹ ∘ comp extendByZero ∘ unitsCmul invCM` (`map_add`, `LinearMap.add_comp`, `unitsCmul_add`).
- Hypotheses: none.
- Uses from project: [`Col`, `colemanSeries`, `colemanSeries_mul`, `colemanSeries_isUnit`, `dlog`, `dlog_mul`, `unitsCmul_add`]
- Used by: `range_Col_eq_ker_chiMoment`
- Visibility: public
- Lines: 977–981 (proof ~3 lines)
- Notes: none

### theorem exists_invColeman_Col_eq
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) (hμ : μ (unitsPowCM p 1) = 0) : ∃ (g) (hg : IsUnit g) (hN : normOp g = g), Col p (invColeman p g hg hN) = μ`
- What: The measure-inversion step of the cokernel converse — every `μ` killed by the χ-moment is `Col (invColeman g)` for a `𝒩`-fixed unit `g`.
- How: Sets `μ'' = (unitsPowCM 1)·μ`, `H = 𝓐(ι μ'')`; shows `H ∈ ψ=0` (`isSupportedOn_units_iff_psi_eq_zero`, `res_iota`, `mahlerTransform_psi`) with `H(0)=0`; `exists_one_sub_phi_eq` gives `F₀` with `(1−φ)F₀ = H`, `dlog_surjective_onto_psiId` a `𝒩`-fixed unit `g` with `∂log g = F₀`; reverses transport (`iota_comp_extendByZero`, `mahlerTransform_res_units`, `mahlerTransform_injective`) and undoes `unitsCmul invCM`. Hinges on `exists_one_sub_phi_eq`, `dlog_surjective_onto_psiId`, `mahlerTransform_psi`.
- Hypotheses: `μ(unitsPowCM 1) = 0`.
- Uses from project: [`PadicMeasure.unitsCmul`, `PadicMeasure.unitsPowCM`, `PadicMeasure.invCM`, `PadicMeasure.unitsCmul_apply`, `PadicMeasure.mahlerTransform`, `PadicMeasure.iota`, `PadicMeasure.psi`, `PadicMeasure.isSupportedOn_units_iff_psi_eq_zero`, `PadicMeasure.res_iota`, `psiZeroSeries`, `psiSeries`, `mahlerTransform_psi`, `PadicMeasure.mahlerTransform_zero`, `PadicMeasure.coeff_mahlerTransform`, `mahler_zero_eq_one`, `PadicMeasure.pushforward_apply`, `PadicMeasure.unitsValCM`, `exists_one_sub_phi_eq`, `dlog_surjective_onto_psiId`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.extendByZero`, `iota_comp_extendByZero`, `PadicMeasure.iota_injective`, `PadicMeasure.mahlerTransform_injective`, `mahlerTransform_res_units`, `PadicMeasure.mahlerLinearEquiv_symm_apply`, `PadicMeasure.mahlerTransform_ofPowerSeries`, `phiSeries`, `phiHom`, `phiHom_apply`, `Col`, `colemanSeries_invColeman`, `invColeman`, `invCM_mul_unitsPowCM_one`]
- Used by: `range_Col_eq_ker_chiMoment`
- Visibility: public
- Lines: 993–1032 (proof ~39 lines)
- Notes: long(30–50)

### def teichNCU
- Type: `(a : ℤ_[p]ˣ) : NormCompatUnits p`
- What: The constant `ℤ_[p]`-Teichmüller system — every level is `toCp(ω(a))`, the image in `ℂ_[p]` of the `ℤ_[p]`-Teichmüller representative `ω(a)` (`teichmullerFun`).
- How: `elems _ = map toCp (isUnit_teichmullerFun a).unit`; `mem`/`inv_mem` from `ω(a) ∈ ℚ_p ⊂ K_n` (`algebraMap_mem`) + `‖toCp(·)‖ ≤ 1`; `compat` from `levelNorm_const_eq_pow` + `ω(a)^{p−1}=1` (`teichmullerFun_pow_card_sub_one`) giving `ω(a)^p = ω(a)`.
- Hypotheses: `a : ℤ_[p]ˣ`.
- Uses from project: [`NormCompatUnits`, `toCp`, `norm_toCp`, `O`, `K`, `levelNorm`, `levelNorm_const_eq_pow`]; mathlib: `PadicInt.isUnit_teichmullerFun`, `PadicInt.teichmullerFun`, `PadicInt.teichmullerFun_pow_card_sub_one`
- Used by: `teichNCU_torsion`, `teichNCU_elems`, `range_Col_eq_ker_chiMoment`
- Visibility: private
- Lines: 1050–1083 (fields/proof ~33 lines)
- Notes: long(30–50)

### theorem teichNCU_torsion
- Type: `(a : ℤ_[p]ˣ) (n : ℕ) : (teichNCU p a).elems n ^ (p-1) = 1`
- What: `teichNCU a` is `(p−1)`-torsion: `(ω(a))^{p−1} = 1`.
- How: `Units.ext`, push to `ℂ_[p]`, `IsUnit.unit_spec` + `map_pow` + `teichmullerFun_pow_card_sub_one`.
- Hypotheses: `a : ℤ_[p]ˣ`.
- Uses from project: [`teichNCU`]; mathlib: `PadicInt.isUnit_teichmullerFun`, `PadicInt.teichmullerFun_pow_card_sub_one`
- Used by: `range_Col_eq_ker_chiMoment`
- Visibility: private
- Lines: 1086–1091 (proof ~5 lines)
- Notes: none

### theorem teichNCU_elems
- Type: `(a : ℤ_[p]ˣ) (n : ℕ) : ((teichNCU p a).elems n : ℂ_[p]) = toCp p (teichmullerFun p (a:ℤ_[p]))`
- What: The `ℂ_[p]`-value of `teichNCU a` at any level is `toCp(ω(a))`.
- How: `change` to the definitional value, `IsUnit.unit_spec`.
- Hypotheses: `a : ℤ_[p]ˣ`.
- Uses from project: [`teichNCU`, `toCp`]; mathlib: `PadicInt.isUnit_teichmullerFun`, `PadicInt.teichmullerFun`
- Used by: `range_Col_eq_ker_chiMoment`
- Visibility: private
- Lines: 1094–1097 (proof ~2 lines)
- Notes: none

### theorem norm_evalPi_sub_constantCoeff_lt_one
- Type: `(g : PowerSeries ℤ_[p]) {n : ℕ} (hn : 1 ≤ n) : ‖evalPi p g n - toCp p (constantCoeff g)‖ < 1`
- What: `g(π_n) ≡ g₀ mod 𝔭_n` for `n ≥ 1` (`‖g(π_n) − toCp(constantCoeff g)‖ < 1`).
- How: Writes `g − C g₀ = X·U`, evaluates at `π_n` to `π_n·U(π_n)` (`evalPi_X`, `evalPi_mul`, `evalPi_sub`, `evalPi_C`), bounds by `‖π_n‖ < 1` using `evalPi_mem_O` and `norm_pi_lt_one`.
- Hypotheses: `n ≥ 1`.
- Uses from project: [`evalPi`, `toCp`, `evalPi_C`, `evalPi_sub`, `evalPi_mul`, `evalPi_X`, `evalPi_mem_O`, `norm_pi_lt_one`, `pi`, `O`]
- Used by: `range_Col_eq_ker_chiMoment`
- Visibility: private
- Lines: 1101–1113 (proof ~12 lines)
- Notes: none

### theorem range_Col_eq_ker_chiMoment
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) : (∃ u ∈ unitsTower1 p, Col p u = μ) ↔ μ (unitsPowCM p 1) = 0`
- What: RJW thm:fund exact seq, right-exactness / cokernel — the image of `Col` on `𝒰_{∞,1}` is the kernel of the χ-moment `μ ↦ μ(x)`.
- How: Forward is `Col_apply_unitsPowCM_one_eq_zero`. Converse: `exists_invColeman_Col_eq` gives `u₀=invColeman g` with `Col u₀=μ`; divides off the constant Teichmüller `v=teichNCU a` (`a=constantCoeff g`): `Col v⁻¹=0` (`Col_eq_zero_of_torsion`+`teichNCU_torsion`), so by `Col_add` `Col(u₀·v⁻¹)=μ`, and `w=u₀·v⁻¹` is principal because `g(π_n)≡a mod 𝔭_n` (`norm_evalPi_sub_constantCoeff_lt_one`) and `a·ω(a)⁻¹≡1 mod p` (`teichmullerFun_sub_self_mem`). Hinges on `exists_invColeman_Col_eq`, `Col_add`, `Col_eq_zero_of_torsion`, `norm_evalPi_sub_constantCoeff_lt_one`.
- Hypotheses: none (the iff itself; converse needs `μ(unitsPowCM 1)=0`). No `p`-odd hypothesis.
- Uses from project: [`Col`, `unitsTower1`, `PadicMeasure.unitsPowCM`, `Col_apply_unitsPowCM_one_eq_zero`, `exists_invColeman_Col_eq`, `invColeman`, `evalPi`, `evalPi_unit_ne_zero`, `teichNCU`, `teichNCU_elems`, `teichNCU_torsion`, `toCp`, `norm_toCp`, `O`, `mem_localUnitsOne_iff`, `norm_evalPi_sub_constantCoeff_lt_one`, `Col_eq_zero_of_torsion`, `Col_add`]; mathlib: `PadicInt.isUnit_teichmullerFun`, `PadicInt.teichmullerFun`, `PadicInt.teichmullerFun_sub_self_mem`, `PadicInt.norm_le_pow_iff_mem_span_pow`
- Used by: unused in file
- Visibility: public
- Lines: 1139–1218 (proof ~78 lines)
- Notes: OVER-50 (needs /decompose-proof)

---

## File Summary

**Total declarations: 41** — 3 defs (`ZpOne`, `invColeman`, `teichNCU`) / 36 lemmas+theorems / 0 instances. (Plus 2 structure-valued defs counted among the 3 defs.)

**Key API (used by ≥3 in-file):**
- `evalPi_unit_ne_zero` — used by `invColeman`, `colemanSeries_invColeman`, `exists_invColeman_Col_eq` (and many via `evalPi`)
- `mahlerTransform_res_units` — used by `Col_eq_zero_iff`, `Col_apply_unitsPowCM_one_eq_zero`, `exists_invColeman_Col_eq`
- `invColeman` — used by `colemanSeries_invColeman`, `exists_invColeman_Col_eq`, `range_Col_eq_ker_chiMoment`
- `invCM_mul_unitsPowCM_one`, `mahler_zero_eq_one` — each used by 2 (borderline)
- `norm_zetaSys_sub_one_lt_one` — used by `zpPow_zetaSys'`, `ZpOne`, `mem_ker_Col_iff_mem_ZpOne`

**Unused in file (terminal results / API for downstream §12 files):** `mahlerTransform_psi`, `evalPi_binomialSeries`, `normOp_binomialSeries`, `colemanSeries_eq_binomialSeries_of_mem_ZpOne`, `ZpOne`, `mem_ker_Col_iff_mem_ZpOne`, `colemanSeries_invColeman`, `Col_add`, `range_Col_eq_ker_chiMoment`. The two headline theorems `mem_ker_Col_iff_mem_ZpOne` and `range_Col_eq_ker_chiMoment` are the file's exports (used in `iwasawa_theorem` per header).

**Declarations with `sorry`: none** (file is sorry-free, per header).

**`set_option`:** `levelNorm_zetaSys` (lines 227, 229) — `synthInstance.maxHeartbeats 1000000` + `maxHeartbeats 1000000`. No `sorry`/`TODO`/`admit` anywhere.

**Proofs >50 lines (OVER-50), count = 2:**
- `mem_ker_Col_iff_mem_ZpOne` (~72 lines, 791–864)
- `range_Col_eq_ker_chiMoment` (~78 lines, 1139–1218)

**Proofs 30–50 lines, count = 5:**
- `levelNorm_zetaSys` (~46, 243–290)
- `phiHom_fixed_eq_C` (~34, 474–508)
- `eq_C_mul_binomialSeries_of_dlog_eq_C` (~38, 635–673)
- `oneUnit_pow_p_sub_one_eq_one` (~38, 734–772)
- `exists_invColeman_Col_eq` (~39, 993–1032)
- `teichNCU` (def, ~33, 1050–1083)

(6 entries span 30–50 if the structure-valued `teichNCU` def is included.)
