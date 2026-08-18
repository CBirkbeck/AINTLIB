# Inventory: PadicLFunctions/ResidueZeta.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/ResidueZeta.lean`
(1830 lines). RJW §7: the residue of `ζ_p` at `s = 1` — Theorem 7.1: branch `ζ_{p,i}` continuous for `i ≠ p−1`; `ζ_{p,p−1}` has a simple pole at `s=1` with residue `1 − p⁻¹`.

`namespace PadicLFunctions`; `variable (p : ℕ) [hp : Fact p.Prime]`. Sections: `expTail`, `character`, `mass`, `descent`.

---

### lemma norm_factorial_inv_smul_pow_le_quad
- Type: `{w : L} (hw : InExpBall p w) {n : ℕ} (hn : 2 ≤ n) : ‖(n.factorial : ℚ_[p])⁻¹ • w ^ n‖ ≤ (p : ℝ) * ‖w‖ ^ 2`
- What: Per-term quadratic bound — for `n ≥ 2`, the `n`-th exponential series term is `≤ p·‖w‖²` on the convergence ball.
- How: Power-level comparison at the `(p−1)`-th power: `‖term‖^{p−1} ≤ ‖w‖^{p−1}·(p‖w‖^{p−1})^{n−1}`, bounding the inner factor `≤ 1` via `pow_le_one₀` since `p‖w‖^{p−1} < 1`, then `le_of_pow_le_pow_left₀`. Hinges on `norm_factorial_inv_smul_pow_le`.
- Hypotheses: `L` normed `ℚ_[p]`-algebra; `w` in the exponential ball; `n ≥ 2`.
- Uses from project: [`InExpBall`, `norm_factorial_inv_smul_pow_le`]
- Used by: `norm_padicExp_sub_one_sub_self_le`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 44–76 (proof ~27)
- Notes: none

### theorem norm_padicExp_sub_one_sub_self_le
- Type: `{w : L} (hw : InExpBall p w) : ‖padicExp p w - 1 - w‖ ≤ (p : ℝ) * ‖w‖ ^ 2`
- What: R7.1a — the quadratic tail of the exponential: `‖exp w − 1 − w‖ ≤ p·‖w‖²` on the convergence ball.
- How: Peels the `n=0`,`n=1` terms via `summable_padicExp_terms` and two `tsum_eq_zero_add`, leaving `∑' (n+2)`-terms; bounds via `IsUltrametricDist.norm_tsum_le_of_forall_le` with `norm_factorial_inv_smul_pow_le_quad`.
- Hypotheses: `w` in the exponential ball.
- Uses from project: [`InExpBall`, `padicExp`, `summable_padicExp_terms`, `norm_factorial_inv_smul_pow_le_quad`]
- Used by: `tendsto_branch_denom_div`
- Visibility: public
- Lines: 78–94 (proof ~12)
- Notes: none

### theorem norm_onePAdicPow_sub_one
- Type: `(hp2 : p ≠ 2) {y : ℤ_[p]} (hy : y - 1 ∈ Ideal.span {(p : ℤ_[p])}) (t : ℤ_[p]) : ‖(onePAdicPow p y hy t : ℤ_[p]) - 1‖ = ‖t‖ * ‖y - 1‖`
- What: R7.1b — the one-unit power is a norm isometry in the exponent: `‖y^t − 1‖ = ‖t‖·‖y−1‖` for `y ∈ 1+pℤ_p`.
- How: The T523 exp/log bridge `y^t = exp(t·log y)` (`padicExp_smul_padicLog_eq_onePAdicPow`), then `norm_padicExp_sub_one` gives `‖exp w − 1‖ = ‖w‖`, and `norm_padicLog`/`pZpLog_coe` give `‖log y‖ = ‖y−1‖`.
- Hypotheses: `p ≠ 2`; `y ≡ 1 mod p`.
- Uses from project: [`pZpLog`, `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`, `pZpExp_coe`, `norm_padicExp_sub_one`, `inExpBall_of_mem_span`, `pZpLog_coe`, `norm_padicLog`]
- Used by: unused in file
- Visibility: public
- Lines: 100–122 (proof ~17)
- Notes: none

### theorem teichmuller_isPrimitiveRoot
- Type: `{u : ℤ_[p]ˣ} (hgen : Subgroup.zpowers (unitsToZModPow p 1 u) = ⊤) : IsPrimitiveRoot (PadicInt.teichmuller p u) (p - 1)`
- What: R7.2a — the Teichmüller value of a unit whose level-1 reduction generates `(ZMod p)ˣ` is a primitive `(p−1)`-th root of unity.
- How: `orderOf ω(u) ∣ p−1` from `ω(u)^{p−1}=1` (`teichmullerFun_pow_card_sub_one`); conversely the generating hypothesis gives `orderOf g = p−1` (`orderOf_eq_card_of_forall_mem_zpowers`, `ZMod.card_units_eq_totient`, `Nat.totient_prime`), and `ω(u)` reduces to the same residue (`ker_toZModPow`, `teichmullerFun_sub_self_mem`) so `p−1 ∣ orderOf`; `Nat.dvd_antisymm`.
- Hypotheses: level-1 reduction `unitsToZModPow p 1 u` generates `(ZMod p)ˣ`.
- Uses from project: [`PadicMeasure.unitsToZModPow`]
- Used by: `norm_teichmuller_pow_sub_one_eq_one`
- Visibility: public
- Lines: 124–158 (proof ~25)
- Notes: none

### lemma norm_teichmuller_pow_sub_one_eq_one
- Type: `{u : ℤ_[p]ˣ} (hgen : ∀ n, Subgroup.zpowers (unitsToZModPow p n u) = ⊤) {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) : ‖(teichmuller p u : ℤ_[p]) ^ i - 1‖ = 1`
- What: For `0 < i < p−1`, the reduction `ω(u)^i ≢ 1 mod p`, hence `‖ω(u)^i − 1‖ = 1`.
- How: If `(toZMod u)^i = 1` then lifting through the section forces `(p−1) ∣ i` (via `teichmuller_isPrimitiveRoot`), impossible for `0 < i < p−1`; nonzero reduction ⟺ not divisible by `p` ⟺ norm one (`norm_lt_one_iff_dvd`, `ker_toZMod`).
- Hypotheses: `u` a topological generator at every level; `0 < i < p−1`.
- Uses from project: [`PadicMeasure.unitsToZModPow`, `teichmuller_isPrimitiveRoot`]
- Used by: `branch_denom_ne_zero`
- Visibility: private
- Lines: 160–186 (proof ~25)
- Notes: none

### theorem branch_denom_ne_zero
- Type: `{u : ℤ_[p]ˣ} (hgen : ∀ n, …= ⊤) {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) (s : ℤ_[p]) : (((branchChar p i s u : ℤ_[p])) : ℚ_[p]) - 1 ≠ 0`
- What: R7.2b (RJW Lemma 7.2(i), strengthened to all `s`) — for `0 < i < p−1` the branch denominator `⟨u⟩^{1−s}·ω^i − 1` never vanishes.
- How: Ultrametric isoceles: `‖ω^i − 1‖ = 1` (prev lemma) while `‖A − 1‖ < 1` (`onePAdicPow_sub_one_mem`), and `‖ω^i‖ = 1`, so `‖ω^i·A − ω^i‖ < ‖ω^i − 1‖`; `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` gives `‖V − 1‖ = 1 ≠ 0`; descend through `PadicInt.coe_eq_zero`.
- Hypotheses: `u` a topological generator at every level; `0 < i < p−1`.
- Uses from project: [`branchChar`, `branchChar_apply`, `norm_teichmuller_pow_sub_one_eq_one`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`, `PadicInt.onePAdicPow`, `PadicInt.onePAdicPow_sub_one_mem`]
- Used by: `continuousAt_zetaPBranch`
- Visibility: public
- Lines: 188–229 (proof ~34)
- Notes: long(30-50)

### theorem tendsto_branch_denom_div
- Type: `(hp2 : p ≠ 2) {u : ℤ_[p]ˣ} : Tendsto (fun s => ((s:ℚ_[p])-1)⁻¹ * (((branchChar p (p-1) (1-s) u : ℤ_[p]) : ℚ_[p]) - 1)) (𝓝[≠] 1) (𝓝 (-(pZpLog p ⟨u⟩ : ℚ_[p])))`
- What: R7.2c (RJW Lemma 7.2(ii)) — the `i = p−1` denominator has a simple zero at `s = 1` with derivative `−log_p⟨u⟩`.
- How: `branchChar p (p−1) (1−s) u = exp((1−s)·L)` (`ω^{p−1}=1`, then `padicExp_smul_padicLog_eq_onePAdicPow`); the shifted difference equals `(s−1)⁻¹·(exp w − 1 − w)` with `w = -(s−1)·L`; bounded by `p·‖L‖²·‖s−1‖` via `norm_padicExp_sub_one_sub_self_le`; squeeze to 0 (`squeeze_zero_norm'`) and add the constant.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`pZpLog`, `pZpLog_mem`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`, `branchChar`, `branchChar_apply`, `PadicInt.teichmuller`, `padicExp`, `padicExp_smul_padicLog_eq_onePAdicPow`, `pZpExp_coe`, `InExpBall`, `inExpBall_of_mem_span`, `norm_padicExp_sub_one_sub_self_le`]
- Used by: `tendsto_sub_one_mul_zetaPBranch`
- Visibility: public
- Lines: 231–312 (proof ~78)
- Notes: OVER-50

### lemma onePAdicPow_sub_one_mem_span_pow
- Type: `{y : ℤ_[p]} (hy : y - 1 ∈ Ideal.span {(p:ℤ_[p])}) (k : ℕ) {t : ℤ_[p]} (ht : t ∈ Ideal.span {(p:ℤ_[p])^k}) : onePAdicPow p y hy t - 1 ∈ Ideal.span {(p:ℤ_[p])^k}`
- What: Exponent-congruence (valid at `p=2`): if `t ∈ p^k·ℤ_p` then `y^t ≡ 1 mod p^k`.
- How: Write `t = p^k·c`, so `y^t = (y^c)^{p^k}` (`AddChar.map_nsmul_eq_pow`); `p ∣ y^c − 1` (`onePAdicPow_sub_one_mem`); `dvd_sub_pow_of_dvd_sub` lifts to `p^{k+1} ∣ (y^c)^{p^k} − 1`, then weaken to `p^k`.
- Hypotheses: `y ≡ 1 mod p`; `t ∈ p^k·ℤ_p`.
- Uses from project: [`PadicInt.onePAdicPow`, `PadicInt.onePAdicPow_sub_one_mem`]
- Used by: `norm_onePAdicPow_sub_one_le`
- Visibility: private
- Lines: 314–340 (proof ~18)
- Notes: none

### lemma norm_onePAdicPow_sub_one_le
- Type: `{y : ℤ_[p]} (hy : y - 1 ∈ Ideal.span {(p:ℤ_[p])}) (t : ℤ_[p]) : ‖(onePAdicPow p y hy t : ℤ_[p]) - 1‖ ≤ ‖t‖`
- What: The `p=2`-valid weak isometry `‖y^t − 1‖ ≤ ‖t‖` for `y ∈ 1 + pℤ_p` and every `t` (one-sided, no `p ≠ 2` needed).
- How: Trivial at `t=0`; otherwise `t ∈ span{p^{val t}}` (`norm_le_pow_iff_mem_span_pow`, `norm_eq_zpow_neg_valuation`), then `onePAdicPow_sub_one_mem_span_pow` gives the membership translating back to the norm bound.
- Hypotheses: `y ≡ 1 mod p`.
- Uses from project: [`PadicInt.onePAdicPow`, `onePAdicPow_sub_one_mem_span_pow`]
- Used by: `continuous_zetaNum_branch_pairing`
- Visibility: private
- Lines: 342–357 (proof ~11)
- Notes: none

### theorem continuous_zetaNum_branch_pairing
- Type: `(m i : ℕ) : Continuous (fun s : ℤ_[p] => ((zetaNum p m (branchChar p i (1 - s)) : ℤ_[p]) : ℚ_[p]))`
- What: R7.3a — the numerator pairing `s ↦ ⟨zetaNum, branchChar(1−s)⟩` is continuous in `s` (everywhere; `p=2` allowed).
- How: Pointwise sup-norm bound `‖branchChar(1−s) x − branchChar(1−s') x‖ ≤ ‖s−s'‖` via `κ(1−s)=κ(1−s')·κ(s'−s)` (`AddChar.map_add_eq_mul`) and `norm_onePAdicPow_sub_one_le`; assembles to `LipschitzWith 1` through `PadicMeasure.norm_apply_le` and `ContinuousMap.norm_le`.
- Hypotheses: none beyond globals.
- Uses from project: [`PadicMeasure.zetaNum`, `branchChar`, `branchChar_apply`, `PadicInt.teichmuller`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`, `PadicInt.onePAdicPow`, `norm_onePAdicPow_sub_one_le`, `PadicMeasure.norm_apply_le`]
- Used by: `continuousAt_zetaPBranch`, `tendsto_sub_one_mul_zetaPBranch`
- Visibility: public
- Lines: 359–399 (proof ~37)
- Notes: long(30-50)

### theorem continuousAt_zetaPBranch
- Type: `(hp2 : p ≠ 2) {i : ℕ} (hi0 : 0 < i) (hi : i < p - 1) : ContinuousAt (zetaPBranch p hp2 i) 1`
- What: RJW Theorem 7.1(i) — for `0 < i < p−1` the branch `ζ_{p,i}` is continuous (analytic) at `s = 1`.
- How: Extracts topological-generator data (`exists_nat_topological_generator`); denominator `s ↦ branchChar(1−s) − 1` continuous (`continuous_onePAdicPow`) and nonzero at `1` (`branch_denom_ne_zero`); assembles `(denom)⁻¹·numerator` via `.inv₀` and `continuous_zetaNum_branch_pairing`.
- Hypotheses: `p ≠ 2`; `0 < i < p−1`.
- Uses from project: [`zetaPBranch`, `PadicMeasure.exists_nat_topological_generator`, `branchChar`, `branchChar_apply`, `PadicInt.teichmuller`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`, `PadicInt.onePAdicPow`, `PadicInt.continuous_onePAdicPow`, `branch_denom_ne_zero`, `continuous_zetaNum_branch_pairing`]
- Used by: unused in file
- Visibility: public
- Lines: 401–429 (proof ~25)
- Notes: none

### def uA
- Type: `(a : ℕ) : PowerSeries K := PowerSeries.mk fun n => ((a : K))⁻¹ * (a.choose (n + 1))`
- What: R7.4a — the unit factor `u_a` of `(1+T)^a − 1 = a·T·u_a` (constant term `1`).
- How: definition.
- Hypotheses: `K` complete ultrametric `ℚ_[p]`-algebra of char 0.
- Uses from project: []
- Used by: `constantCoeff_uA`, `hasSubst_uA_sub_one`, `FtildeA`, `natCast_smul_uA_eq_map_geomSum`, `uA_mul_subst_derivative_formalLog`, `one_add_mul_derivative_FtildeA`, `norm_coeff_uA_le_one`, `norm_coeff_uA_sub_one_le_one`, `coeff_uA_sub_one_pow_eq_zero`, `norm_coeff_uA_sub_one_pow_le_one`, `norm_coeff_subst_formalLog_le`, `norm_coeff_FtildeA_le`, `natCast_mul_seriesEval_uA`, `seriesEval_uA_sub_one`, `norm_seriesEval_uA_sub_one_lt`, `seriesEval_FtildeA_at_root`, `sum_seriesEval_FtildeA`
- Visibility: public (noncomputable)
- Lines: 438–441
- Notes: none

### lemma coeff_one_add_X_pow
- Type: `{R : Type*} [CommRing R] (a n : ℕ) : PowerSeries.coeff n ((1 + X)^a : PowerSeries R) = (a.choose n : R)`
- What: The `n`-th coefficient of `(1+X)^a` over any commutative ring is `C(a,n)` (formal binomial theorem).
- How: Transport from the polynomial statement `Polynomial.coeff_one_add_X_pow` via `Polynomial.coeff_coe`.
- Hypotheses: `R` commutative ring.
- Uses from project: []
- Used by: `coeff_geomSum`, `one_add_mul_derivative_FtildeA`, `natCast_mul_seriesEval_uA`
- Visibility: private
- Lines: 444–450 (proof ~5)
- Notes: none

### lemma constantCoeff_uA
- Type: `{a : ℕ} (ha0 : a ≠ 0) : PowerSeries.constantCoeff (uA K a) = 1`
- What: The constant coefficient of `u_a` is `1` (`C(a,1)·a⁻¹ = 1`).
- How: `coeff 0 = constantCoeff`, `coeff_mk`, `Nat.choose_one_right`, `inv_mul_cancel₀`.
- Hypotheses: `a ≠ 0`.
- Uses from project: [`uA`]
- Used by: `hasSubst_uA_sub_one`, `constantCoeff_FtildeA`, `norm_coeff_uA_sub_one_le_one`, `coeff_uA_sub_one_pow_eq_zero`, `seriesEval_uA_sub_one` (via callers), `norm_seriesEval_uA_sub_one_lt`, `seriesEval_FtildeA_at_root`, `sum_seriesEval_FtildeA`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 452–458 (proof ~4)
- Notes: none

### lemma hasSubst_uA_sub_one
- Type: `{a : ℕ} (ha0 : a ≠ 0) : PowerSeries.HasSubst (uA K a - 1 : PowerSeries K)`
- What: `u_a − 1` has zero constant term, hence is a legal substitution argument.
- How: `HasSubst.of_constantCoeff_zero'` with `constantCoeff (uA − 1) = 0`.
- Hypotheses: `a ≠ 0`.
- Uses from project: [`uA`, `constantCoeff_uA`]
- Used by: `uA_mul_subst_derivative_formalLog`, `one_add_mul_derivative_FtildeA`, `norm_coeff_subst_formalLog_le`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 460–465 (proof ~2)
- Notes: none

### def FtildeA
- Type: `(a : ℕ) : PowerSeries K := PowerSeries.C (-(extLog p (a:K))) - (formalLog).subst (uA K a - 1) + ((a-1 : ℕ)) • formalLog`
- What: R7.4b — RJW's antiderivative `F̃_a = log(T/(1+T)·(1+T)^a/((1+T)^a−1))`, realised as `−log_p(a) − log(u_a) + (a−1)·log(1+T)`.
- How: definition.
- Hypotheses: `K` complete ultrametric `ℚ_[p]`-algebra of char 0.
- Uses from project: [`extLog`, `formalLog`, `uA`]
- Used by: `constantCoeff_FtildeA`, `one_add_mul_derivative_FtildeA`, `norm_coeff_FtildeA_le`, `summable_seriesEval_FtildeA`, `p_mul_constantCoeff_mahlerK_rhoA`, `seriesEval_FtildeA_at_root`, `sum_seriesEval_FtildeA`, `constantCoeff_mahlerK_rhoA`
- Visibility: public (noncomputable)
- Lines: 467–475
- Notes: none

### theorem constantCoeff_FtildeA
- Type: `{a : ℕ} (ha0 : a ≠ 0) : PowerSeries.constantCoeff (FtildeA p K a) = -(extLog p (a:K))`
- What: R7.4c — the constant coefficient of `F̃_a` is `−log_p(a)`.
- How: The substitution term has zero constant coefficient (`constantCoeff_subst_eq_zero` + `constantCoeff_formalLog`), and the `nsmul`-term too; remaining `constantCoeff_C`.
- Hypotheses: `a ≠ 0` (T704 statement note: `uA 0 = 0` makes the composition junk).
- Uses from project: [`FtildeA`, `extLog`, `uA`, `constantCoeff_uA`, `formalLog`, `constantCoeff_formalLog`]
- Used by: `constantCoeff_mahlerK_rhoA`
- Visibility: public (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 477–491 (proof ~9)
- Notes: none

### lemma coeff_geomSum
- Type: `(a n : ℕ) : PowerSeries.coeff n (PadicMeasure.geomSum p a) = (a.choose (n+1) : ℤ_[p])`
- What: The `n`-th coefficient of `geomSum a` is `C(a,n+1)`.
- How: `coeff_succ_mul_X` against `geomSum_mul_X`, then `coeff_one_add_X_pow` and `coeff_one`.
- Hypotheses: none beyond globals.
- Uses from project: [`PadicMeasure.geomSum`, `PadicMeasure.geomSum_mul_X`, `coeff_one_add_X_pow`]
- Used by: `natCast_smul_uA_eq_map_geomSum`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 493–500 (proof ~4)
- Notes: none

### lemma natCast_smul_uA_eq_map_geomSum
- Type: `{a : ℕ} (ha0 : a ≠ 0) : (a:K) • uA K a = PowerSeries.map ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) (PadicMeasure.geomSum p a)`
- What: Step A (RJW TeX 2296–2300) — `a·u_a` is the base-changed geometric sum.
- How: Coefficientwise: `coeff_map`, `coeff_geomSum`, `coeff_mk`, and `a·a⁻¹ = 1`.
- Hypotheses: `a ≠ 0`.
- Uses from project: [`uA`, `PadicMeasure.geomSum`, `coeff_geomSum`]
- Used by: `one_add_mul_derivative_FtildeA`, `natCast_mul_seriesEval_uA`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 502–511 (proof ~5)
- Notes: none

### lemma uA_mul_subst_derivative_formalLog
- Type: `{a : ℕ} (ha0 : a ≠ 0) : uA K a * (derivativeFun formalLog).subst (uA K a - 1) = 1`
- What: Step B (RJW TeX 2271–2279) — substituting `u_a − 1` into `(1+X)·∂(log) = 1` gives `u_a·(∂log)(u_a − 1) = 1`.
- How: Apply `.subst (uA−1)` to `one_add_mul_derivative_formalLog`; rewrite `1+(uA−1)=uA` through `coe_substAlgHom`, `substAlgHom_X`.
- Hypotheses: `a ≠ 0`.
- Uses from project: [`uA`, `formalLog`, `hasSubst_uA_sub_one`, `one_add_mul_derivative_formalLog`]
- Used by: `one_add_mul_derivative_FtildeA`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`; include `hp`)
- Lines: 513–524 (proof ~6)
- Notes: none

### theorem one_add_mul_derivative_FtildeA
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) : (1+X)*derivativeFun (FtildeA p K a) = PowerSeries.map (…) (PadicMeasure.Fa p a)`
- What: R7.4d (RJW Lemma 7.3) — `∂F̃_a = F_a` formally (with `∂ = (1+T)d/dT`).
- How: Differentiates the formal identities: `S·X = (1+X)^a−1` (base-changed `geomSum_mul_X`), Step B `uA·P=1`, `derivative_pow`, `(1+X)·∂((1+X)^a) = a·(1+X)^a`; `RHS·G` collapses via `one_add_X_pow_sub_one_mul_Fa`; cancels `G = (1+X)^a−1` (nonzero by coeff at 1) and closes with `linear_combination`. Hinges on `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`, `PadicMeasure.geomSum_mul_X`.
- Hypotheses: `p ∤ a` (T704: `Fa p a` is junk `0` when `p ∣ a`); `a ≠ 0`.
- Uses from project: [`FtildeA`, `uA`, `PadicMeasure.geomSum`, `PadicMeasure.geomSum_mul_X`, `PadicMeasure.Fa`, `PadicMeasure.one_add_X_pow_sub_one_mul_Fa`, `natCast_smul_uA_eq_map_geomSum`, `coeff_one_add_X_pow`, `uA_mul_subst_derivative_formalLog`, `formalLog`, `one_add_mul_derivative_formalLog`, `hasSubst_uA_sub_one`]
- Used by: `p_mul_constantCoeff_mahlerK_rhoA`
- Visibility: public
- Lines: 532–650 (proof ~115)
- Notes: OVER-50

### def rhoA
- Type: `(a : ℕ) : MeasureR K ℤ_[p] := MeasureR.baseChange p K (PadicMeasure.iota p (PadicMeasure.zetaNum p a))`
- What: R7.5a — the §4 numerator measure `x⁻¹·Res_{ℤ_p^×}(μ_a)` (= `zetaNum`), pushed to `ℤ_p` and base-changed to `K`.
- How: definition.
- Hypotheses: `K` complete ultrametric `ℚ_[p]`-algebra of char 0.
- Uses from project: [`MeasureR.baseChange`, `PadicMeasure.iota`, `PadicMeasure.zetaNum`]
- Used by: `psi_rhoA`, `one_add_mul_derivative_mahlerK_rhoA`, `p_mul_constantCoeff_mahlerK_rhoA`, `constantCoeff_mahlerK_rhoA`, `constantCoeff_mahlerK_rhoA_eq_algebraMap`
- Visibility: public (noncomputable)
- Lines: 652–655
- Notes: none

### theorem map_derivativeFun'
- Type: `{R S} [CommRing R] [CommRing S] (f : R →+* S) (F : PowerSeries R) : map f (derivativeFun F) = derivativeFun (map f F)`
- What: `PowerSeries.map` commutes with `derivativeFun` (re-proved locally; ValuesAtOne version private).
- How: Coefficientwise via `coeff_derivativeFun` and `coeff_map`/`map_natCast`.
- Hypotheses: `R, S` commutative rings.
- Uses from project: []
- Used by: `map_one_add_mul_derivativeFun'`
- Visibility: private
- Lines: 657–666 (proof ~4)
- Notes: none

### theorem map_one_add_mul_derivativeFun'
- Type: `{R S} [CommRing R] [CommRing S] (f : R →+* S) (F : PowerSeries R) : map f ((1+X)*derivativeFun F) = (1+X)*derivativeFun (map f F)`
- What: `PowerSeries.map` commutes with `∂ = (1+T)d/dT` (re-proved locally).
- How: `map_mul`, `map_add`, `map_X` plus `map_derivativeFun'`.
- Hypotheses: `R, S` commutative rings.
- Uses from project: [`map_derivativeFun'`]
- Used by: `one_add_mul_derivative_mahlerK_rhoA`
- Visibility: private
- Lines: 668–673 (proof ~2)
- Notes: none

### lemma cmul_mahler_one_iota_zetaNum
- Type: `(a : ℕ) : PadicMeasure.cmul p (mahler 1) (iota p (zetaNum p a)) = PadicMeasure.res p (isClopen_units p) (muA p a)`
- What: The `ℤ_p`-level multiplication-by-`x` identity: the `x⁻¹` in `zetaNum` cancels the `x`-monomial on the units, so `x·ι(zetaNum a) = Res_{ℤ_p^×}(μ_a)`.
- How: `LinearMap.ext`; unfolds `cmul`, `iota`, `pushforward`, `zetaNum`, `unitsCmul`; the function-level cancellation `invCM·(mahler 1·f) = f` on units (`mahler_apply`, `Ring.choose_one_right`, `inv_mul_cancel`); closes via `iota_muAUnits`.
- Hypotheses: none beyond globals.
- Uses from project: [`PadicMeasure.cmul`, `PadicMeasure.cmul_apply`, `PadicMeasure.iota`, `PadicMeasure.pushforward_apply`, `PadicMeasure.zetaNum`, `PadicMeasure.unitsCmul_apply`, `PadicMeasure.invCM`, `PadicMeasure.unitsValCM`, `PadicMeasure.res`, `PadicMeasure.isClopen_units`, `PadicMeasure.muA`, `PadicMeasure.iota_muAUnits`]
- Used by: `one_add_mul_derivative_mahlerK_rhoA`
- Visibility: private
- Lines: 675–695 (proof ~14)
- Notes: none

### theorem psi_rhoA
- Type: `(a : ℕ) : MeasureR.psi p K (rhoA p K a) = 0`
- What: R7.5b — `ρ_a` is supported on the units (its `ψ`-part vanishes).
- How: `isSupportedOn_units_iff_psi_eq_zero`, `IsSupportedOn`, `baseChange_res`, `res_iota`.
- Hypotheses: none beyond globals (omit `CharZero`).
- Uses from project: [`MeasureR.psi`, `rhoA`, `MeasureR.IsSupportedOn`, `MeasureR.isSupportedOn_units_iff_psi_eq_zero`, `MeasureR.baseChange_res`, `PadicMeasure.res_iota`]
- Used by: `p_mul_constantCoeff_mahlerK_rhoA`
- Visibility: public (omit `CharZero`)
- Lines: 697–701 (proof ~2)
- Notes: none

### theorem one_add_mul_derivative_mahlerK_rhoA
- Type: `(a : ℕ) : (1+X)*derivativeFun (mahlerK p K (rhoA p K a)) = mahlerK p K (MeasureR.res p K (isClopen_units p) (baseChange p K (muA p a)))`
- What: R7.5c (Lemma 6.3's pattern, T614) — multiplication by `x` recovers `Res_{units}(μ_a)`: `∂𝓐(ρ_a) = 𝓐(Res_{units}(μ_a))` over `K`.
- How: Base-changes `cmul_mahler_one_iota_zetaNum` to `K` (`baseChange_cmul`, `algCM_mahler`, `baseChange_res`); transports through `mahlerK` via `mahlerTransform_cmul_X` and `map_one_add_mul_derivativeFun'`.
- Hypotheses: none beyond globals (omit `CharZero`).
- Uses from project: [`mahlerK`, `rhoA`, `MeasureR.res`, `PadicMeasure.isClopen_units`, `MeasureR.baseChange`, `PadicMeasure.muA`, `MeasureR.cmul`, `MeasureR.mahlerCM`, `cmul_mahler_one_iota_zetaNum`, `MeasureR.baseChange_cmul`, `MeasureR.algCM_mahler`, `MeasureR.baseChange_res`, `MeasureR.mahlerTransform_cmul_X`, `MeasureR.del`, `MeasureR.mahlerTransform`, `map_one_add_mul_derivativeFun'`]
- Used by: `p_mul_constantCoeff_mahlerK_rhoA`
- Visibility: public (omit `CharZero`)
- Lines: 703–725 (proof ~14)
- Notes: none

### lemma mahlerK_baseChange_muA
- Type: `(a : ℕ) : mahlerK p K (baseChange p K (muA p a)) = PowerSeries.map ((algebraMap ℚ_[p] K).comp PadicInt.Coe.ringHom) (PadicMeasure.Fa p a)`
- What: The `M`-bridge (Step 1 of the c₀-pin) — `mahlerK` of base-changed `μ_a` is the `M`-image of `F_a`.
- How: `mahlerTransform_baseChange`, `mahlerTransform_muA`, then coefficientwise `coeff_map`·3 and `rfl` (the `Algebra ℤ_[p] (integerRing K)` instance is the codRestriction of `M`).
- Hypotheses: none beyond globals (omit `CharZero`).
- Uses from project: [`mahlerK`, `MeasureR.baseChange`, `PadicMeasure.muA`, `PadicMeasure.Fa`, `MeasureR.mahlerTransform_baseChange`, `PadicMeasure.mahlerTransform_muA`]
- Used by: `p_mul_constantCoeff_mahlerK_rhoA`
- Visibility: private (omit `CharZero`)
- Lines: 727–739 (proof ~6)
- Notes: none

### lemma norm_coeff_uA_le_one
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (n : ℕ) : ‖PowerSeries.coeff n (uA K a)‖ ≤ 1`
- What: The coefficients of `u_a` are integral (`= a⁻¹·C(a,n+1)`, `‖a⁻¹‖=1` for `p∤a`).
- How: `coeff_mk`, `norm_natCast_eq_one_of_not_dvd` for `‖a⁻¹‖=1`, and `norm_natCast_le_one` for the binomial coefficient.
- Hypotheses: `p ∤ a`.
- Uses from project: [`uA`, `norm_natCast_eq_one_of_not_dvd`]
- Used by: `norm_coeff_uA_sub_one_le_one`, `natCast_mul_seriesEval_uA`, `seriesEval_uA_sub_one`
- Visibility: private (omit `CompleteSpace`, `CharZero`)
- Lines: 741–748 (proof ~3)
- Notes: none

### lemma norm_coeff_uA_sub_one_le_one
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) (n : ℕ) : ‖PowerSeries.coeff n (uA K a - 1)‖ ≤ 1`
- What: The coefficients of `u_a − 1` are integral (constant term `0`, rest are `u_a`-coefficients).
- How: Case split on `n`: `n=0` gives `0`; `n=m+1` reduces to `norm_coeff_uA_le_one`.
- Hypotheses: `p ∤ a`; `a ≠ 0`.
- Uses from project: [`uA`, `constantCoeff_uA`, `norm_coeff_uA_le_one`]
- Used by: `norm_coeff_uA_sub_one_pow_le_one`, `seriesEval_FtildeA_at_root`, `norm_seriesEval_uA_sub_one_lt`
- Visibility: private (omit `CompleteSpace`)
- Lines: 750–764 (proof ~9)
- Notes: none

### lemma coeff_uA_sub_one_pow_eq_zero
- Type: `{a : ℕ} (ha0 : a ≠ 0) {k d : ℕ} (hkd : k < d) : PowerSeries.coeff k ((uA K a - 1)^d) = 0`
- What: `(u_a − 1)^d` vanishes below degree `d` (`X^d ∣ (u_a − 1)^d`).
- How: `X_pow_dvd_iff`, `pow_dvd_pow_of_dvd`, `X_dvd_iff` with `constantCoeff (uA−1) = 0`.
- Hypotheses: `a ≠ 0`.
- Uses from project: [`uA`, `constantCoeff_uA`]
- Used by: `norm_coeff_subst_formalLog_le`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 766–773 (proof ~3)
- Notes: none

### lemma norm_coeff_uA_sub_one_pow_le_one
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) (d k : ℕ) : ‖PowerSeries.coeff k ((uA K a - 1)^d)‖ ≤ 1`
- What: Powers of `u_a − 1` have integral coefficients.
- How: Induction on `d` via `coeff_mul` and `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`, each factor bounded by `norm_coeff_uA_sub_one_le_one`.
- Hypotheses: `p ∤ a`; `a ≠ 0`.
- Uses from project: [`uA`, `norm_coeff_uA_sub_one_le_one`]
- Used by: `norm_coeff_subst_formalLog_le`
- Visibility: private (omit `CompleteSpace`)
- Lines: 775–792 (proof ~13)
- Notes: none

### theorem norm_natCast_inv_le
- Type: `{n : ℕ} (hn : 1 ≤ n) : ‖((n : K))⁻¹‖ ≤ (n : ℝ)`
- What: `‖(n:K)⁻¹‖ ≤ n` for `n ≥ 1` (re-proved locally; ValuesAtOne private). The norm is `p^{−v_p(n)}` whose inverse is `ordProj[p] n ≤ n`.
- How: `norm_algebraMap'`, `Padic.norm_eq_zpow_neg_valuation`, `valuation_natCast`, `factorization_def`, then `Nat.ordProj_le`.
- Hypotheses: `n ≥ 1`.
- Uses from project: []
- Used by: `norm_coeff_formalLog_le`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`, `CharZero`; include `hp`)
- Lines: 794–807 (proof ~9)
- Notes: none

### theorem norm_coeff_formalLog_le
- Type: `(n : ℕ) : ‖PowerSeries.coeff n (formalLog K)‖ ≤ (n : ℝ) + 1`
- What: The coefficients of `formalLog` are linearly bounded `‖coeff n‖ ≤ n+1` (the `1/n`-factor has norm `≤ n`).
- How: Case `n=0` zero (`coeff_zero_formalLog`); `n=m+1` uses `coeff_succ_formalLog` and `norm_natCast_inv_le`.
- Hypotheses: none beyond globals.
- Uses from project: [`formalLog`, `coeff_zero_formalLog`, `coeff_succ_formalLog`, `norm_natCast_inv_le`]
- Used by: `norm_coeff_subst_formalLog_le`, `norm_coeff_FtildeA_le`, `seriesEval_subst_formalLog`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`, `CharZero`; include `hp`)
- Lines: 809–821 (proof ~6)
- Notes: none

### theorem norm_coeff_subst_formalLog_le
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) (n : ℕ) : ‖PowerSeries.coeff n ((formalLog K).subst (uA K a - 1))‖ ≤ (n : ℝ) + 1`
- What: The substitution `(formalLog).subst (u_a − 1)` has linearly-bounded coefficients `‖coeff n‖ ≤ n+1`.
- How: `coeff_subst'`-finsum supported on `d ≤ n` (since `(u_a − 1)^d` vanishes below `d`); `norm_sum_le_of_forall_le_of_nonneg`, each term `(d+1)·1 ≤ n+1` via `norm_coeff_formalLog_le` and `norm_coeff_uA_sub_one_pow_le_one`.
- Hypotheses: `p ∤ a`; `a ≠ 0`.
- Uses from project: [`formalLog`, `uA`, `hasSubst_uA_sub_one`, `coeff_uA_sub_one_pow_eq_zero`, `norm_coeff_formalLog_le`, `norm_coeff_uA_sub_one_pow_le_one`]
- Used by: `norm_coeff_FtildeA_le`, `seriesEval_FtildeA_at_root`
- Visibility: private (omit `CompleteSpace`; include `hp`)
- Lines: 823–852 (proof ~21)
- Notes: none

### theorem norm_coeff_FtildeA_le
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) (n : ℕ) : ‖PowerSeries.coeff n (FtildeA p K a)‖ ≤ max 1 ‖extLog p (a:K)‖ * ((n:ℝ)+1)`
- What: The coefficients of `F̃_a` are linearly bounded `‖coeff n‖ ≤ C·(n+1)` with `C = max 1 ‖log_p a‖`. Drives summability of `seriesEval (F̃_a)`.
- How: Splits `F̃_a` into three summands (`C`, `subst`, `nsmul`), bounds each by `C·(n+1)` (`coeff_C`, `norm_coeff_subst_formalLog_le`, `norm_coeff_formalLog_le`, `norm_natCast_le_one`), and combines via `norm_add_le_max`.
- Hypotheses: `p ∤ a`; `a ≠ 0`.
- Uses from project: [`FtildeA`, `extLog`, `formalLog`, `uA`, `norm_coeff_subst_formalLog_le`, `norm_coeff_formalLog_le`]
- Used by: `summable_seriesEval_FtildeA`
- Visibility: private (omit `CompleteSpace`; include `hp`)
- Lines: 854–890 (proof ~26)
- Notes: none

### theorem summable_seriesEval_FtildeA
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) {z : K} (hz : ‖z‖ < 1) : Summable fun m => PowerSeries.coeff m (FtildeA p K a) * z ^ m`
- What: `seriesEval (F̃_a) z` converges for `‖z‖ < 1` (linear-growth coefficients).
- How: `summable_seriesEval_of_norm_coeff_le_linear` with `norm_coeff_FtildeA_le`.
- Hypotheses: `p ∤ a`; `a ≠ 0`; `‖z‖ < 1`.
- Uses from project: [`FtildeA`, `extLog`, `norm_coeff_FtildeA_le`, `summable_seriesEval_of_norm_coeff_le_linear`]
- Used by: `p_mul_constantCoeff_mahlerK_rhoA`
- Visibility: private (include `hp`)
- Lines: 892–898 (proof ~2)
- Notes: none

### theorem p_mul_constantCoeff_mahlerK_rhoA
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) : (p:K)*constantCoeff (mahlerK p K (rhoA p K a)) = (p:K)*constantCoeff (FtildeA p K a) - ∑ i : Fin p, seriesEval (FtildeA p K a) (ξ^(i:ℕ)-1)`
- What: R7.6a (c₀-pin, T615) — `p·𝓐(ρ_a)(0) = p·F̃_a(0) − Σ_{i<p} F̃_a(ξ^i − 1)`.
- How: Gets a bounded antiderivative `C₁` (`exists_antideriv_bounded`); establishes `(1+X)·∂F̃_a = mahlerK(baseChange μ_a)` (T704+M-bridge) and `(1+X)·∂𝓐ρ = … − φB` (`res_units_eq`, `mahlerK_phi`); the difference `W = F̃_a − 𝓐ρ` satisfies `(1+X)·∂(W − φC₁) = 0`, so `W = φC₁ + C c₀` (`eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`); evaluates at the `z_j = ξ^j−1` (with `seriesEval_phi_at_root_of_summable`, `sum_seriesEval_mahlerK`, `psi_rhoA`) and sums. Hinges on `MeasureR.exists_antideriv_bounded`, `eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`.
- Hypotheses: `p ∤ a`; `a ≠ 0`; `ξ` a primitive `p`-th root of unity in `K`.
- Uses from project: [`mahlerK`, `rhoA`, `FtildeA`, `MeasureR.psi`, `MeasureR.baseChange`, `PadicMeasure.muA`, `MeasureR.exists_antideriv_bounded`, `norm_coeff_mahlerK_le_one`, `one_add_mul_derivative_FtildeA`, `mahlerK_baseChange_muA`, `one_add_mul_derivative_mahlerK_rhoA`, `MeasureR.res_units_eq`, `mahlerK_sub`, `mahlerK_phi`, `phiSeries`, `one_add_mul_derivative_phiSeries`, `phiSeries_C_mul`, `eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`, `constantCoeff_phiSeries`, `seriesEval`, `seriesEval_sub`, `seriesEval_add`, `seriesEval_C`, `summable_seriesEval_FtildeA`, `summable_seriesEval_of_norm_coeff_le_one`, `summable_seriesEval_of_norm_coeff_le_linear`, `norm_coeff_phiSeries_le_linear`, `summable_prod_of_norm_coeff_le_linear`, `seriesEval_phi_at_root_of_summable`, `sum_seriesEval_mahlerK`, `psi_rhoA`, `IsPrimitiveRoot.norm_sub_one_lt`]
- Used by: `constantCoeff_mahlerK_rhoA`
- Visibility: public
- Lines: 900–1026 (proof ~123)
- Notes: OVER-50

### lemma coeff_pow_eq_zero_of_constantCoeff_zero
- Type: `{G : PowerSeries K} (hG0 : constantCoeff G = 0) {k d : ℕ} (hkd : k < d) : PowerSeries.coeff k (G^d) = 0`
- What: A power `G^d` of a series with zero constant coefficient vanishes below degree `d` (generic version of `coeff_uA_sub_one_pow_eq_zero`).
- How: `X_pow_dvd_iff`, `pow_dvd_pow_of_dvd`, `X_dvd_iff`.
- Hypotheses: `constantCoeff G = 0`.
- Uses from project: []
- Used by: `seriesEval_subst_formalLog`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`, `CharZero`)
- Lines: 1028–1036 (proof ~3)
- Notes: none

### lemma norm_coeff_pow_le_one
- Type: `{G : PowerSeries K} (hG : ∀ n, ‖coeff n G‖ ≤ 1) (d k : ℕ) : ‖PowerSeries.coeff k (G^d)‖ ≤ 1`
- What: Powers of a series with integral coefficients have integral coefficients (generic version of `norm_coeff_uA_sub_one_pow_le_one`).
- How: Induction on `d` via `coeff_mul` and `exists_norm_finsetSum_le_of_nonempty`.
- Hypotheses: `‖coeff n G‖ ≤ 1` for all `n`.
- Uses from project: []
- Used by: `seriesEval_pow`, `seriesEval_subst_formalLog`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`, `CharZero`)
- Lines: 1038–1055 (proof ~11)
- Notes: none

### lemma seriesEval_one
- Type: `(z : K) : seriesEval (1 : PowerSeries K) z = 1`
- What: `seriesEval 1 z = 1` (the unit series is `C 1`).
- How: `1 = C 1`, then `seriesEval_C`.
- Hypotheses: none beyond globals.
- Uses from project: [`seriesEval`, `seriesEval_C`]
- Used by: `seriesEval_pow`, `natCast_mul_seriesEval_uA`, `seriesEval_uA_sub_one`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`, `CharZero`)
- Lines: 1057–1060 (proof ~1)
- Notes: none

### lemma seriesEval_pow
- Type: `{G : PowerSeries K} (hG : ∀ n, ‖coeff n G‖ ≤ 1) {z : K} (hz : ‖z‖ < 1) (d : ℕ) : seriesEval (G^d) z = (seriesEval G z)^d`
- What: `seriesEval (G^d) z = (seriesEval G z)^d` for an integral-coefficient series at `‖z‖ < 1`.
- How: Induction on `d` via `seriesEval_mul` (each power summable by `norm_coeff_pow_le_one`).
- Hypotheses: integral coefficients; `‖z‖ < 1`.
- Uses from project: [`seriesEval`, `seriesEval_one`, `seriesEval_mul`, `norm_coeff_pow_le_one`, `summable_seriesEval_of_norm_coeff_le_one`]
- Used by: `seriesEval_subst_formalLog`
- Visibility: private (omit `CharZero`)
- Lines: 1062–1073 (proof ~6)
- Notes: none

### lemma norm_seriesEval_le
- Type: `{G : PowerSeries K} (hG0 : constantCoeff G = 0) (hG : ∀ n, ‖coeff n G‖ ≤ 1) {z : K} (hz : ‖z‖ ≤ 1) : ‖seriesEval G z‖ ≤ ‖z‖`
- What: `‖seriesEval G z‖ ≤ ‖z‖` when `constantCoeff G = 0` and coefficients integral.
- How: `norm_tsum_le_of_forall_le`; `n=0` term vanishes, `n≥1` terms `≤ ‖z‖^n ≤ ‖z‖`.
- Hypotheses: `constantCoeff G = 0`; integral coefficients; `‖z‖ ≤ 1`.
- Uses from project: [`seriesEval`]
- Used by: `seriesEval_subst_formalLog`, `norm_seriesEval_uA_sub_one_lt`
- Visibility: private (omit `CompleteSpace`, `CharZero`)
- Lines: 1075–1093 (proof ~13)
- Notes: none

### theorem seriesEval_subst_formalLog
- Type: `{G : PowerSeries K} (hG0 : constantCoeff G = 0) (hG : ∀ n, ‖coeff n G‖ ≤ 1) {z : K} (hz : ‖z‖ < 1) : seriesEval ((formalLog).subst G) z = padicLog p (1 + seriesEval G z)`
- What: Step 1 bridge (main new infrastructure) — substituting `G` (zero constant coeff, integral) into `formalLog` and evaluating at `‖z‖ < 1` gives `padicLog (1 + seriesEval G z)`.
- How: Defines the total family `T d n = coeff_d(formalLog)·coeff_n(G^d)·z^n`, proves joint summability over `ℕ×ℕ` (`summable_iff_tendsto_cofinite_zero` + a finite-support argument via `tendsto_self_mul_const_pow_of_lt_one`), expands LHS coefficientwise (`coeff_subst'`), swaps the double sum (`Summable.tsum_comm`), and reduces the inner sum to `seriesEval_pow`; closes with `MeasureR.seriesEval_formalLog`. Hinges on `Summable.tsum_comm`, `MeasureR.seriesEval_formalLog`.
- Hypotheses: `constantCoeff G = 0`; integral coefficients; `‖z‖ < 1`.
- Uses from project: [`formalLog`, `seriesEval`, `norm_coeff_formalLog_le`, `norm_coeff_pow_le_one`, `coeff_pow_eq_zero_of_constantCoeff_zero`, `seriesEval_pow`, `norm_seriesEval_le`, `summable_seriesEval_of_norm_coeff_le_one`, `MeasureR.seriesEval_formalLog`]
- Used by: `seriesEval_FtildeA_at_root`
- Visibility: private (omit `CharZero`)
- Lines: 1095–1188 (proof ~88)
- Notes: OVER-50

### lemma seriesEval_X
- Type: `(z : K) : seriesEval (PowerSeries.X : PowerSeries K) z = z`
- What: `seriesEval X z = z` (the monomial `X` peels to its single nonzero term).
- How: `tsum_eq_single 1`, `coeff_one_X`.
- Hypotheses: none (omits all algebra/completeness instances incl. `Fact p.Prime`).
- Uses from project: [`seriesEval`]
- Used by: `natCast_mul_seriesEval_uA`
- Visibility: private
- Lines: 1190–1196 (proof ~2)
- Notes: none

### lemma seriesEval_smul
- Type: `(c : K) (F : PowerSeries K) (z : K) : seriesEval (c • F) z = c * seriesEval F z`
- What: `seriesEval (c • F) z = c · seriesEval F z`.
- How: `smul_eq_C_mul`, `seriesEval_C_mul`.
- Hypotheses: none (omits all algebra/completeness instances incl. `Fact p.Prime`).
- Uses from project: [`seriesEval`, `seriesEval_C_mul`]
- Used by: `natCast_mul_seriesEval_uA`
- Visibility: private
- Lines: 1198–1203 (proof ~1)
- Notes: none

### lemma nsmul_eq_C_natCast_mul
- Type: `(n : ℕ) (F : PowerSeries K) : (n • F) = PowerSeries.C ((n:K)) * F`
- What: `(n:ℕ) • F = C (n:K) * F` for a `K`-coefficient power series.
- How: `smul_eq_C_mul`, `Nat.cast_smul_eq_nsmul`.
- Hypotheses: none (omits all algebra/completeness instances incl. `Fact p.Prime`).
- Uses from project: []
- Used by: `seriesEval_FtildeA_at_root`
- Visibility: private
- Lines: 1205–1210 (proof ~1)
- Notes: none

### lemma natCast_mul_seriesEval_uA
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) {z : K} (hz : ‖z‖ < 1) : (a:K)*z*seriesEval (uA K a) z = (1+z)^a - 1`
- What: Step 2 (RJW TeX 2296–2300, evaluated) — `(a:K)·z·seriesEval(u_a) z = (1+z)^a − 1`.
- How: Evaluates the formal identity `(a:K)•uA·X = (1+X)^a−1` (`natCast_smul_uA_eq_map_geomSum`, `geomSum_mul_X`) at `z` via `seriesEval_mul`/`seriesEval_X`/`seriesEval_smul`, RHS through `seriesEval_one_add_X_pow`.
- Hypotheses: `p ∤ a`; `a ≠ 0`; `‖z‖ < 1`.
- Uses from project: [`uA`, `natCast_smul_uA_eq_map_geomSum`, `PadicMeasure.geomSum_mul_X`, `norm_coeff_uA_le_one`, `summable_seriesEval_of_norm_coeff_le_one`, `seriesEval_mul`, `seriesEval_smul`, `seriesEval_X`, `seriesEval_one_add_X_pow`, `seriesEval_C`, `coeff_one_add_X_pow`, `seriesEval_sub`]
- Used by: `sum_seriesEval_FtildeA`
- Visibility: private (omits all algebra/completeness instances incl. `Fact p.Prime`)
- Lines: 1212–1250 (proof ~31)
- Notes: long(30-50)

### lemma norm_prod_sub_one_lt_one
- Type: `{ι} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, ‖f i - 1‖ < 1) : ‖(∏ i ∈ s, f i) - 1‖ < 1`
- What: The open unit ball `‖· − 1‖ < 1` is closed under finite products.
- How: `Finset.induction`; the inductive step uses `xy − 1 = x·(y−1) + (x−1)` and `norm_add_le_max`, with `‖f a‖ ≤ 1`.
- Hypotheses: every `f i` in the open unit ball about `1`.
- Uses from project: []
- Used by: `padicLog_prod_of_norm_lt_one`
- Visibility: private (omits `Fact p.Prime`, `NormedAlgebra`, `CompleteSpace`, `CharZero`)
- Lines: 1252–1272 (proof ~14)
- Notes: none

### lemma padicLog_prod_of_norm_lt_one
- Type: `{ι} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, ‖f i - 1‖ < 1) : padicLog p (∏ i ∈ s, f i) = ∑ i ∈ s, padicLog p (f i)`
- What: Step 6 — `padicLog` of a finite product equals the sum of `padicLog`s when all factors are in the open unit ball.
- How: `Finset.induction` via `MeasureR.padicLog_mul_of_norm_lt_one` (ball closed under products by `norm_prod_sub_one_lt_one`).
- Hypotheses: every `f i` in the open unit ball about `1`.
- Uses from project: [`MeasureR.padicLog_mul_of_norm_lt_one`, `norm_prod_sub_one_lt_one`]
- Used by: `sum_seriesEval_FtildeA`
- Visibility: private (omit `CharZero`)
- Lines: 1274–1288 (proof ~7)
- Notes: none

### lemma seriesEval_uA_sub_one
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) {z : K} (hz : ‖z‖ < 1) : seriesEval (uA K a - 1) z = seriesEval (uA K a) z - 1`
- What: `seriesEval (u_a − 1) z = seriesEval(u_a) z − 1` for `‖z‖ < 1`.
- How: `seriesEval_sub` (both summable) with `seriesEval_one`.
- Hypotheses: `p ∤ a`; `‖z‖ < 1`.
- Uses from project: [`uA`, `seriesEval_sub`, `seriesEval_one`, `norm_coeff_uA_le_one`, `summable_seriesEval_of_norm_coeff_le_one`]
- Used by: `norm_seriesEval_uA_sub_one_lt`, `seriesEval_FtildeA_at_root`
- Visibility: private (omit `CharZero`)
- Lines: 1290–1300 (proof ~5)
- Notes: none

### lemma norm_seriesEval_uA_sub_one_lt
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) {z : K} (hz : ‖z‖ < 1) : ‖seriesEval (uA K a) z - 1‖ < 1`
- What: `seriesEval(u_a) z` lands in the open unit ball (distance to `1` is `≤ ‖z‖ < 1`).
- How: Rewrites via `seriesEval_uA_sub_one` and bounds by `norm_seriesEval_le` (`< ‖z‖ < 1`).
- Hypotheses: `p ∤ a`; `a ≠ 0`; `‖z‖ < 1`.
- Uses from project: [`uA`, `seriesEval_uA_sub_one`, `norm_seriesEval_le`, `constantCoeff_uA`, `norm_coeff_uA_sub_one_le_one`]
- Used by: `sum_seriesEval_FtildeA`
- Visibility: private
- Lines: 1302–1309 (proof ~3)
- Notes: none

### lemma seriesEval_FtildeA_at_root
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) (i : Fin p) : seriesEval (FtildeA p K a) (ξ^(i:ℕ)-1) = -(extLog p (a:K)) - padicLog p (seriesEval (uA K a) (ξ^(i:ℕ)-1))`
- What: Step 3 (per-point) — evaluating `F̃_a` at `z_i = ξ^i − 1` gives `−log_p(a) − padicLog(seriesEval(u_a) z_i)` (the `(a−1)·log(1+T)` term vanishes since `(ξ^i)^p = 1`).
- How: Establishes `‖z‖ < 1` and `1+z=ξ^i`; three summabilities; evaluates `F̃_a`'s three summands; the subst-term equals `padicLog(seriesEval(u_a) z)` via `seriesEval_subst_formalLog` + `seriesEval_uA_sub_one`; the log-term vanishes by `extLog_eq_zero_of_pow_eq_one`. Hinges on `seriesEval_subst_formalLog`, `MeasureR.seriesEval_formalLog`.
- Hypotheses: `p ∤ a`; `a ≠ 0`; `ξ` a primitive `p`-th root.
- Uses from project: [`FtildeA`, `uA`, `extLog`, `formalLog`, `seriesEval_subst_formalLog`, `seriesEval_uA_sub_one`, `constantCoeff_uA`, `norm_coeff_uA_sub_one_le_one`, `norm_coeff_subst_formalLog_le`, `norm_coeff_formalLog_le`, `nsmul_eq_C_natCast_mul`, `seriesEval_add`, `seriesEval_sub`, `seriesEval_C`, `seriesEval_C_mul`, `MeasureR.seriesEval_formalLog`, `MeasureR.extLog_eq_padicLog_of_norm_lt_one`, `extLog_eq_zero_of_pow_eq_one`, `summable_seriesEval_of_norm_coeff_le_linear`, `IsPrimitiveRoot.norm_sub_one_lt`]
- Used by: `sum_seriesEval_FtildeA`
- Visibility: private
- Lines: 1311–1371 (proof ~58)
- Notes: OVER-50

### lemma prod_erase_pow_twist
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) {ξ : K} (hξ : IsPrimitiveRoot ξ p) : ∏ i ∈ univ.erase 0, (ξ^(a*(i:ℕ))-1) = ∏ i ∈ univ.erase 0, (ξ^(i:ℕ)-1)`
- What: Step 5 reindex — for `p ∤ a`, `i ↦ a·i mod p` permutes `univ.erase 0`, so the twisted product equals the untwisted one.
- How: `Finset.prod_nbij'` through `ZMod p` with inverse `a⁻¹ mod p`; the summand matches via `IsOfFinOrder.pow_eq_pow_iff_modEq` (order of `ξ` is `p`).
- Hypotheses: `p ∤ a`; `ξ` a primitive `p`-th root.
- Uses from project: []
- Used by: `sum_seriesEval_FtildeA`
- Visibility: private (omits `NormedAlgebra`, `IsUltrametricDist`, `CompleteSpace`, `CharZero`)
- Lines: 1373–1424 (proof ~48)
- Notes: long(30-50)

### lemma norm_natCast_pow_sub_one_le
- Type: `{a : ℕ} (ha : ¬(p:ℕ)∣a) : ‖((a:K))^(p-1) - 1‖ ≤ (p:ℝ)⁻¹`
- What: Step 7 (Fermat bound) — `‖a^{p−1} − 1‖ ≤ p⁻¹`.
- How: Fermat over `ℤ` (`ZMod.pow_card_sub_one_eq_one`) gives `p ∣ a^{p−1} − 1`, transport to `K` as `p·m` with `‖m‖ ≤ 1` (`norm_intCast_le_one`).
- Hypotheses: `p ∤ a`.
- Uses from project: [`norm_natCast_p`]
- Used by: `inExpBall_natCast_pow_sub_one`, `sum_seriesEval_FtildeA`
- Visibility: private (omit `CompleteSpace`, `CharZero`)
- Lines: 1426–1446 (proof ~15)
- Notes: none

### lemma inExpBall_natCast_pow_sub_one
- Type: `(hp2 : p ≠ 2) {a : ℕ} (ha : ¬(p:ℕ)∣a) : InExpBall p (((a:K))^(p-1) - 1)`
- What: Step 7 (membership) — for `p` odd and `p ∤ a`, `a^{p−1}` lies in the exponential ball.
- How: `‖·‖^{p−1} ≤ (p⁻¹)^{p−1} ≤ (p⁻¹)^2 < p⁻¹` using `p − 1 ≥ 2` and `norm_natCast_pow_sub_one_le`.
- Hypotheses: `p ≠ 2`; `p ∤ a`.
- Uses from project: [`InExpBall`, `norm_natCast_pow_sub_one_le`]
- Used by: `sum_seriesEval_FtildeA`, `map_extLog_natCast`
- Visibility: private (omit `CompleteSpace`, `CharZero`)
- Lines: 1448–1465 (proof ~14)
- Notes: none

### theorem sum_seriesEval_FtildeA
- Type: `(hp2 : p ≠ 2) {a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) : ∑ i : Fin p, seriesEval (FtildeA p K a) (ξ^(i:ℕ)-1) = -(extLog p (a:K))`
- What: R7.6b (RJW Lemma 7.5's trace) — the evaluated `μ_p`-sum collapses to `−log_p(a)`.
- How: Step 3 per-point summed (`seriesEval_FtildeA_at_root`); the `i=0` log vanishes; collapses `Π_{i≠0} u_i = (a^{p−1})⁻¹` via Step 2 + Step 5 reindex (`prod_erase_pow_twist`); `padicLog` of the product (`padicLog_prod_of_norm_lt_one`); identifies `padicLog(a^{p−1}) = (p−1)·extLog a` (`extLog_eq_of_witness`) and `padicLog((·)⁻¹) = −padicLog(·)`; final `ring`. Hinges on `prod_erase_pow_twist`, `padicLog_prod_of_norm_lt_one`, `extLog_eq_of_witness`.
- Hypotheses: `p ≠ 2`; `p ∤ a`; `a ≠ 0`; `ξ` a primitive `p`-th root.
- Uses from project: [`FtildeA`, `uA`, `extLog`, `extLog_eq_of_witness`, `seriesEval`, `seriesEval_FtildeA_at_root`, `natCast_mul_seriesEval_uA`, `prod_erase_pow_twist`, `padicLog_prod_of_norm_lt_one`, `norm_seriesEval_uA_sub_one_lt`, `constantCoeff_uA`, `seriesEval_zero_arg`, `inExpBall_natCast_pow_sub_one`, `norm_natCast_pow_sub_one_le`, `norm_natCast_eq_one_of_not_dvd`, `MeasureR.padicLog_mul_of_norm_lt_one`, `IsPrimitiveRoot.norm_sub_one_lt`, `IsPrimitiveRoot.pow_ne_one_of_pos_of_lt`]
- Used by: `constantCoeff_mahlerK_rhoA`, `tendsto_sub_one_mul_zetaPBranch`
- Visibility: public
- Lines: 1467–1572 (proof ~98)
- Notes: OVER-50

### theorem constantCoeff_mahlerK_rhoA
- Type: `(hp2 : p ≠ 2) {a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) {ξ : K} (hξ : IsPrimitiveRoot ξ p) : constantCoeff (mahlerK p K (rhoA p K a)) = -(1 - (p:K)⁻¹) * extLog p (a:K)`
- What: R7.6c (RJW Lemma 7.5) — the mass of `x⁻¹·Res(μ_a)` is `−(1−p⁻¹)·log_p(a)`.
- How: From `p·𝓐ρ(0) = p·F̃_a(0) − Σ F̃_a(z_i)` (`p_mul_constantCoeff_mahlerK_rhoA`) with `constantCoeff_FtildeA` and `sum_seriesEval_FtildeA`, divide by `p` (`field_simp` + `linear_combination`).
- Hypotheses: `p ≠ 2`; `p ∤ a`; `a ≠ 0`; `ξ` a primitive `p`-th root.
- Uses from project: [`mahlerK`, `rhoA`, `FtildeA`, `extLog`, `p_mul_constantCoeff_mahlerK_rhoA`, `constantCoeff_FtildeA`, `sum_seriesEval_FtildeA`]
- Used by: `zetaNum_one`
- Visibility: public
- Lines: 1574–1587 (proof ~8)
- Notes: none

### theorem map_padicLog
- Type: `(y : ℚ_[p]) : algebraMap ℚ_[p] K (padicLog p y) = padicLog p (algebraMap ℚ_[p] K y)`
- What: R7.7a (descent) — `padicLog` commutes with the structure map `algebraMap ℚ_[p] K`.
- How: The structure map is an isometry (closed embedding, `ℚ_[p]` complete), so it pushes through the defining `tsum` (`IsClosedEmbedding.map_tsum`); termwise transport of ring/scalar operations.
- Hypotheses: none beyond globals (omit `IsUltrametricDist`, `CompleteSpace`).
- Uses from project: [`padicLog`]
- Used by: `map_extLog_natCast`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`)
- Lines: 1589–1600 (proof ~5)
- Notes: none

### lemma map_smul_padic
- Type: `(c x : ℚ_[p]) : algebraMap ℚ_[p] K (c • x) = c • (algebraMap ℚ_[p] K x)`
- What: The structure map is `ℚ_[p]`-linear (pulls a `ℚ_[p]`-scalar through `•`).
- How: `simp [Algebra.smul_def]`.
- Hypotheses: none beyond globals (omit `IsUltrametricDist`, `CompleteSpace`, `CharZero`).
- Uses from project: []
- Used by: `map_extLog_natCast`
- Visibility: private (omit `IsUltrametricDist`, `CompleteSpace`, `CharZero`)
- Lines: 1602–1607 (proof ~1)
- Notes: none

### theorem map_extLog_natCast
- Type: `(hp2 : p ≠ 2) {a : ℕ} (ha : ¬(p:ℕ)∣a) : extLog p ((a:K)) = algebraMap ℚ_[p] K (extLog p ((a:ℚ_[p])))`
- What: R7.7b (descent) — for `p ∤ a`, `extLog(a:K)` is the structure-map image of `extLog(a:ℚ_[p])`.
- How: Both sides via the same Fermat witness `a^{p−1} = p^0·a^{p−1}` (`extLog_eq_of_witness`, `inExpBall_natCast_pow_sub_one`); reduces to `map_padicLog` on `a^{p−1}` and the scalar pull-through.
- Hypotheses: `p ≠ 2`; `p ∤ a`.
- Uses from project: [`extLog`, `extLog_eq_of_witness`, `inExpBall_natCast_pow_sub_one`, `map_smul_padic`, `map_padicLog`]
- Used by: `zetaNum_one`
- Visibility: private (omit `CharZero`)
- Lines: 1609–1620 (proof ~6)
- Notes: none

### theorem constantCoeff_mahlerK_rhoA_eq_algebraMap
- Type: `(a : ℕ) : constantCoeff (mahlerK p K (rhoA p K a)) = algebraMap ℚ_[p] K (((zetaNum p a (1 : C(ℤ_[p]ˣ, ℤ_[p]))) : ℤ_[p]) : ℚ_[p])`
- What: R7.7c (descent, mass identification) — the `K`-mass `𝓐(ρ_a)(0)` is the structure-map image of the `ℚ_[p]`-coercion of the `ℤ_p`-mass `zetaNum p a 1`.
- How: Unfolds `mahlerK = map subtype ∘ 𝓐`, peels the constant coefficient to `ρ_a(mahlerCM 0)`, identifies through `baseChange_algCM` (`mahler 0 = 1`) and `iota = pushforward unitsValCM` (`1 ∘ unitsValCM = 1`); the `subtype ∘ algebraMap` composite is `algebraMap ℚ_[p] K ∘ (↑·)` definitionally.
- Hypotheses: none beyond globals (omit `CharZero`).
- Uses from project: [`mahlerK`, `rhoA`, `PadicMeasure.zetaNum`, `MeasureR.coeff_mahlerTransform`, `MeasureR.mahlerCM`, `MeasureR.algCM`, `MeasureR.algCM_mahler`, `MeasureR.baseChange_algCM`, `PadicMeasure.iota`, `PadicMeasure.pushforward_apply`]
- Used by: `zetaNum_one`
- Visibility: private (omit `CharZero`)
- Lines: 1622–1645 (proof ~16)
- Notes: none

### theorem zetaNum_one
- Type: `(hp2 : p ≠ 2) {a : ℕ} (ha : ¬(p:ℕ)∣a) (ha0 : a ≠ 0) : (((zetaNum p a (1 : C(ℤ_[p]ˣ, ℤ_[p]))) : ℤ_[p]) : ℚ_[p]) = -(1 - (p:ℚ_[p])⁻¹) * extLog p ((a:ℚ_[p]))`
- What: R7.7 (RJW eq:zeta p residue 2 + Lemma 7.5, descended to `ℚ_p`) — the total mass `∫_{ℤ_p^×} x⁻¹·μ_a = −(1−p⁻¹)·log_p(a)`.
- How: Computes in `ℂ_p` (which has a primitive `p`-th root by `HasEnoughRootsOfUnity`) via `constantCoeff_mahlerK_rhoA_eq_algebraMap` + `constantCoeff_mahlerK_rhoA`, then descends along the injective structure map `ℚ_p ↪ ℂ_p` using `map_extLog_natCast`.
- Hypotheses: `p ≠ 2`; `p ∤ a`; `a ≠ 0`.
- Uses from project: [`PadicMeasure.zetaNum`, `extLog`, `constantCoeff_mahlerK_rhoA_eq_algebraMap`, `constantCoeff_mahlerK_rhoA`, `map_extLog_natCast`]
- Used by: `tendsto_sub_one_mul_zetaPBranch`
- Visibility: public
- Lines: 1651–1669 (proof ~6)
- Notes: none

### lemma angleUnit_coe_ne_one
- Type: `{u : ℤ_[p]ˣ} (hgen : ∀ n, …= ⊤) : (PadicInt.angleUnit p u : ℤ_[p]) ≠ 1`
- What: The angle bracket `⟨u⟩` of a topological generator is nontrivial.
- How: If `⟨u⟩ = 1` then `u = ω(u)`, so `u^{p−1} = 1`, forcing `orderOf (unitsToZModPow p 2 u) ∣ p−1`; but `hgen 2` makes that order `φ(p²) = p(p−1)` (`Nat.totient_prime_pow`), and `p(p−1) ∣ p−1` is impossible (`nlinarith`).
- Hypotheses: `u` a topological generator at every level.
- Uses from project: [`PadicInt.angleUnit`, `PadicMeasure.unitsToZModPow`, `PadicInt.teichmuller`, `PadicInt.teichmuller_mul_angleUnit`]
- Used by: `pZpLog_angleUnit_ne_zero`
- Visibility: private
- Lines: 1671–1703 (proof ~26)
- Notes: none

### lemma pZpLog_angleUnit_ne_zero
- Type: `(hp2 : p ≠ 2) {u : ℤ_[p]ˣ} (hgen : ∀ n, …= ⊤) : pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) ≠ 0`
- What: `log_p⟨u⟩ ≠ 0` for a topological generator `u`.
- How: Via the T523 bridge `exp(1·log⟨u⟩) = ⟨u⟩` (`padicExp_smul_padicLog_eq_onePAdicPow`, `onePAdicPow_apply_one`): `log⟨u⟩ = 0` would give `⟨u⟩ = exp 0 = 1`, contradicting `angleUnit_coe_ne_one`.
- Hypotheses: `p ≠ 2`; `u` a topological generator at every level.
- Uses from project: [`pZpLog`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`, `padicExp_smul_padicLog_eq_onePAdicPow`, `PadicInt.onePAdicPow_apply_one`, `pZpExp_coe`, `padicExp_zero`, `angleUnit_coe_ne_one`]
- Used by: `tendsto_sub_one_mul_zetaPBranch`
- Visibility: private
- Lines: 1705–1720 (proof ~10)
- Notes: none

### lemma extLog_natCast_eq_pZpLog_angle
- Type: `(hp2 : p ≠ 2) {m : ℕ} {u : ℤ_[p]ˣ} (huv : (u : ℤ_[p]) = (m : ℤ_[p])) : extLog p ((m:ℚ_[p])) = ((pZpLog p (PadicInt.angleUnit p u : ℤ_[p]) : ℤ_[p]) : ℚ_[p])`
- What: `extLog(m:ℚ_[p])` equals the coercion of `log_p⟨u⟩`, where `(u:ℤ_[p])=(m:ℤ_[p])`.
- How: Via `u = ω(u)·⟨u⟩` (`teichmuller_mul_angleUnit`), `extLog_mul`, and `extLog ω = 0` (`extLog_eq_zero_of_pow_eq_one`, it is a `(p−1)`-th root); the `⟨u⟩`-part via `extLog_eq_padicLog` + `pZpLog_coe`. Builds the `ExtLogDomain` witnesses for both factors.
- Hypotheses: `p ≠ 2`; `(u:ℤ_[p]) = (m:ℤ_[p])`.
- Uses from project: [`extLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`, `extLog_eq_padicLog`, `ExtLogDomain`, `pZpLog`, `pZpLog_coe`, `PadicInt.teichmuller`, `PadicInt.teichmuller_mul_angleUnit`, `PadicInt.angleUnit`, `PadicInt.angleUnit_sub_one_mem`, `InExpBall`, `inExpBall_of_mem_span`, `inExpBall_one_sub_one`]
- Used by: `tendsto_sub_one_mul_zetaPBranch`
- Visibility: private
- Lines: 1722–1757 (proof ~28)
- Notes: none

### theorem tendsto_sub_one_mul_zetaPBranch
- Type: `(hp2 : p ≠ 2) : Tendsto (fun s => ((s:ℚ_[p])-1)*zetaPBranch p hp2 (p-1) s) (𝓝[≠] 1) (𝓝 (1 - (p:ℚ_[p])⁻¹))`
- What: RJW Theorem 7.1(ii) — `ζ_{p,p−1}` has a simple pole at `s=1` with residue `1 − p⁻¹` (as the topological limit `lim_{s→1,s≠1} (s−1)·ζ_{p,p−1}(s) = 1 − p⁻¹`).
- How: Extracts generator data; `Lq = log⟨u⟩ ≠ 0` (`pZpLog_angleUnit_ne_zero`); denominator limit `(s−1)⁻¹·denom → −Lq` (`tendsto_branch_denom_div`) inverted; numerator continuous → `num 1` (`continuous_zetaNum_branch_pairing`); `num 1 = −(1−p⁻¹)·extLog m` via `branchChar(1−1)=1` and `zetaNum_one`; `extLog m = Lq` (`extLog_natCast_eq_pZpLog_angle`); assembles the product limit and congruence to the target. Hinges on `tendsto_branch_denom_div`, `zetaNum_one`, `extLog_natCast_eq_pZpLog_angle`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`zetaPBranch`, `PadicMeasure.exists_nat_topological_generator`, `pZpLog`, `PadicInt.angleUnit`, `branchChar`, `branchChar_apply`, `PadicMeasure.zetaNum`, `PadicInt.teichmuller`, `pZpLog_angleUnit_ne_zero`, `tendsto_branch_denom_div`, `continuous_zetaNum_branch_pairing`, `zetaNum_one`, `extLog`, `extLog_natCast_eq_pZpLog_angle`]
- Used by: unused in file
- Visibility: public
- Lines: 1759–1825 (proof ~65)
- Notes: OVER-50

---

## File Summary

Total declarations: 49 (defs: 4 [`uA`, `FtildeA`, `rhoA`, plus the section also has no instances/structures]; lemmas+theorems: 45; instances: 0; structures/classes/abbrevs/inductives: 0).

Key API (used by ≥3 within this file):
- `uA` (def) — used by ~18 decls (the unit factor underpinning the whole `mass` section).
- `constantCoeff_uA` — used by ~8 decls.
- `FtildeA` (def) — used by ~8 decls (RJW's antiderivative).
- `rhoA` (def) — used by 5 decls.
- `norm_coeff_formalLog_le` — used by 3 decls.
- `norm_coeff_uA_le_one` — used by 3 decls.
- `seriesEval_one` — used by 3 decls.
- `seriesEval_uA_sub_one`, `norm_coeff_uA_sub_one_le_one`, `inExpBall_natCast_pow_sub_one` — each used by ~2-3.

Unused in file (terminal API, the §7 public theorems + the `p=2` isometry):
- `norm_onePAdicPow_sub_one` (public, p ≠ 2 sharp isometry — superseded internally by the `_le` version)
- `continuousAt_zetaPBranch` (RJW Thm 7.1(i))
- `tendsto_sub_one_mul_zetaPBranch` (RJW Thm 7.1(ii) — the file's main result)

Decls with `sorry`: none.

`set_option`: none.

Proofs over 50 lines (OVER-50) — count 7: `tendsto_branch_denom_div` (~78), `one_add_mul_derivative_FtildeA` (~115), `p_mul_constantCoeff_mahlerK_rhoA` (~123), `seriesEval_subst_formalLog` (~88), `seriesEval_FtildeA_at_root` (~58), `sum_seriesEval_FtildeA` (~98), `tendsto_sub_one_mul_zetaPBranch` (~65). All candidates for `/decompose-proof`.

Proofs 30–50 lines (long) — count 4: `branch_denom_ne_zero` (~34), `continuous_zetaNum_branch_pairing` (~37), `natCast_mul_seriesEval_uA` (~31), `prod_erase_pow_twist` (~48).
