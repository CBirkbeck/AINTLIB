# Inventory: PadicLFunctions/KubotaLeopoldt/MuA.lean

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/MuA.lean`

Namespaces: `PadicInt`, `PadicMeasure`. Imports: `PadicLFunctions.Measure.PseudoMeasure`, `PadicLFunctions.KubotaLeopoldt.ZetaValues`, `Mathlib.RingTheory.PowerSeries.Exp`.

File-level `noncomputable section`; `open PowerSeries`. `variable (p : ℕ) [hp : Fact p.Prime]` (in `PadicMeasure`).

---

### lemma isUnit_natCast_of_not_dvd
- Type: `{p : ℕ} [Fact p.Prime] {a : ℕ} (hpa : ¬ p ∣ a) : IsUnit (a : ℤ_[p])`
- What: A natural number not divisible by the prime `p` casts to a unit of the `p`-adic integers `ℤ_[p]`.
- How: Via `PadicInt.isUnit_iff` (unit iff norm = 1); antisymmetry of norm bounds, using `PadicInt.norm_int_lt_one_iff_dvd` to convert norm `< 1` into divisibility, contradicting `hpa`.
- Hypotheses: `p` prime; `a : ℕ` with `¬ p ∣ a`.
- Uses from project: []
- Used by: `isUnit_geomSum`, `psi_dirac_natCast` (both in file).
- Visibility: public
- Lines: 35–39 (proof 4 lines)
- Notes: none

### def geomSum
- Type: `(a : ℕ) : PowerSeries ℤ_[p] := ∑ i ∈ Finset.range a, (1 + X) ^ i`
- What: The geometric sum `Σ_{i<a} (1+T)^i` in `ℤ_p⟦T⟧`, the cofactor in `(1+T)^a − 1 = T·geomSum a` (RJW Prop. 4.4).
- How: Direct definition as a finite sum of powers of `1 + X`.
- Hypotheses: `a : ℕ`.
- Uses from project: []
- Used by: `constantCoeff_geomSum`, `geomSum_mul_X`, `isUnit_geomSum`, `FaNum`, `X_mul_FaNum`, `Fa`, `geomSum_mul_Fa`, `dirac_natCast_sub_one_mul_muA`, `X_mul_subst_exp_Fa`, `psi_muA` (in file).
- Visibility: public
- Lines: 51–52 (defn, no proof)
- Notes: none

### lemma constantCoeff_geomSum
- Type: `(a : ℕ) : constantCoeff (geomSum p a) = (a : ℤ_[p])`
- What: The constant coefficient of `geomSum a` equals `a` (each summand `(1+T)^i` has constant term 1).
- How: `simp [geomSum]`.
- Hypotheses: `a : ℕ`.
- Uses from project: [geomSum]
- Used by: `isUnit_geomSum` (in file).
- Visibility: public; `@[simp]`
- Lines: 54–55 (proof 1 line)
- Notes: none

### lemma geomSum_mul_X
- Type: `(a : ℕ) : geomSum p a * X = (1 + X) ^ a - 1`
- What: Multiplying the geometric sum by `T` telescopes to `(1+T)^a − 1`.
- How: Mathlib's `geom_sum_mul (1 + X) a` then `add_sub_cancel_left` to simplify `(1+X) − 1`.
- Hypotheses: `a : ℕ`.
- Uses from project: [geomSum]
- Used by: `one_add_X_pow_sub_one_mul_Fa`, `psi_muA` (in file).
- Visibility: public
- Lines: 58–60 (proof 3 lines)
- Notes: none

### lemma isUnit_geomSum
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) : IsUnit (geomSum p a)`
- What: When `p ∤ a`, the power series `geomSum a` is a unit of `ℤ_p⟦T⟧` (its constant coefficient `a` is a unit).
- How: `PowerSeries.isUnit_iff_constantCoeff` reduces to a unit constant coefficient; `constantCoeff_geomSum` gives `a`, and `isUnit_natCast_of_not_dvd` finishes.
- Hypotheses: `p` prime; `¬ p ∣ a`.
- Uses from project: [geomSum, constantCoeff_geomSum, isUnit_natCast_of_not_dvd]
- Used by: `geomSum_mul_Fa` (in file).
- Visibility: public
- Lines: 62–64 (proof 3 lines)
- Notes: none

### def FaNum
- Type: `(a : ℕ) : PowerSeries ℤ_[p] := PowerSeries.mk fun n => coeff (n + 1) (geomSum p a)`
- What: The numerator `(geomSum a − a)/T` of `F_a`, defined by shifting coefficients of `geomSum a` down by one.
- How: Direct definition via `PowerSeries.mk` with the shifted coefficient.
- Hypotheses: `a : ℕ`.
- Uses from project: [geomSum]
- Used by: `X_mul_FaNum`, `Fa`, `geomSum_mul_Fa` (in file).
- Visibility: public
- Lines: 67–68 (defn)
- Notes: none

### lemma X_mul_FaNum
- Type: `(a : ℕ) : X * FaNum p a = geomSum p a - (a : PowerSeries ℤ_[p])`
- What: `T·FaNum a = geomSum a − a`, expressing that `FaNum` is genuinely the quotient `(geomSum a − a)/T`.
- How: Coefficientwise (`ext n`), case split on `n`; uses `coeff_succ_X_mul`, `coeff_C`, and `map_natCast` to handle the constant term; `simp [FaNum]`.
- Hypotheses: `a : ℕ`.
- Uses from project: [FaNum, geomSum]
- Used by: `one_add_X_pow_sub_one_mul_Fa` (in file).
- Visibility: public
- Lines: 70–78 (proof 9 lines)
- Notes: none

### def Fa
- Type: `(a : ℕ) : PowerSeries ℤ_[p] := FaNum p a * Ring.inverse (geomSum p a)`
- What: RJW Prop. 4.4 power series `F_a = 1/T − a/((1+T)^a−1)`, realised as `((geomSum a − a)/T)·geomSum a⁻¹`; junk value 0 when `p ∣ a`.
- How: Direct definition as `FaNum` times the ring-theoretic inverse of `geomSum`.
- Hypotheses: `a : ℕ`.
- Uses from project: [FaNum, geomSum]
- Used by: `geomSum_mul_Fa`, `one_add_X_pow_sub_one_mul_Fa`, `muA`, `mahlerTransform_muA`, `X_mul_subst_exp_Fa`, `muA_apply_powCM` (in file).
- Visibility: public
- Lines: 84–85 (defn)
- Notes: none

### lemma geomSum_mul_Fa
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) : geomSum p a * Fa p a = FaNum p a`
- What: When `p ∤ a`, `geomSum a · F_a = FaNum a`, i.e. multiplying back by `geomSum` cancels its inverse.
- How: Unfold `Fa`, reassociate, then `Ring.mul_inverse_cancel` using `isUnit_geomSum p hpa`.
- Hypotheses: `p` prime; `¬ p ∣ a`.
- Uses from project: [geomSum, Fa, FaNum, isUnit_geomSum]
- Used by: `one_add_X_pow_sub_one_mul_Fa` (in file).
- Visibility: public
- Lines: 87–90 (proof 3 lines)
- Notes: none

### lemma one_add_X_pow_sub_one_mul_Fa
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) : ((1 + X) ^ a - 1) * Fa p a = geomSum p a - (a : PowerSeries ℤ_[p])`
- What: The characterising identity `((1+T)^a − 1)·F_a = geomSum a − a`, the formal content of `F_a = 1/T − a/((1+T)^a−1)` (RJW Lem. 4.3).
- How: Rewrite `(1+X)^a − 1` as `geomSum·X` (via `geomSum_mul_X`), commute/reassociate, apply `geomSum_mul_Fa` then `X_mul_FaNum`.
- Hypotheses: `p` prime; `¬ p ∣ a`.
- Uses from project: [geomSum_mul_X, geomSum, Fa, geomSum_mul_Fa, X_mul_FaNum]
- Used by: `dirac_natCast_sub_one_mul_muA`, `X_mul_subst_exp_Fa` (in file).
- Visibility: public
- Lines: 94–97 (proof 2 lines)
- Notes: none

### def muA
- Type: `(a : ℕ) : PadicMeasure p ℤ_[p] := (mahlerLinearEquiv p).symm (Fa p a)`
- What: RJW Def. 4.5 — the measure `μ_a` on `ℤ_p` whose Mahler transform is `F_a`.
- How: Apply the inverse of the Mahler linear equivalence to `Fa`.
- Hypotheses: `a : ℕ`.
- Uses from project: [Fa] (and `mahlerLinearEquiv`)
- Used by: `mahlerTransform_muA`, `dirac_natCast_sub_one_mul_muA`, `muA_apply_powCM`, `psi_muA`, `res_units_muA_apply_powCM` (in file).
- Visibility: public
- Lines: 101–102 (defn)
- Notes: none

### lemma mahlerTransform_muA
- Type: `(a : ℕ) : mahlerTransform p (muA p a) = Fa p a`
- What: The Mahler transform of `μ_a` is `F_a` (left inverse of the equivalence's symm).
- How: `(mahlerLinearEquiv p).apply_symm_apply (Fa p a)`.
- Hypotheses: `a : ℕ`.
- Uses from project: [muA, Fa] (and `mahlerLinearEquiv`)
- Used by: `dirac_natCast_sub_one_mul_muA`, `muA_apply_powCM` (in file).
- Visibility: public; `@[simp]`
- Lines: 104–106 (proof 1 line)
- Notes: none

### lemma mahlerTransform_sub
- Type: `(μ ν : PadicMeasure p ℤ_[p]) : mahlerTransform p (μ - ν) = mahlerTransform p μ - mahlerTransform p ν`
- What: The Mahler transform is additive on differences of measures.
- How: `map_sub (mahlerTransformₗ p) μ ν` (it is a linear map).
- Hypotheses: `μ ν : PadicMeasure p ℤ_[p]`.
- Uses from project: [] (uses `mahlerTransformₗ`/`mahlerTransform`)
- Used by: `dirac_natCast_sub_one_mul_muA`, `dirac_natCast_sub_one_ne_zero` (in file).
- Visibility: public; `@[simp]`
- Lines: 108–111 (proof 1 line)
- Notes: none

### lemma mahlerTransform_smul
- Type: `(c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) : mahlerTransform p (c • μ) = c • mahlerTransform p μ`
- What: The Mahler transform commutes with `ℤ_p`-scalar multiplication of measures.
- How: `map_smul (mahlerTransformₗ p) c μ`.
- Hypotheses: `c : ℤ_[p]`, `μ` a measure.
- Uses from project: [] (uses `mahlerTransformₗ`/`mahlerTransform`)
- Used by: `dirac_natCast_sub_one_mul_muA`, instance `SMulCommClass` (in file).
- Visibility: public; `@[simp]`
- Lines: 113–116 (proof 1 line)
- Notes: none

### lemma dirac_natCast_sub_one_mul_muA
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) : (dirac p ((a : ℕ) : ℤ_[p]) - 1) * muA p a = (∑ i ∈ Finset.range a, dirac p ((i : ℕ) : ℤ_[p])) - (a : ℤ_[p]) • 1`
- What: Convolution form of the characterising identity: `([a] − [0])·μ_a = Σ_{i<a}[i] − a·[0]` in `Λ(ℤ_p)`.
- How: Compute Mahler transform of both sides; key sub-fact `hsum` shows the transform of `Σ[i]` is `geomSum a` (via `mahlerTransform_dirac` + `binomialSeries_nat`); then `mahlerTransform_injective` plus `one_add_X_pow_sub_one_mul_Fa` and `mahlerTransform_mul`.
- Hypotheses: `p` prime; `¬ p ∣ a`.
- Uses from project: [dirac, muA, geomSum, mahlerTransform_dirac, mahlerTransform_muA, one_add_X_pow_sub_one_mul_Fa, mahlerTransform_sub, mahlerTransform_one, mahlerTransform_mul, mahlerTransform_smul, mahlerTransform_injective, binomialSeries_nat, mahlerTransformₗ]
- Used by: `psi_muA` (in file).
- Visibility: public
- Lines: 121–137 (proof ~16 lines)
- Notes: none

### instance instIsDomain
- Type: `IsDomain (PadicMeasure p ℤ_[p])`
- What: The measure algebra `Λ(ℤ_p)` is an integral domain.
- How: Transport `IsDomain` from `ℤ_p⟦T⟧` (a domain) along the ring isomorphism `mahlerRingEquiv p` via `MulEquiv.isDomain`.
- Hypotheses: `p` prime (ambient).
- Uses from project: [] (uses `mahlerRingEquiv`)
- Used by: unused in file (provides instance used implicitly by cancellation lemmas).
- Visibility: public (instance)
- Lines: 140–141 (proof 1 line)
- Notes: none

### instance (SMulCommClass)
- Type: `SMulCommClass ℤ_[p] (PadicMeasure p ℤ_[p]) (PadicMeasure p ℤ_[p])`
- What: Scalar multiplication by `ℤ_p` commutes with ring multiplication of measures: `c • (μ*ν) = μ*(c•ν)`.
- How: Reduce via `change` to the smul-comm statement, apply `mahlerTransform_injective`, push through `mahlerTransform_smul`/`mahlerTransform_mul`, then `mul_smul_comm`.
- Hypotheses: `p` prime (ambient).
- Uses from project: [mahlerTransform_injective, mahlerTransform_smul, mahlerTransform_mul]
- Used by: unused in file (instance, used implicitly e.g. in `mul_smul_comm` steps).
- Visibility: public (instance, anonymous)
- Lines: 143–149 (proof ~6 lines)
- Notes: none

### lemma dirac_natCast_sub_one_ne_zero
- Type: `{a : ℕ} (ha : a ≠ 0) : (dirac p ((a : ℕ) : ℤ_[p]) - 1 : PadicMeasure p ℤ_[p]) ≠ 0`
- What: For `a ≠ 0`, the element `[a] − [0]` of `Λ(ℤ_p)` is nonzero.
- How: Suppose zero; apply Mahler transform, reduce to `(1+T)^a = 1` via `binomialSeries_nat`; take coefficient at `1` using `Polynomial.coeff_one_add_X_pow`, giving `a = 0` by `omega`, contradiction.
- Hypotheses: `a ≠ 0`.
- Uses from project: [dirac, mahlerTransform_sub, mahlerTransform_one, mahlerTransform_dirac, mahlerTransform_zero, binomialSeries_nat]
- Used by: `psi_muA` (in file).
- Visibility: public
- Lines: 151–162 (proof ~11 lines)
- Notes: none

### def delQ
- Type: `(G : PowerSeries ℚ_[p]) : PowerSeries ℚ_[p] := (1 + X) * PowerSeries.derivativeFun G`
- What: The operator `∂ = (1+T) d/dT` over `ℚ_p` (the `ℚ_p`-analogue of `PadicMeasure.del`).
- How: Direct definition as `(1+X)` times the formal derivative.
- Hypotheses: `G : PowerSeries ℚ_[p]`.
- Uses from project: []
- Used by: `map_del`, `derivativeFun_subst_exp`, `constantCoeff_iterate_delQ`, `muA_apply_powCM` (in file).
- Visibility: public
- Lines: 173–174 (defn)
- Notes: TODO/cleanup note in docstring (merge with `PadicMeasure.del`).

### lemma map_derivativeFun
- Type: `(F : PowerSeries ℤ_[p]) : PowerSeries.map PadicInt.Coe.ringHom (derivativeFun F) = derivativeFun (PowerSeries.map PadicInt.Coe.ringHom F)`
- What: The coercion `ℤ_p → ℚ_p` commutes with the formal derivative of power series.
- How: Coefficientwise (`ext n`), `simp [coeff_derivativeFun]`.
- Hypotheses: `F : PowerSeries ℤ_[p]`.
- Uses from project: [] (uses `PadicInt.Coe.ringHom`)
- Used by: `map_del` (in file).
- Visibility: public
- Lines: 176–180 (proof 2 lines)
- Notes: none

### lemma map_del
- Type: `(F : PowerSeries ℤ_[p]) : PowerSeries.map PadicInt.Coe.ringHom (del p F) = delQ p (PowerSeries.map PadicInt.Coe.ringHom F)`
- What: The coercion `ℤ_p → ℚ_p` intertwines the integral operator `del` with its rational analogue `delQ`.
- How: Unfold `del` and `delQ`, push `map` through mul/add/one/X, then `map_derivativeFun`.
- Hypotheses: `F : PowerSeries ℤ_[p]`.
- Uses from project: [del, delQ, map_derivativeFun]
- Used by: `muA_apply_powCM` (in file).
- Visibility: public
- Lines: 182–185 (proof 1 line)
- Notes: none

### lemma hasSubst_exp_sub_one
- Type: `HasSubst (exp ℚ_[p] - 1)`
- What: The power series `exp(t) − 1` is a valid substitution argument (its constant coefficient is 0).
- How: `HasSubst.of_constantCoeff_zero'` with `simp` verifying constant coefficient 0.
- Hypotheses: `p` prime (ambient).
- Uses from project: []
- Used by: `derivativeFun_subst_exp`, `constantCoeff_subst_exp`, `X_mul_subst_exp_Fa` (in file).
- Visibility: public
- Lines: 187–188 (proof 1 line)
- Notes: none

### lemma derivativeFun_subst_exp
- Type: `(F : PowerSeries ℚ_[p]) : derivativeFun (F.subst (exp ℚ_[p] - 1)) = (delQ p F).subst (exp ℚ_[p] - 1)`
- What: Chain rule for substitution `T = e^t − 1`: `d/dt (F(e^t−1)) = (∂F)(e^t−1)`, i.e. `d/dt` becomes `∂` (RJW Lem. 4.3).
- How: `calc` using `derivative_subst` (mathlib chain rule for `subst`), `derivative_exp`, and `subst_mul`/`subst_add`/`subst_X`; auxiliary facts `hone` (subst of 1) and `hder` (`d/dX (exp−1) = exp`).
- Hypotheses: `F : PowerSeries ℚ_[p]`.
- Uses from project: [hasSubst_exp_sub_one, delQ]
- Used by: `constantCoeff_iterate_delQ` (in file).
- Visibility: public
- Lines: 192–207 (proof ~16 lines)
- Notes: none

### lemma constantCoeff_subst_exp
- Type: `(F : PowerSeries ℚ_[p]) : constantCoeff (F.subst (exp ℚ_[p] - 1)) = constantCoeff F`
- What: Substituting `T = e^t − 1` does not change the constant coefficient of a power series.
- How: Rewrite via `constantCoeff_subst` and `finsum_eq_single _ 0`, killing `d ≠ 0` terms using `zero_pow` on the zero constant coefficient of `exp−1`; `simp`.
- Hypotheses: `F : PowerSeries ℚ_[p]`.
- Uses from project: [hasSubst_exp_sub_one]
- Used by: `constantCoeff_iterate_delQ` (in file).
- Visibility: public
- Lines: 209–218 (proof ~10 lines)
- Notes: none

### lemma constantCoeff_iterate_derivativeFun
- Type: `(k : ℕ) (G : PowerSeries ℚ_[p]) : constantCoeff (derivativeFun^[k] G) = (k.factorial : ℚ_[p]) * coeff k G`
- What: The constant coefficient of the `k`-fold formal derivative equals `k!` times the degree-`k` coefficient.
- How: Induction on `k` (generalizing `G`); base via `coeff_zero_eq_constantCoeff`; step uses `coeff_derivativeFun`, `Nat.factorial_succ`, `push_cast`, `ring`.
- Hypotheses: `k : ℕ`, `G` a power series over `ℚ_p`.
- Uses from project: []
- Used by: unused in file.
- Visibility: public
- Lines: 220–228 (proof ~9 lines)
- Notes: none — appears unused in this file.

### lemma constantCoeff_iterate_delQ
- Type: `(k : ℕ) (F : PowerSeries ℚ_[p]) : constantCoeff ((delQ p)^[k] F) = (k.factorial : ℚ_[p]) * coeff k (F.subst (exp ℚ_[p] - 1))`
- What: `(∂^k F)(0) = k! · [t^k](F(e^t−1))` — iterated `∂` at 0 extracts Taylor coefficients after the exp substitution.
- How: Induction on `k` (generalizing `F`); base via `constantCoeff_subst_exp`; step uses `derivativeFun_subst_exp` (turning `delQ` iterate into a derivative on the substituted series), `coeff_derivativeFun`, `Nat.factorial_succ`.
- Hypotheses: `k : ℕ`, `F` a power series over `ℚ_p`.
- Uses from project: [delQ, constantCoeff_subst_exp, derivativeFun_subst_exp]
- Used by: `muA_apply_powCM` (in file).
- Visibility: public
- Lines: 233–242 (proof ~10 lines)
- Notes: none

### lemma X_mul_subst_exp_Fa
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) : X * (PowerSeries.map PadicInt.Coe.ringHom (Fa p a)).subst (exp ℚ_[p] - 1) = bernoulliPowerSeries ℚ_[p] - rescale (a : ℚ_[p]) (bernoulliPowerSeries ℚ_[p])`
- What: Bernoulli evaluation `t·f_a(t) = B(t) − B(at)` with `f_a = F_a(e^t−1)` (algebraic content of RJW Lem. 4.2).
- How: Map the characterising identity to `ℚ_p` (`hQ`), substitute `T = e^t−1` (`hsub`, using `exp_pow_eq_rescale_exp`); the Bernoulli side uses `bernoulliPowerSeries_mul_exp_sub_one`, a telescoping factorisation of `rescale_a exp − 1` (`hfac` via `geom_sum_mul`), and `rescale`-linearity; finally `mul_right_cancel₀` by the regular factor `e^{at}−1 ≠ 0` (`hreg`) closes the `calc`.
- Hypotheses: `p` prime; `¬ p ∣ a` (forces `a ≠ 0`, so `e^{at}−1` cancellable).
- Uses from project: [hasSubst_exp_sub_one, Fa, geomSum, one_add_X_pow_sub_one_mul_Fa]
- Used by: `muA_apply_powCM` (in file).
- Visibility: public
- Lines: 247–311 (proof ~64 lines)
- Notes: OVER-50 (needs /decompose-proof). No sorry/set_option.

### theorem muA_apply_powCM
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) (k : ℕ) : ((muA p a (powCM p k) : ℤ_[p]) : ℚ_[p]) = (-1) ^ k * (1 - (a : ℚ_[p]) ^ (k + 1)) * ((zetaNeg k : ℚ) : ℚ_[p])`
- What: RJW Prop. 4.6 — the `k`-th moment `∫_{ℤ_p} x^k dμ_a = (−1)^k (1 − a^{k+1}) ζ(−k)` (in `ℚ_p`).
- How: `apply_powCM` rewrites the moment as a constant coefficient of `del^[k] Fa`; `hiter` (induction) moves `map` past the `del`/`delQ` iterate; `constantCoeff_iterate_delQ` introduces `k!·coeff k`; `hcoeff` extracts the coefficient from `X_mul_subst_exp_Fa` (via `coeff_succ_X_mul`, `coeff_rescale`, Bernoulli coeff); finishes by unfolding `zetaNeg`, parity split (`Nat.even_or_odd`) with `field_simp`/`ring`.
- Hypotheses: `p` prime; `¬ p ∣ a`; `k : ℕ`.
- Uses from project: [muA, powCM, mahlerTransform_muA, del, Fa, map_del, constantCoeff_iterate_delQ, delQ, X_mul_subst_exp_Fa, zetaNeg, apply_powCM]
- Used by: unused in file (consumed externally; `res_units_muA_apply_powCM` calls it).
- Visibility: public
- Lines: 314–353 (proof ~40 lines)
- Notes: long(30-50). No sorry/set_option.

### theorem psi_phi_mul
- Type: `(ν μ : PadicMeasure p ℤ_[p]) : psi p (phi p ν * μ) = ν * psi p μ`
- What: Projection formula `ψ(φ(ν)·μ) = ν·ψ(μ)` in `Λ(ℤ_p)` (the ξ-free engine for RJW Lem. 4.7).
- How: Test against `f` (`LinearMap.ext`); unfold both sides to integrals against the indicator `charFn` of `pℤ_p` times shifted/composed test functions; reduce to a pointwise identity of integrands, splitting on `‖y‖ < 1` using non-archimedean norm bounds (`PadicInt.nonarchimedean`, `mem_pZp_of_mul`), `mul_shiftDiv_of_mem`/`shiftDiv_mul`, and `Set.indicator` membership lemmas.
- Hypotheses: `ν μ` measures on `ℤ_p`.
- Uses from project: [psi, phi, convInner, shiftDiv, mulCM, mem_pZp_of_mul, mul_shiftDiv_of_mem, shiftDiv_mul, isClopen_pZp] (and `LocallyConstant.charFn`)
- Used by: `psi_muA` (in file).
- Visibility: public
- Lines: 360–395 (proof ~36 lines)
- Notes: long(30-50). No sorry/set_option.

### lemma phi_dirac
- Type: `(x : ℤ_[p]) : phi p (dirac p x) = dirac p ((p : ℤ_[p]) * x)`
- What: The operator `φ` sends the Dirac measure `[x]` to `[p·x]`.
- How: `LinearMap.ext fun _ => rfl` (definitional).
- Hypotheses: `x : ℤ_[p]`.
- Uses from project: [phi, dirac]
- Used by: `psi_dirac_mul`, `psi_muA` (in file).
- Visibility: public; `@[simp]`
- Lines: 397–399 (proof 1 line)
- Notes: none

### lemma psi_dirac_mul
- Type: `(x : ℤ_[p]) : psi p (dirac p ((p : ℤ_[p]) * x)) = dirac p x`
- What: `ψ([p·x]) = [x]` — `ψ` undoes multiplication by `p` on Dirac measures.
- How: Rewrite `[p·x]` as `φ[x]` (via `phi_dirac`), then `psi_phi`.
- Hypotheses: `x : ℤ_[p]`.
- Uses from project: [psi, dirac, phi_dirac, psi_phi]
- Used by: `psi_dirac_natCast` (in file).
- Visibility: public; `@[simp]`
- Lines: 401–403 (proof 1 line)
- Notes: none

### lemma psi_dirac_of_isUnit
- Type: `{x : ℤ_[p]} (hx : IsUnit x) : psi p (dirac p x) = 0`
- What: `ψ([x]) = 0` when `x` is a unit (i.e. `x ∉ pℤ_p`).
- How: Test against `f`; the integrand is `charFn(pℤ_p)(x)·…`, which vanishes since a unit has norm 1 hence `x ∉ {‖z‖<1}` (`PadicInt.isUnit_iff`), via `Set.indicator_of_notMem`.
- Hypotheses: `IsUnit x`.
- Uses from project: [psi, dirac, shiftDiv, isClopen_pZp] (and `LocallyConstant.charFn`)
- Used by: `psi_dirac_natCast` (in file).
- Visibility: public
- Lines: 405–413 (proof ~9 lines)
- Notes: none

### lemma psi_zero
- Type: `psi p (0 : PadicMeasure p ℤ_[p]) = 0`
- What: `ψ` sends the zero measure to zero.
- How: `LinearMap.ext fun _ => rfl` (definitional).
- Hypotheses: none (ambient `p`).
- Uses from project: [psi]
- Used by: `psi_sum` (in file).
- Visibility: public
- Lines: 415–416 (proof 1 line)
- Notes: none

### lemma psi_add
- Type: `(μ ν : PadicMeasure p ℤ_[p]) : psi p (μ + ν) = psi p μ + psi p ν`
- What: `ψ` is additive on measures.
- How: `LinearMap.ext fun _ => rfl` (definitional).
- Hypotheses: `μ ν` measures.
- Uses from project: [psi]
- Used by: `psi_sum` (in file).
- Visibility: public
- Lines: 418–419 (proof 1 line)
- Notes: none

### lemma psi_smul
- Type: `(c : ℤ_[p]) (μ : PadicMeasure p ℤ_[p]) : psi p (c • μ) = c • psi p μ`
- What: `ψ` commutes with `ℤ_p`-scalar multiplication of measures.
- How: `LinearMap.ext fun _ => rfl` (definitional).
- Hypotheses: `c : ℤ_[p]`, `μ` a measure.
- Uses from project: [psi]
- Used by: `psi_muA` (in file).
- Visibility: public
- Lines: 421–422 (proof 1 line)
- Notes: none

### lemma psi_sum
- Type: `{ι : Type*} (s : Finset ι) (f : ι → PadicMeasure p ℤ_[p]) : psi p (∑ i ∈ s, f i) = ∑ i ∈ s, psi p (f i)`
- What: `ψ` commutes with finite sums of measures.
- How: `Finset.induction`; empty case from `psi_zero`, insert case from `Finset.sum_insert` + `psi_add`.
- Hypotheses: `s` a finset, `f` an indexed family of measures.
- Uses from project: [psi, psi_zero, psi_add]
- Used by: `psi_muA` (in file).
- Visibility: public
- Lines: 424–429 (proof ~3 lines)
- Notes: none

### lemma dirac_zero_eq_one
- Type: `dirac p (0 : ℤ_[p]) = 1`
- What: `δ_0 = 1` (the Dirac measure at 0 is the unit of `Λ(ℤ_p)`).
- How: `mahlerTransform_injective`; both transforms equal `1` via `mahlerTransform_dirac` + `binomialSeries_zero` and `mahlerTransform_one`.
- Hypotheses: none (ambient `p`).
- Uses from project: [dirac, mahlerTransform_injective, mahlerTransform_dirac, mahlerTransform_one, binomialSeries_zero]
- Used by: `psi_muA`, `phi_dirac` use-site in `psi_muA` (hphi_va, htel, hpsi2) (in file).
- Visibility: public
- Lines: 432–434 (proof 2 lines)
- Notes: none

### lemma psi_dirac_natCast
- Type: `(n : ℕ) : psi p (dirac p ((n : ℕ) : ℤ_[p])) = if p ∣ n then dirac p ((n / p : ℕ) : ℤ_[p]) else 0`
- What: `ψ([n]) = [n/p]` if `p ∣ n`, else `0` (for `n : ℕ`).
- How: Case split on `p ∣ n`; divisible case writes `n = p·m`, casts, applies `psi_dirac_mul` and `Nat.mul_div_cancel_left`; non-divisible case applies `psi_dirac_of_isUnit` with `isUnit_natCast_of_not_dvd`.
- Hypotheses: `n : ℕ`.
- Uses from project: [psi, dirac, psi_dirac_mul, psi_dirac_of_isUnit, isUnit_natCast_of_not_dvd]
- Used by: `psi_muA` (in file).
- Visibility: public
- Lines: 437–446 (proof ~9 lines)
- Notes: none

### theorem psi_muA
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) : psi p (muA p a) = muA p a`
- What: RJW Lem. 4.7 — `ψ(μ_a) = μ_a` (ψ-invariance of `μ_a`).
- How: Establishes `φ([a]−1)=[ap]−1` (`hphi_va`); telescope `(Σ_{j<p}[aj])·([a]−1)=[ap]−1` (`htel`, via `dirac_mul_dirac` + `Finset.sum_range_sub`); product/Mahler identities `(Σ[aj])·(Σ[i])=Σ_{n<ap}[n]` (`hgeom`); `ψ(Σ_{n<ap}[n])=Σ_{m<a}[m]` (`hpsi1`, a `Finset.sum_nbij'` reindex by `n↦n/p`); `ψ(Σ_{j<p}[aj])=1` (`hpsi2`); then the key chain `([a]−1)·ψμ_a = ψ(([ap]−1)·μ_a) = … = ([a]−1)·μ_a` via `psi_phi_mul`, `dirac_natCast_sub_one_mul_muA`, and cancels `[a]−1` by `mul_left_cancel₀` with `dirac_natCast_sub_one_ne_zero`.
- Hypotheses: `p` prime; `¬ p ∣ a`.
- Uses from project: [psi, muA, dirac, phi_dirac, dirac_zero_eq_one, dirac_mul_dirac, mahlerTransform, mahlerTransformₗ, geomSum, geomSum_mul_X, mahlerTransform_dirac, mahlerTransform_injective, mahlerTransform_mul, binomialSeries_nat, psi_sum, psi_dirac_natCast, psi_phi_mul, dirac_natCast_sub_one_mul_muA, psi_sub, psi_smul, dirac_natCast_sub_one_ne_zero]
- Used by: `res_units_muA_apply_powCM` (in file).
- Visibility: public
- Lines: 454–545 (proof ~91 lines)
- Notes: OVER-50 (needs /decompose-proof). Uses `classical`. No sorry/set_option.

### lemma phi_apply_powCM
- Type: `(μ : PadicMeasure p ℤ_[p]) (k : ℕ) : phi p μ (powCM p k) = (p : ℤ_[p]) ^ k * μ (powCM p k)`
- What: Evaluating `φμ` on the monomial `x^k` scales the `μ`-moment by `p^k`.
- How: `change` to `μ` of `(powCM k)∘(mulCM p)`; rewrite that composite as `p^k • powCM k` (by `ext`/`simp [powCM, mulCM, mul_pow]`), then `map_smul` + `smul_eq_mul`.
- Hypotheses: `μ` a measure, `k : ℕ`.
- Uses from project: [phi, powCM, mulCM]
- Used by: `res_units_muA_apply_powCM` (in file).
- Visibility: public
- Lines: 549–554 (proof ~4 lines)
- Notes: none

### theorem res_units_muA_apply_powCM
- Type: `{a : ℕ} (hpa : ¬ p ∣ a) (k : ℕ) : ((res p (isClopen_units p) (muA p a) (powCM p k) : ℤ_[p]) : ℚ_[p]) = (-1) ^ k * (1 - (p : ℚ_[p]) ^ k) * (1 - (a : ℚ_[p]) ^ (k + 1)) * ((zetaNeg k : ℚ) : ℚ_[p])`
- What: RJW Prop. 4.8 — restricting `μ_a` to `ℤ_p^×` removes the Euler factor: `∫_{ℤ_p^×} x^k dμ_a = (−1)^k (1−p^k)(1−a^{k+1}) ζ(−k)`.
- How: `res_units_eq` expresses the restricted moment as `(μ_a − φ(ψμ_a))`-style difference; `psi_muA` replaces `ψμ_a` by `μ_a`; `phi_apply_powCM` extracts the `p^k` factor; `muA_apply_powCM` plugs in the unrestricted moment; `push_cast` + `ring`.
- Hypotheses: `p` prime; `¬ p ∣ a`; `k : ℕ`.
- Uses from project: [res, muA, powCM, psi_muA, phi_apply_powCM, muA_apply_powCM, zetaNeg, isClopen_units]
- Used by: unused in file (terminal result, consumed externally).
- Visibility: public
- Lines: 559–566 (proof ~4 lines)
- Notes: none

---

## File Summary

- **Total declarations: 33** — 6 defs (`geomSum`, `FaNum`, `Fa`, `muA`, `delQ`; plus `isUnit_natCast_of_not_dvd` is a lemma — recount: defs = `geomSum`, `FaNum`, `Fa`, `muA`, `delQ` = **5 defs**), **26 lemmas/theorems**, **2 instances** (`instIsDomain`, anonymous `SMulCommClass`). (5 + 26 + 2 = 33.)
- **Key API (used by ≥3 in-file):**
  - `geomSum` — used by 10+ decls.
  - `Fa` — used by 6 decls.
  - `muA` — used by 5 decls.
  - `dirac_zero_eq_one`, `phi_dirac` — used in multiple sub-proofs of `psi_muA`.
  - `hasSubst_exp_sub_one` — used by 3 decls.
  - (Mahler-transform helpers `mahlerTransform_sub`/`_smul` each used by 2; `binomialSeries_nat` from `PseudoMeasure` is pervasively relied on.)
- **Unused in file:** `constantCoeff_iterate_derivativeFun` (lemma, no in-file caller); the two instances `instIsDomain` and `SMulCommClass` (used only implicitly by typeclass resolution / cancellation); terminal results `muA_apply_powCM` and `res_units_muA_apply_powCM` are consumed externally (the former is called by the latter).
- **Decls with `sorry`: none.**
- **`set_option`: none.** `classical` is used in `psi_muA` (and `psi_sum`).
- **Proofs > 50 lines (OVER-50): 2** — `X_mul_subst_exp_Fa` (~64 lines, 247–311) and `psi_muA` (~91 lines, 454–545). Both flagged for `/decompose-proof`.
- **Proofs 30–50 lines: 2** — `muA_apply_powCM` (~40 lines, 314–353) and `psi_phi_mul` (~36 lines, 360–395).

Output path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_KubotaLeopoldt_MuA.md`
