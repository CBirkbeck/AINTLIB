# Inventory: PadicLFunctions/MeasureR/FormalPsi.lean

File-wide context: `namespace PadicLFunctions`; `variable (p : ℕ) [hp : Fact p.Prime]`.
Three sections: `digits` (general `CommRing R`), `integral` and `bridge` (normed field `K` over `ℚ_[p]`, ultrametric, complete; `integerRing K` coefficients). Builds the formal power-series avatar of the measure-level trace operator `ψ`, the digit decomposition `F = Σ_{i<p} (1+T)^i·φ(G_i)`, the Mahler-transform bridge to `MeasureR`, junk-total `K`-evaluation `seriesEval`, and the realised `Eqphipsi` evaluation identity at `T=0`.

---

### def phiSeries
- Type: `noncomputable def phiSeries (F : PowerSeries R) : PowerSeries R`
- What: The formal Frobenius substitution `φ : F(T) ↦ F((1+T)^p − 1)`, the series-side of the measure operator `phi`.
- How: Definitional — `F.subst ((1 + X)^p − 1)`.
- Hypotheses: `R` a `CommRing`.
- Uses from project: []
- Used by: `hasSubst_one_add_X_pow_sub_one` (implicitly via simp lemmas about it), `phiSeries_zero`, `constantCoeff_phiSeries`, `phiSeries_C_mul`, `IsDigitDecomp`, `map_phiSeries`, `one_add_mul_derivative_phiSeries`, `mahlerTransform_phi`, `mahlerTransform_sum_dirac_mul_phi`, `psiSeries_phi`, `phiSeries_C`, `psiSeries_add`, `psiSeries_C_mul`, `seriesEval_phi_of_summable_prod`, `mahlerK_phi`, `seriesEval_phi_at_root`, `seriesEval_phi_at_root_of_summable`, `norm_coeff_phiSeries_le_one`, `norm_coeff_phiSeries_le_linear`, `sum_seriesEval_mahlerK`, `phiSeries_formalLog`
- Visibility: public
- Lines: 37-38 (def, no proof)
- Notes: none

### lemma hasSubst_one_add_X_pow_sub_one
- Type: `lemma hasSubst_one_add_X_pow_sub_one : PowerSeries.HasSubst ((1 + X)^p − 1 : PowerSeries R)`
- What: The substituend `(1+T)^p − 1` always has constant coefficient `0`, so `φ = subst` is well-defined over any `CommRing`.
- How: `HasSubst.of_constantCoeff_zero'` after `simp` discharges the constant-coefficient-zero side goal.
- Hypotheses: `R` a `CommRing`; `omit Fact p.Prime`.
- Uses from project: []
- Used by: `phiSeries_zero`, `phiSeries_C_mul`, `map_phiSeries`, `one_add_mul_derivative_phiSeries`, `psiSeries_add`, `psiSeries_C_mul`, `seriesEval_phi_of_summable_prod`, `norm_coeff_phiSeries_le_one`, `norm_coeff_phiSeries_le_linear`, `phiSeries_formalLog`
- Visibility: public
- Lines: 40-45 (proof 1 line)
- Notes: none

### lemma phiSeries_zero
- Type: `@[simp] lemma phiSeries_zero : phiSeries p (0 : PowerSeries R) = 0`
- What: `φ` sends the zero series to zero.
- How: Rewrite through `coe_substAlgHom` and `map_zero`.
- Hypotheses: `R` a `CommRing`; `omit Fact p.Prime`.
- Uses from project: [phiSeries, hasSubst_one_add_X_pow_sub_one]
- Used by: `psiSeries_phi`
- Visibility: public
- Lines: 47-50 (proof 1 line)
- Notes: none

### lemma constantCoeff_phiSeries
- Type: `@[simp] lemma constantCoeff_phiSeries (G : PowerSeries R) : constantCoeff (phiSeries p G) = constantCoeff G`
- What: `φ` preserves constant coefficients (the substituend has constant term `0`).
- How: `coeff_subst'` expands `φ` as a `finsum` over powers of the substituend; `finsum_eq_single 0` kills all but the `n=0` term because `X^n ∣ S^n` makes `coeff 0 (S^n) = 0` for `n>0` (`X_pow_dvd_iff`).
- Hypotheses: `R` a `CommRing`; `omit Fact p.Prime`.
- Uses from project: [phiSeries, hasSubst_one_add_X_pow_sub_one]
- Used by: `phiSeries_formalLog`
- Visibility: public
- Lines: 52-66 (proof 11 lines)
- Notes: none

### lemma phiSeries_C_mul
- Type: `lemma phiSeries_C_mul (a : R) (G : PowerSeries R) : phiSeries p (C a * G) = C a * phiSeries p G`
- What: `φ(C a · G) = C a · φ(G)` — substitution is a ring hom fixing constants.
- How: `subst_mul` distributes the substitution and `subst_C` fixes the constant factor.
- Hypotheses: `R` a `CommRing`; `omit Fact p.Prime`.
- Uses from project: [phiSeries, hasSubst_one_add_X_pow_sub_one]
- Used by: unused in file
- Visibility: public
- Lines: 68-74 (proof 3 lines)
- Notes: none

### def IsDigitDecomp
- Type: `def IsDigitDecomp (F : PowerSeries R) (G : Fin p → PowerSeries R) : Prop`
- What: Predicate that `G` is a family of `p` digits for `F` along `φ`: `F = Σ_{i<p} (1+T)^i·φ(G_i)`.
- How: Definitional equality.
- Hypotheses: `R` a `CommRing`.
- Uses from project: [phiSeries]
- Used by: `psiSeries`, `psiSeries_eq_of_unique`, `isDigitDecomp_map`, `existsUnique_digits`, `psiSeries_eq_of_isDigitDecomp`, `psiSeries_phi`, `psiSeries_add`, `psiSeries_C_mul`, `psiSeries_map`, `mahlerTransform_psi`
- Visibility: public
- Lines: 76-79 (def, no proof)
- Notes: none

### def psiSeries
- Type: `noncomputable def psiSeries (F : PowerSeries R) : PowerSeries R`
- What: The formal trace operator `ψ` — the `0`-th digit of the unique digit decomposition (when it exists), junk-totalised to `0` otherwise.
- How: `Classical` `if`-`then` on `∃! G, IsDigitDecomp p F G`, returning `h.exists.choose 0`.
- Hypotheses: `R` a `CommRing`.
- Uses from project: [IsDigitDecomp]
- Used by: `psiSeries_eq_of_unique`, `psiSeries_eq_of_isDigitDecomp`, `psiSeries_phi`, `psiSeries_C`, `psiSeries_add`, `psiSeries_C_mul`, `psiSeries_map`, `mahlerTransform_psi`
- Visibility: public
- Lines: 96-99 (def, no proof)
- Notes: none; long docstring documents replan R6 W6b-b1' statement defect (FALSE over fields where `p` invertible).

### theorem psiSeries_eq_of_unique
- Type: `theorem psiSeries_eq_of_unique (hex : ∃! G, IsDigitDecomp p F G) (hG : IsDigitDecomp p F G) : psiSeries p F = G 0`
- What: Whenever `F` has a unique digit decomposition, `psiSeries` equals its `0`-th digit (general `CommRing` form).
- How: Unfold `psiSeries`, take the `dif_pos` branch, then `hex.unique` identifies `choose` with the given `G`.
- Hypotheses: `R` a `CommRing`; `F` has a unique digit decomposition; `G` is a digit decomposition.
- Uses from project: [psiSeries, IsDigitDecomp]
- Used by: `psiSeries_eq_of_isDigitDecomp`, `psiSeries_map`
- Visibility: public
- Lines: 101-108 (proof 1 line)
- Notes: none

### lemma map_phiSeries
- Type: `lemma map_phiSeries (f : R →+* S) (G : PowerSeries R) : map f (phiSeries p G) = phiSeries p (map f G)`
- What: Coefficient maps commute with `φ` (the substituend `(1+T)^p − 1` is fixed by `map f`).
- How: `coeff_subst'` on both sides; truncate the two `finsum`s to `Finset.range (n+1)` using `X^d ∣ S^d` vanishing (`X_pow_dvd_iff`, `hvanishR`/`hvanishS`); then `coeff_map` and `hcoeffB` push `f` through each binomial coefficient termwise.
- Hypotheses: `R, S` `CommRing`s; `f` a ring hom; `omit Fact p.Prime`.
- Uses from project: [phiSeries, hasSubst_one_add_X_pow_sub_one]
- Used by: `isDigitDecomp_map`, `mahlerK_phi`, `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 110-148 (proof 29 lines)
- Notes: none

### lemma isDigitDecomp_map
- Type: `lemma isDigitDecomp_map (f : R →+* S) (hG : IsDigitDecomp p F G) : IsDigitDecomp p (map f F) (fun i => map f (G i))`
- What: A coefficient map `f` sends a digit decomposition of `F` to one of `map f F`.
- How: Unfold `IsDigitDecomp`, `map_sum`, then termwise `map_mul`/`map_pow` and `map_phiSeries`.
- Hypotheses: `R, S` `CommRing`s; `f` ring hom; `hG` a digit decomposition; `omit Fact p.Prime`.
- Uses from project: [IsDigitDecomp, map_phiSeries]
- Used by: `psiSeries_map`
- Visibility: public
- Lines: 150-157 (proof 3 lines)
- Notes: none

### theorem one_add_mul_derivative_phiSeries
- Type: `theorem one_add_mul_derivative_phiSeries (F) : (1+X)·derivativeFun (phiSeries p F) = (p:R) • phiSeries p ((1+X)·derivativeFun F)`
- What: The commutation `∂φ = p·φ∂` for the operator `∂ = (1+T)d/dT`.
- How: Chain rule `derivative_subst` gives `d(F∘S) = (dF∘S)·dS`; compute `dS = p·(1+X)^{p−1}` (`Derivation.leibniz_pow`); rewrite `1+S = (1+X)^p` and `(1+X)·(1+X)^{p−1} = (1+X)^p` (`pow_succ'`, `Nat.sub_add_cancel`); reassemble.
- Hypotheses: `R` a `CommRing`; uses `hp.out.one_le`.
- Uses from project: [phiSeries, hasSubst_one_add_X_pow_sub_one]
- Used by: `phiSeries_formalLog`
- Visibility: public
- Lines: 159-186 (proof 20 lines)
- Notes: none

### lemma dirac_mul_eq_pushforward
- Type: `lemma dirac_mul_eq_pushforward (a : ℤ_[p]) (μ : MeasureR K ℤ_[p]) : dirac K ℤ_[p] a * μ = pushforward K ℤ_[p] ℤ_[p] ⟨fun y => a + y, _⟩ μ`
- What: Convolution of a measure by a Dirac `δ_a` is the pushforward along addition `y ↦ a+y`.
- How: `LinearMap.ext`, then unfold both sides via `mul_apply`, `dirac_apply`, `convInner_apply`, `pushforward_apply`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [] (only MeasureR API: dirac, pushforward, mul_apply, dirac_apply, convInner_apply, pushforward_apply)
- Used by: `existsUnique_measure_digits`
- Visibility: public
- Lines: 197-203 (proof 1 line)
- Notes: none

### theorem mahlerTransform_phi
- Type: `theorem mahlerTransform_phi (μ : MeasureR K ℤ_[p]) : mahlerTransform p K (MeasureR.phi p K μ) = phiSeries p (mahlerTransform p K μ)`
- What: The Mahler transform intertwines the measure operator `phi` and the series operator `phiSeries` (R-level Eq. (3.9)).
- How: Compute the `n`-th coefficient. Key fact `mahler n (p·k) = Σ_d coeff_n(S^d)·C(k,d)` via `mahler_natCast_eq`, `binomialSeries_nat`, `Ring.choose_natCast`; then build `(mahlerCM n).comp(mulCM p) = Σ_d coeff_n(B^d)•mahlerCM d` on the dense set of `natCast`s (`denseRange_natCast.equalizer`); finally apply `μ` and read off via `coeff_mahlerTransform`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit CompleteSpace`.
- Uses from project: [phiSeries] (plus MeasureR: mahlerTransform, MeasureR.phi, coeff_mahlerTransform, mahlerCM, mahlerCM_apply, mulCM)
- Used by: `mahlerTransform_sum_dirac_mul_phi`, `mahlerK_phi`
- Visibility: public
- Lines: 205-278 (proof 66 lines)
- Notes: OVER-50 (needs /decompose-proof)

### lemma mahlerTransform_dirac_natCast
- Type: `lemma mahlerTransform_dirac_natCast (i : ℕ) : mahlerTransform p K (dirac K ℤ_[p] (i:ℤ_[p])) = (1+X)^i`
- What: The Mahler transform of `δ_i` is `(1+T)^i`.
- How: `mahlerTransform_dirac` then `binomialSeries_nat` and `map_pow`/`map_add`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit CompleteSpace`.
- Uses from project: [] (MeasureR: mahlerTransform, mahlerTransform_dirac, dirac)
- Used by: `mahlerTransform_sum_dirac_mul_phi`
- Visibility: public
- Lines: 280-286 (proof 2 lines)
- Notes: none

### lemma psi_dirac_mul_phi_eq_zero
- Type: `lemma psi_dirac_mul_phi_eq_zero (ha : ‖a‖ = 1) (ν) : MeasureR.psi p K (dirac K ℤ_[p] a * MeasureR.phi p K ν) = 0`
- What: A unit-translate of a `φ`-image is supported off `pℤ_p`, hence killed by `ψ`.
- How: Unfold `ψ` against the test function (`charFnCM · * f∘shiftDiv`); reduce to showing the composed continuous map is `0` pointwise; the ultrametric inequality `‖a‖ ≤ max(‖a+pz‖, ‖pz‖)` (`IsUltrametricDist.norm_add_le_max`) with `‖a‖=1`, `‖pz‖<1` (`mem_pZp_of_mul`) forces `a + pz ∉ {‖·‖<1}`, so the indicator vanishes.
- Hypotheses: `‖a‖ = 1`; `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [] (MeasureR: psi, dirac, phi, charFnCM, shiftDiv, isClopen_pZp, mulCM, mem_pZp_of_mul)
- Used by: `psi_dirac_neg_mul_sum`
- Visibility: public
- Lines: 288-319 (proof 28 lines)
- Notes: none

### lemma norm_natCast_sub_natCast_eq_one
- Type: `lemma norm_natCast_sub_natCast_eq_one (hi : i < p) (hj : j < p) (hij : i ≠ j) : ‖(i:ℤ_[p]) − (j:ℤ_[p])‖ = 1`
- What: For distinct digits `i, j < p`, `‖i − j‖ = 1` in `ℤ_[p]`.
- How: Auxiliary `hkey`: `‖m‖ = 1` for `0 < m < p` via `norm_natCast_eq_one_iff` and `coprime_iff_not_dvd`; split on `j ≤ i` vs `i ≤ j`, rewrite the difference as `±(|i−j|:ℤ_[p])` and apply `hkey`.
- Hypotheses: `i, j < p` and `i ≠ j`.
- Uses from project: []
- Used by: `psi_dirac_neg_mul_sum`
- Visibility: public
- Lines: 321-337 (proof 13 lines)
- Notes: none

### lemma sum_charFn_pZp_sub_natCast
- Type: `lemma sum_charFn_pZp_sub_natCast (y : ℤ_[p]) : ∑ i : Fin p, charFnCM K ℤ_[p] (isClopen_pZp p) (y − (i:ℤ_[p])) = 1`
- What: Residue-partition identity `ℤ_p = ⊔_{i<p}(i+pℤ_p)`: exactly one digit shares `y`'s residue, so the indicator sum is `1`.
- How: Let `c` be the residue of `y` mod `p` (`toZModPow 1`); prove `y − i ∈ {‖·‖<1} ↔ i = c` via `norm_lt_one_iff_dvd`, `ker_toZModPow`, `val_natCast_of_lt`; rewrite each indicator as `if i=c then 1 else 0`, then `Finset.sum_ite_eq'`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit NormedAlgebra ℚ_[p] K, CompleteSpace`.
- Uses from project: [] (MeasureR: charFnCM, isClopen_pZp)
- Used by: `existsUnique_measure_digits`
- Visibility: public
- Lines: 339-376 (proof 31 lines)
- Notes: long(30-50)

### lemma psi_dirac_neg_mul_sum
- Type: `lemma psi_dirac_neg_mul_sum (ν : Fin p → MeasureR K ℤ_[p]) (j : Fin p) : MeasureR.psi p K (dirac K ℤ_[p] (-(j:ℤ_[p])) * Σ_i dirac K ℤ_[p] (i:ℤ_[p]) * MeasureR.phi p K (ν i)) = ν j`
- What: Digit extraction: applying `ψ(δ_{−j} · −)` to the full digit sum recovers `ν_j`.
- How: Distribute `Finset.mul_sum`, `MeasureR.psi_sum`, isolate the single `i=j` term (`Finset.sum_eq_single`); `i=j` gives `ψφ = id` via `dirac_mul_dirac`, `neg_add_cancel`, `MeasureR.psi_phi`; off-diagonal terms vanish by `psi_dirac_mul_phi_eq_zero` using `norm_natCast_sub_natCast_eq_one`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [psi_dirac_mul_phi_eq_zero, norm_natCast_sub_natCast_eq_one] (MeasureR: psi, psi_sum, dirac, phi, dirac_mul_dirac, one_def, psi_phi)
- Used by: `existsUnique_measure_digits`, `mahlerTransform_psi`, `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 378-393 (proof 10 lines)
- Notes: none

### theorem existsUnique_measure_digits
- Type: `theorem existsUnique_measure_digits (μ : MeasureR K ℤ_[p]) : ∃! ν : Fin p → MeasureR K ℤ_[p], μ = Σ_i dirac K ℤ_[p] (i:ℤ_[p]) * MeasureR.phi p K (ν i)`
- What: Every measure has a unique `p`-residue digit decomposition `μ = Σ_{i<p} δ_i·φ(ν_i)`.
- How: Candidate `ν_j := ψ(δ_{−j}·μ)`. Existence: `phi_psi`, `dirac_mul_eq_pushforward`, `MeasureR.res`/`cmul` reduce the `i`-th term to `μ(hfun i)`; summing the indicators over `i` gives `1` by `sum_charFn_pZp_sub_natCast`, recovering `μ`. Uniqueness: any decomposing `ν` satisfies `ν j = psi_dirac_neg_mul_sum`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [dirac_mul_eq_pushforward, sum_charFn_pZp_sub_natCast, psi_dirac_neg_mul_sum] (MeasureR: psi, phi, phi_psi, dirac, res, cmul, charFnCM, isClopen_pZp)
- Used by: `existsUnique_digits`, `mahlerTransform_psi`, `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 395-431 (proof 35 lines)
- Notes: long(30-50)

### lemma mahlerTransform_sum (private)
- Type: `private lemma mahlerTransform_sum (s : Finset ι) (m : ι → MeasureR K ℤ_[p]) : mahlerTransform p K (∑ i ∈ s, m i) = ∑ i ∈ s, mahlerTransform p K (m i)`
- What: The Mahler transform is additive over finite sums of measures.
- How: `map_sum` of the linear map `mahlerTransformₗ`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit CompleteSpace`.
- Uses from project: [] (MeasureR: mahlerTransform, mahlerTransformₗ)
- Used by: `mahlerTransform_sum_dirac_mul_phi`
- Visibility: private
- Lines: 433-437 (proof 1 line)
- Notes: none

### lemma mahlerTransform_sum_dirac_mul_phi
- Type: `lemma mahlerTransform_sum_dirac_mul_phi (ν : Fin p → MeasureR K ℤ_[p]) : mahlerTransform p K (Σ_i dirac K ℤ_[p] (i:ℤ_[p]) * MeasureR.phi p K (ν i)) = Σ_i (1+X)^i · phiSeries p (mahlerTransform p K (ν i))`
- What: The Mahler transform intertwines the measure-level and series-level digit decompositions.
- How: `mahlerTransform_sum`, then termwise `mahlerTransform_mul`, `mahlerTransform_dirac_natCast`, `mahlerTransform_phi`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [phiSeries, mahlerTransform_sum, mahlerTransform_dirac_natCast, mahlerTransform_phi] (MeasureR: mahlerTransform, dirac, phi, mahlerTransform_mul)
- Used by: `existsUnique_digits`, `mahlerTransform_psi`, `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 439-448 (proof 3 lines)
- Notes: none

### theorem existsUnique_digits
- Type: `theorem existsUnique_digits (F : PowerSeries (integerRing K)) : ∃! G : Fin p → PowerSeries (integerRing K), IsDigitDecomp p F G`
- What: W6b-b1: over the integral ring `integerRing K`, every series has a unique digit decomposition (the general-`CommRing` form is false).
- How: Transport `existsUnique_measure_digits` for `ofPowerSeries p K F` through `mahlerTransform`: existence via `mahlerTransform_sum_dirac_mul_phi` + `mahlerTransform_ofPowerSeries`; uniqueness via `mahlerTransform_injective` and the measure-level uniqueness `hνuniq`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [IsDigitDecomp, phiSeries, existsUnique_measure_digits, mahlerTransform_sum_dirac_mul_phi] (MeasureR: ofPowerSeries, mahlerTransform, mahlerTransform_ofPowerSeries, mahlerTransform_injective, phi, dirac)
- Used by: `psiSeries_eq_of_isDigitDecomp`, `psiSeries_add`, `psiSeries_C_mul`, `psiSeries_map`
- Visibility: public
- Lines: 450-471 (proof 18 lines)
- Notes: none

### theorem psiSeries_eq_of_isDigitDecomp
- Type: `theorem psiSeries_eq_of_isDigitDecomp (hG : IsDigitDecomp p F G) : psiSeries p F = G 0`
- What: Over `integerRing K`, `psiSeries` is the `0`-th digit of *any* digit decomposition (all agree by uniqueness).
- How: `psiSeries_eq_of_unique` with the uniqueness witness `existsUnique_digits`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete; `hG` a digit decomposition over `integerRing K`.
- Uses from project: [IsDigitDecomp, psiSeries, psiSeries_eq_of_unique, existsUnique_digits]
- Used by: `psiSeries_phi`, `psiSeries_add`, `psiSeries_C_mul`, `mahlerTransform_psi`
- Visibility: public
- Lines: 473-478 (proof 1 line)
- Notes: none

### theorem psiSeries_phi
- Type: `theorem psiSeries_phi (G : PowerSeries (integerRing K)) : psiSeries p (phiSeries p G) = G`
- What: `ψ∘φ = id` on `integerRing K`: the digit family of `φG` is `(G,0,…,0)`.
- How: Apply `psiSeries_eq_of_isDigitDecomp` to the digit family `i ↦ if i=0 then G else 0`; `Finset.sum_eq_single 0` with `phiSeries_zero` collapses all off-diagonal terms.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [psiSeries, phiSeries, psiSeries_eq_of_isDigitDecomp, phiSeries_zero]
- Used by: `psiSeries_C`
- Visibility: public
- Lines: 480-491 (proof 6 lines)
- Notes: none

### lemma phiSeries_C
- Type: `lemma phiSeries_C (a : integerRing K) : phiSeries p (C a) = C a`
- What: `φ` fixes constant series `C a`.
- How: Unfold `phiSeries`, apply `subst_C`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit Fact p.Prime, CompleteSpace`.
- Uses from project: [phiSeries]
- Used by: `psiSeries_C`
- Visibility: public
- Lines: 493-497 (proof 1 line)
- Notes: none

### theorem psiSeries_C
- Type: `@[simp] theorem psiSeries_C (a : integerRing K) : psiSeries p (C a) = C a`
- What: `ψ` fixes constant series `C a`.
- How: Rewrite `C a = φ(C a)` via `phiSeries_C`, then `psiSeries_phi`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [psiSeries, phiSeries_C, psiSeries_phi]
- Used by: unused in file
- Visibility: public
- Lines: 499-503 (proof 2 lines)
- Notes: none

### theorem psiSeries_add
- Type: `theorem psiSeries_add (F G : PowerSeries (integerRing K)) : psiSeries p (F + G) = psiSeries p F + psiSeries p G`
- What: `ψ` is additive over `integerRing K`.
- How: Take digit decompositions `GF, GG` (`existsUnique_digits`); their pointwise sum `GF i + GG i` is a digit decomposition of `F+G` (via `subst_add`), so `psiSeries_eq_of_isDigitDecomp` gives the result.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [psiSeries, phiSeries, hasSubst_one_add_X_pow_sub_one, existsUnique_digits, psiSeries_eq_of_isDigitDecomp]
- Used by: unused in file
- Visibility: public
- Lines: 505-516 (proof 11 lines)
- Notes: none

### theorem psiSeries_C_mul
- Type: `theorem psiSeries_C_mul (a : integerRing K) (F) : psiSeries p (C a * F) = C a * psiSeries p F`
- What: `ψ` is `C a`-linear over `integerRing K`.
- How: Digit decomposition `GF` of `F`; the scaled family `C a · GF i` decomposes `C a · F` (via `subst_mul`, `subst_C`, `ring`); apply `psiSeries_eq_of_isDigitDecomp`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [psiSeries, phiSeries, hasSubst_one_add_X_pow_sub_one, existsUnique_digits, psiSeries_eq_of_isDigitDecomp]
- Used by: unused in file
- Visibility: public
- Lines: 518-532 (proof 14 lines)
- Notes: none

### theorem psiSeries_map
- Type: `theorem psiSeries_map (f : integerRing K →+* S) (F) (hS : ∃! G, IsDigitDecomp p (map f F) G) : psiSeries p (map f F) = map f (psiSeries p F)`
- What: W6b-b8: `ψ` commutes with coefficient maps out of `integerRing K`, on the locus where the image again has a unique digit decomposition.
- How: Digit decomposition `GF` of `F`; `isDigitDecomp_map` transports it under `f`; combine `psiSeries_eq_of_isDigitDecomp` (source) and `psiSeries_eq_of_unique hS` (target).
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete; `S` `CommRing`; `f` ring hom; `hS` uniqueness of the image decomposition.
- Uses from project: [psiSeries, IsDigitDecomp, existsUnique_digits, psiSeries_eq_of_isDigitDecomp, psiSeries_eq_of_unique, isDigitDecomp_map]
- Used by: unused in file
- Visibility: public
- Lines: 534-546 (proof 2 lines)
- Notes: none

### theorem mahlerTransform_psi
- Type: `theorem mahlerTransform_psi (μ : MeasureR K ℤ_[p]) : mahlerTransform p K (MeasureR.psi p K μ) = psiSeries p (mahlerTransform p K μ)`
- What: W6b-b4: the formal `ψ` is the series-side of the measure-level `ψ` through the Mahler transform.
- How: Digit decomposition `ν` of `μ`; identify `ν 0 = MeasureR.psi p K μ` via `psi_dirac_neg_mul_sum` at `j=0`; show `i ↦ mahlerTransform (ν i)` is a digit decomposition of `mahlerTransform μ` (via `mahlerTransform_sum_dirac_mul_phi`); apply `psiSeries_eq_of_isDigitDecomp`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [psiSeries, IsDigitDecomp, existsUnique_measure_digits, psi_dirac_neg_mul_sum, mahlerTransform_sum_dirac_mul_phi, psiSeries_eq_of_isDigitDecomp] (MeasureR: mahlerTransform, psi, one_def)
- Used by: unused in file
- Visibility: public
- Lines: 555-571 (proof 12 lines)
- Notes: none

### def seriesEval
- Type: `noncomputable def seriesEval (F : PowerSeries K) (z : K) : K`
- What: Junk-total evaluation of a `K`-coefficient power series, `Σ' coeff_n(F)·z^n` (meaningful when summable).
- How: Definitional `tsum`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete (section `bridge`, `{K}` implicit).
- Uses from project: []
- Used by: `seriesEval_zero_arg`, `seriesEval_add`, `seriesEval_neg`, `seriesEval_sub`, `seriesEval_C`, `seriesEval_C_mul`, `seriesEval_phi_of_summable_prod`, `seriesEval_mul`, `seriesEval_one_add_X_pow`, `seriesEval_phi_at_root`, `seriesEval_phi_at_root_of_summable`, `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 575-578 (def, no proof)
- Notes: none

### theorem seriesEval_zero_arg
- Type: `@[simp] theorem seriesEval_zero_arg (F) : seriesEval F (0:K) = constantCoeff F`
- What: Evaluating at `z=0` returns the constant coefficient.
- How: `tsum_eq_single 0` (all `n>0` terms have `0^n=0`), `pow_zero`, `coeff_zero_eq_constantCoeff`.
- Hypotheses: `K` normed field over `ℚ_[p]`; `omit IsUltrametricDist, CompleteSpace`.
- Uses from project: [seriesEval]
- Used by: unused in file
- Visibility: public
- Lines: 580-585 (proof 1 line)
- Notes: none

### theorem seriesEval_add
- Type: `theorem seriesEval_add (hF : Summable …) (hH : Summable …) : seriesEval (F+H) z = seriesEval F z + seriesEval H z`
- What: `seriesEval` is additive on series whose evaluations converge.
- How: `Summable.tsum_add`, then termwise `map_add`/`add_mul`.
- Hypotheses: both evaluation families summable; `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: [seriesEval]
- Used by: `seriesEval_sub`
- Visibility: public
- Lines: 587-594 (proof 2 lines)
- Notes: none

### theorem seriesEval_neg
- Type: `theorem seriesEval_neg (F) (z) : seriesEval (-F) z = -seriesEval F z`
- What: `seriesEval` commutes with negation.
- How: `tsum_neg`, then termwise `map_neg`/`neg_mul`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: [seriesEval]
- Used by: `seriesEval_sub`
- Visibility: public
- Lines: 596-601 (proof 2 lines)
- Notes: none

### theorem seriesEval_sub
- Type: `theorem seriesEval_sub (hF : Summable …) (hH : Summable …) : seriesEval (F−H) z = seriesEval F z − seriesEval H z`
- What: `seriesEval` is subtractive on series whose evaluations converge.
- How: `sub_eq_add_neg`, then `seriesEval_add` and `seriesEval_neg`.
- Hypotheses: both evaluation families summable; `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: [seriesEval_add, seriesEval_neg]
- Used by: unused in file
- Visibility: public
- Lines: 603-610 (proof 2 lines)
- Notes: none

### theorem seriesEval_C
- Type: `@[simp] theorem seriesEval_C (a z : K) : seriesEval (C a) z = a`
- What: Evaluating a constant series `C a` gives `a`.
- How: `tsum_eq_single 0` (`coeff_C` zero off `0`), `pow_zero`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: [seriesEval]
- Used by: unused in file
- Visibility: public
- Lines: 612-617 (proof 1 line)
- Notes: none

### theorem seriesEval_C_mul
- Type: `theorem seriesEval_C_mul (a) (F) (z) : seriesEval (C a * F) z = a * seriesEval F z`
- What: `seriesEval` is `a`-linear: scaling by a constant series scales the value.
- How: `tsum_mul_left`, then termwise `coeff_C_mul`/`mul_assoc`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: [seriesEval]
- Used by: unused in file
- Visibility: public
- Lines: 619-624 (proof 2 lines)
- Notes: none

### instance NonarchimedeanRing K
- Type: `instance : NonarchimedeanRing K`
- What: An ultrametric normed field is a nonarchimedean ring (ring upgrade of the nonarchimedean additive group).
- How: Bundle `IsTopologicalRing` (inferred) with `NonarchimedeanAddGroup.is_nonarchimedean`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: []
- Used by: unused in file (provides instance for summability lemmas via typeclass resolution)
- Visibility: public (instance)
- Lines: 626-630 (instance, no real proof)
- Notes: none

### theorem coeff_substSeries_pow_eq_zero
- Type: `theorem coeff_substSeries_pow_eq_zero (hkn : k < n) : coeff k (((1+X)^p − 1)^n) = 0`
- What: `(1+X)^p − 1` powers vanish below degree `n`: `coeff k(S^n) = 0` for `k < n`.
- How: `X^n ∣ S^n` (constant coefficient `0`), then `X_pow_dvd_iff`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: []
- Used by: `seriesEval_phi_of_summable_prod`, `summable_prod_of_norm_coeff_le_one`, `summable_prod_of_norm_coeff_le_linear`, `norm_coeff_phiSeries_le_one`, `norm_coeff_phiSeries_le_linear`
- Visibility: public
- Lines: 632-638 (proof 1 line)
- Notes: none

### theorem tsum_coeff_substSeries_pow
- Type: `theorem tsum_coeff_substSeries_pow (z : K) (n : ℕ) : (∑' k, coeff k (((1+X)^p − 1)^n)·z^k) = ((1+z)^p − 1)^n`
- What: The evaluation of the polynomial `S^n` at `z` equals `((1+z)^p − 1)^n` (`S^n` is a polynomial, so the `tsum` is finite).
- How: Identify `S^n` with the coerced polynomial `Sp^n` (`coeff_coe`); bound `natDegree(Sp^n) < p·n+1`; collapse the `tsum` to a finite `Finset.range` sum (`tsum_eq_sum`, `coeff_eq_zero_of_natDegree_lt`); then `Polynomial.eval_eq_sum_range'` and `eval_pow`/`eval_sub`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: []
- Used by: `seriesEval_phi_of_summable_prod`
- Visibility: public
- Lines: 640-668 (proof 23 lines)
- Notes: none

### theorem coeff_substSeries_pow_eq_zero_ge
- Type: `theorem coeff_substSeries_pow_eq_zero_ge (hkn : p * n < k) : coeff k (((1+X)^p − 1)^n) = 0`
- What: `(1+X)^p − 1` powers vanish above degree `p·n`: `coeff k(S^n) = 0` for `p·n < k`.
- How: Identify `S^n` with polynomial `Sp^n`; `natDegree(Sp^n) ≤ p·n < k`, then `coeff_eq_zero_of_natDegree_lt`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: []
- Used by: `summable_coeff_substSeries_pow`
- Visibility: public
- Lines: 670-689 (proof 16 lines)
- Notes: none

### theorem summable_coeff_substSeries_pow
- Type: `theorem summable_coeff_substSeries_pow (z : K) (n : ℕ) : Summable fun k => coeff k (((1+X)^p − 1)^n)·z^k`
- What: The single-series evaluation family of `S^n` is summable (finite support).
- How: `summable_of_ne_finset_zero` over `Finset.range (p·n+1)` using `coeff_substSeries_pow_eq_zero_ge`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: [coeff_substSeries_pow_eq_zero_ge]
- Used by: `seriesEval_phi_of_summable_prod`
- Visibility: public
- Lines: 691-698 (proof 2 lines)
- Notes: none

### theorem seriesEval_phi_of_summable_prod
- Type: `theorem seriesEval_phi_of_summable_prod (G) (z) (hprod : Summable …) : seriesEval (phiSeries p G) z = ∑' n, coeff n G · ((1+z)^p − 1)^n`
- What: The `K`-native evaluation bridge for `φ`: under summability of the `ℕ×ℕ` product family, `(φG)(z)` equals the evaluation of `G` at `(1+z)^p − 1`.
- How: Expand `coeff k (phiSeries G)` as a finite `Finset.range` sum (`coeff_subst'`, `coeff_substSeries_pow_eq_zero`); rewrite `seriesEval` as the iterated sum `∑'_k Σ_n T n k`, swap order (`Summable.tsum_comm hprod`), collapse the inner `tsum` via `summable_coeff_substSeries_pow` and `tsum_coeff_substSeries_pow`.
- Hypotheses: `hprod` product family summable; `omit Fact p.Prime, NormedAlgebra`.
- Uses from project: [seriesEval, phiSeries, hasSubst_one_add_X_pow_sub_one, coeff_substSeries_pow_eq_zero, summable_coeff_substSeries_pow, tsum_coeff_substSeries_pow]
- Used by: `seriesEval_phi_at_root`, `seriesEval_phi_at_root_of_summable`
- Visibility: public
- Lines: 700-744 (proof 34 lines)
- Notes: long(30-50)

### def mahlerK
- Type: `noncomputable def mahlerK (μ : MeasureR K ℤ_[p]) : PowerSeries K`
- What: The `K`-mapped Mahler transform — `map (integerRing K).subtype` of `mahlerTransform`, i.e. the integral Mahler transform with coefficients embedded into `K`.
- How: Definitional `PowerSeries.map subtype`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric, complete; `variable (K)`.
- Uses from project: [] (MeasureR: mahlerTransform)
- Used by: `mahlerK_sub`, `mahlerK_phi`, `norm_coeff_mahlerK_le_one`, `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 746-750 (def, no proof)
- Notes: none

### theorem mahlerK_sub
- Type: `theorem mahlerK_sub (μ ν) : mahlerK p K (μ − ν) = mahlerK p K μ − mahlerK p K ν`
- What: `mahlerK` is additive on differences of measures.
- How: `MeasureR.mahlerTransform_sub` then `map_sub`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit CompleteSpace`.
- Uses from project: [mahlerK] (MeasureR: mahlerTransform_sub)
- Used by: unused in file
- Visibility: public
- Lines: 752-756 (proof 1 line)
- Notes: none

### theorem mahlerK_phi
- Type: `theorem mahlerK_phi (μ) : mahlerK p K (MeasureR.phi p K μ) = phiSeries p (mahlerK p K μ)`
- What: The `K`-level `φ`-transport: `𝓐_{φμ}^K = phiSeries 𝓐_μ^K`.
- How: Map the integral `mahlerTransform_phi` through the `subtype` coefficient map, commuting via `map_phiSeries`.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit CompleteSpace`.
- Uses from project: [mahlerK, phiSeries, mahlerTransform_phi, map_phiSeries] (MeasureR: phi)
- Used by: unused in file
- Visibility: public
- Lines: 758-763 (proof 1 line)
- Notes: none

### theorem norm_coeff_mahlerK_le_one
- Type: `theorem norm_coeff_mahlerK_le_one (μ) (n) : ‖coeff n (mahlerK p K μ)‖ ≤ 1`
- What: The `K`-mapped Mahler coefficients are integral (norm `≤ 1`).
- How: `coeff_map` reduces to the norm bound `.2` carried by the `integerRing K` element.
- Hypotheses: `K` normed field over `ℚ_[p]`, ultrametric; `omit CompleteSpace`.
- Uses from project: [mahlerK] (MeasureR: mahlerTransform)
- Used by: unused in file
- Visibility: public
- Lines: 765-770 (proof 2 lines)
- Notes: none

### theorem norm_coeff_substSeries_pow_le_one
- Type: `theorem norm_coeff_substSeries_pow_le_one (k n : ℕ) : ‖coeff k (((1+X)^p − 1)^n)‖ ≤ 1`
- What: The coefficients of `(1+X)^p − 1` powers are integral (`ℤ`-combinations of binomials, norm `≤ 1`).
- How: Realise `S^n` as `map (Int.castRingHom K)` of the `ℤ`-coefficient `S^n`; `coeff_map` then `IsUltrametricDist.norm_intCast_le_one`.
- Hypotheses: `omit Fact p.Prime, NormedAlgebra, CompleteSpace`.
- Uses from project: []
- Used by: `summable_prod_of_norm_coeff_le_one`, `summable_prod_of_norm_coeff_le_linear`, `norm_coeff_phiSeries_le_one`, `norm_coeff_phiSeries_le_linear`
- Visibility: public
- Lines: 772-782 (proof 3 lines)
- Notes: none

### theorem tendsto_natCast_succ_mul_pow (private)
- Type: `private theorem tendsto_natCast_succ_mul_pow (hr0 : 0 ≤ r) (hr1 : r < 1) : Tendsto (fun n => ((n:ℝ)+1)·r^n) atTop (nhds 0)`
- What: `(n+1)·r^n → 0` for `0 ≤ r < 1` (the real geometric-with-linear decay used for polynomial-growth summability).
- How: Split `((n+1))·r^n = n·r^n + r^n`; both `tendsto_self_mul_const_pow_of_lt_one` and `tendsto_pow_atTop_nhds_zero_of_lt_one` go to `0`, sum them.
- Hypotheses: `0 ≤ r < 1` real; `omit Fact p.Prime, NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: []
- Used by: `summable_prod_of_norm_coeff_le_linear`, `summable_seriesEval_of_norm_coeff_le_linear`
- Visibility: private
- Lines: 784-789 (proof 3 lines)
- Notes: none

### theorem summable_prod_of_norm_coeff_le_one
- Type: `theorem summable_prod_of_norm_coeff_le_one (hG : ∀ n, ‖coeff n G‖ ≤ 1) (hz : ‖z‖ < 1) : Summable fun nk : ℕ×ℕ => coeff nk.1 G · coeff nk.2 (S^nk.1) · z^nk.2`
- What: For `‖·‖ ≤ 1`-coefficient `G` and `‖z‖ < 1`, the total `ℕ×ℕ` family of `φ`-evaluation terms is summable.
- How: Nonarchimedean `summable_iff_tendsto_cofinite_zero` + `tendsto_nhds_zero`; bound each term `‖T nk‖ ≤ ‖z‖^{nk.2}` (`norm_coeff_substSeries_pow_le_one`); use `tendsto_pow_atTop_nhds_zero_of_lt_one` to get `N` and confine the complement of the `ε`-bound to a finite box `Iio(N+1)×Iio(N+1)` (terms with `nk.2 < nk.1` vanish, others are small).
- Hypotheses: `‖coeff n G‖ ≤ 1` all `n`; `‖z‖ < 1`; `omit Fact p.Prime, NormedAlgebra`.
- Uses from project: [coeff_substSeries_pow_eq_zero, norm_coeff_substSeries_pow_le_one]
- Used by: `seriesEval_phi_at_root`
- Visibility: public
- Lines: 791-833 (proof 33 lines)
- Notes: long(30-50)

### theorem summable_prod_of_norm_coeff_le_linear
- Type: `theorem summable_prod_of_norm_coeff_le_linear (hG : ∀ n, ‖coeff n G‖ ≤ C·(n+1)) (hz : ‖z‖ < 1) : Summable fun nk : ℕ×ℕ => coeff nk.1 G · coeff nk.2 (S^nk.1) · z^nk.2`
- What: Linear-growth variant: for `‖coeff n G‖ ≤ C·(n+1)`, the `φ`-evaluation product family is summable.
- How: As the `≤ 1` case but with bound `‖T nk‖ ≤ C·((nk.2+1)·‖z‖^{nk.2})` (via `gcongr`, using `nk.1 ≤ nk.2` on the support and `norm_coeff_substSeries_pow_le_one`); decay from `tendsto_natCast_succ_mul_pow`.
- Hypotheses: `‖coeff n G‖ ≤ C·(n+1)`; `‖z‖ < 1`; `omit Fact p.Prime, NormedAlgebra`.
- Uses from project: [coeff_substSeries_pow_eq_zero, norm_coeff_substSeries_pow_le_one, tendsto_natCast_succ_mul_pow]
- Used by: unused in file
- Visibility: public
- Lines: 835-877 (proof 33 lines)
- Notes: long(30-50)

### theorem seriesEval_phi_at_root
- Type: `theorem seriesEval_phi_at_root (hG : ∀ n, ‖coeff n G‖ ≤ 1) (hz : ‖z‖ < 1) (hzp : (1+z)^p = 1) : seriesEval (phiSeries p G) z = constantCoeff G`
- What: φ-collapse at a primitive `p`-th root: for `‖·‖ ≤ 1`-coefficient `G` and `(1+z)^p = 1`, `(φG)(z) = constantCoeff G`.
- How: `seriesEval_phi_of_summable_prod` (summability via `summable_prod_of_norm_coeff_le_one`), then `tsum_eq_single 0` because `(1+z)^p − 1 = 0` kills all `n>0` terms.
- Hypotheses: `‖coeff n G‖ ≤ 1`; `‖z‖ < 1`; `(1+z)^p = 1`; `omit Fact p.Prime, NormedAlgebra`.
- Uses from project: [seriesEval, phiSeries, seriesEval_phi_of_summable_prod, summable_prod_of_norm_coeff_le_one]
- Used by: `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 879-889 (proof 5 lines)
- Notes: none

### theorem seriesEval_phi_at_root_of_summable
- Type: `theorem seriesEval_phi_at_root_of_summable (hprod : Summable …) (hzp : (1+z)^p = 1) : seriesEval (phiSeries p G) z = constantCoeff G`
- What: Unbounded-coefficient variant of `seriesEval_phi_at_root`: same collapse but with summability supplied directly (for polynomial-growth series of the c₀-design).
- How: `seriesEval_phi_of_summable_prod` with the given `hprod`, then `tsum_eq_single 0` collapsing on `(1+z)^p − 1 = 0`.
- Hypotheses: `hprod` product family summable; `(1+z)^p = 1`; `omit Fact p.Prime, NormedAlgebra`.
- Uses from project: [seriesEval, phiSeries, seriesEval_phi_of_summable_prod]
- Used by: unused in file
- Visibility: public
- Lines: 891-908 (proof 4 lines)
- Notes: none

### theorem seriesEval_mul
- Type: `theorem seriesEval_mul (hF : Summable …) (hH : Summable …) : seriesEval (F·H) z = seriesEval F z · seriesEval H z`
- What: `seriesEval` is multiplicative on factors whose evaluations converge (nonarchimedean Cauchy product).
- How: `Summable.mul_of_nonarchimedean` gives the product family summable; `tsum_mul_tsum_eq_tsum_sum_antidiagonal` turns the product of `tsum`s into a `tsum` over antidiagonals; match the Cauchy product `coeff_mul` termwise splitting `z^j = z^{ab.1}·z^{ab.2}`.
- Hypotheses: both evaluation families summable; `omit NormedAlgebra, CompleteSpace`.
- Uses from project: [seriesEval]
- Used by: `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 910-928 (proof 9 lines)
- Notes: `set_option maxHeartbeats 1000000`

### theorem seriesEval_one_add_X_pow
- Type: `theorem seriesEval_one_add_X_pow (z) (i) : seriesEval ((1+X)^i) z = (1+z)^i`
- What: The polynomial series `(1+X)^i` evaluates to `(1+z)^i` (finite support).
- How: Coerce `(1+X)^i` from the polynomial `(1+Polynomial.X)^i`; bound `natDegree < i+1`; collapse `tsum` to a finite range sum (`coeff_coe`, `coeff_eq_zero_of_natDegree_lt`); `Polynomial.eval_eq_sum_range'`.
- Hypotheses: `omit NormedAlgebra, IsUltrametricDist, CompleteSpace`.
- Uses from project: [seriesEval]
- Used by: `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 930-948 (proof 13 lines)
- Notes: none

### theorem summable_seriesEval_of_norm_coeff_le_one
- Type: `theorem summable_seriesEval_of_norm_coeff_le_one (hF : ∀ n, ‖coeff n F‖ ≤ 1) (hz : ‖z‖ < 1) : Summable fun n => coeff n F · z^n`
- What: A `‖·‖ ≤ 1`-coefficient series evaluated at `‖z‖ < 1` is summable (terms `‖·‖ ≤ ‖z‖^n → 0`).
- How: Nonarchimedean `summable_iff_tendsto_cofinite_zero`; bound `‖coeff n F · z^n‖ ≤ ‖z‖^n` and use `tendsto_pow_atTop_nhds_zero_of_lt_one` to confine the complement to `Iio(N+1)`.
- Hypotheses: `‖coeff n F‖ ≤ 1`; `‖z‖ < 1`; `omit NormedAlgebra`.
- Uses from project: []
- Used by: `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 950-968 (proof 13 lines)
- Notes: none

### theorem summable_seriesEval_of_norm_coeff_le_linear
- Type: `theorem summable_seriesEval_of_norm_coeff_le_linear (hF : ∀ n, ‖coeff n F‖ ≤ C·(n+1)) (hz : ‖z‖ < 1) : Summable fun n => coeff n F · z^n`
- What: Linear-growth summability: `‖coeff n F‖ ≤ C·(n+1)` and `‖z‖ < 1` give a summable evaluation family (for the antiderivative series / `F̃`).
- How: Nonarchimedean `summable_iff_tendsto_cofinite_zero`; bound `‖coeff n F · z^n‖ ≤ C·((n+1)·‖z‖^n)` and use `tendsto_natCast_succ_mul_pow` for decay; confine complement to `Iio(N+1)`.
- Hypotheses: `‖coeff n F‖ ≤ C·(n+1)`; `‖z‖ < 1`; `omit NormedAlgebra`.
- Uses from project: [tendsto_natCast_succ_mul_pow]
- Used by: unused in file
- Visibility: public
- Lines: 970-995 (proof 16 lines)
- Notes: none

### theorem norm_coeff_phiSeries_le_one
- Type: `theorem norm_coeff_phiSeries_le_one (hG : ∀ n, ‖coeff n G‖ ≤ 1) (n) : ‖coeff n (phiSeries p G)‖ ≤ 1`
- What: `φ` preserves integral coefficients (`ℤ`-combination of `G`'s integral coefficients).
- How: Expand `coeff n (phiSeries G)` as a finite `Finset.range` sum; `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty` extracts one dominating summand; bound it by `‖coeff d G‖·‖coeff n(S^d)‖ ≤ 1·1` (`norm_coeff_substSeries_pow_le_one`, `mul_le_one₀`).
- Hypotheses: `‖coeff n G‖ ≤ 1`; `omit Fact p.Prime, NormedAlgebra, CompleteSpace`.
- Uses from project: [phiSeries, hasSubst_one_add_X_pow_sub_one, coeff_substSeries_pow_eq_zero, norm_coeff_substSeries_pow_le_one]
- Used by: `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 997-1015 (proof 15 lines)
- Notes: none

### theorem norm_coeff_phiSeries_le_linear
- Type: `theorem norm_coeff_phiSeries_le_linear (hC : 0 ≤ C) (hG : ∀ m, ‖coeff m G‖ ≤ C·(m+1)) (n) : ‖coeff n (phiSeries p G)‖ ≤ C·(n+1)`
- What: `φ` preserves linear coefficient bounds (support `m ≤ n` propagates `C·(m+1) ≤ C·(n+1)` through the ultrametric max).
- How: Expand to a finite sum; `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` reduces to a per-summand bound; on the support `d ≤ n` the bound `‖coeff d G‖·1 ≤ C·(d+1) ≤ C·(n+1)` (and `0` when `n < d`).
- Hypotheses: `0 ≤ C`; `‖coeff m G‖ ≤ C·(m+1)`; `omit Fact p.Prime, NormedAlgebra, CompleteSpace`.
- Uses from project: [phiSeries, hasSubst_one_add_X_pow_sub_one, coeff_substSeries_pow_eq_zero, norm_coeff_substSeries_pow_le_one]
- Used by: unused in file
- Visibility: public
- Lines: 1017-1044 (proof 24 lines)
- Notes: none

### theorem norm_coeff_one_add_X_pow_mul_le_one
- Type: `theorem norm_coeff_one_add_X_pow_mul_le_one (hH : ∀ n, ‖coeff n H‖ ≤ 1) (i n) : ‖coeff n ((1+X)^i · H)‖ ≤ 1`
- What: Multiplying by the integral polynomial `(1+X)^i` preserves integral coefficients.
- How: `coeff_mul` (Cauchy product); `exists_norm_finsetSum_le_of_nonempty` picks one summand; its factor `coeff ab.1 ((1+X)^i)` is a binomial coefficient of norm `≤ 1` (`coeff_one_add_X_pow`, `norm_natCast_le_one`), the other factor `≤ 1` by `hH`.
- Hypotheses: `‖coeff n H‖ ≤ 1`; `omit NormedAlgebra, CompleteSpace`.
- Uses from project: []
- Used by: `sum_seriesEval_mahlerK`
- Visibility: public
- Lines: 1046-1063 (proof 17 lines)
- Notes: none

### theorem sum_seriesEval_mahlerK
- Type: `theorem sum_seriesEval_mahlerK (hξ : IsPrimitiveRoot ξ p) (μ) : ∑ i : Fin p, seriesEval (mahlerK p K μ) (ξ^i − 1) = (p:K) · constantCoeff (mahlerK p K (MeasureR.psi p K μ))`
- What: W6b-b6' (realised `Eqphipsi` at `T=0`): with `ξ` a primitive `p`-th root of unity, `Σ_{i<p} 𝓐_μ(ξ^i − 1) = p·𝓐_{ψμ}(0)`.
- How: Digit decomposition `ν` of `μ`; `ν 0 = ψμ` (`psi_dirac_neg_mul_sum`); each `‖ξ^j − 1‖ < 1` via `IsPrimitiveRoot.norm_sub_one_lt`; evaluate the digit sum at `ξ^j − 1` using `seriesEval_mul`, `seriesEval_one_add_X_pow`, and `seriesEval_phi_at_root` (the `φ`-layer collapses to `c i = constantCoeff(mahlerK ν_i)`), giving `Σ_i ξ^{ji}·c_i`; swap sums and apply orthogonality `Σ_j ξ^{ji} = p·[i≡0]` (`geom_sum_eq_zero` off-diagonal, `IsPrimitiveRoot.pow_of_coprime`).
- Hypotheses: `ξ` a primitive `p`-th root of unity; `K` normed field over `ℚ_[p]`, ultrametric, complete.
- Uses from project: [seriesEval, mahlerK, phiSeries, existsUnique_measure_digits, psi_dirac_neg_mul_sum, mahlerTransform_sum_dirac_mul_phi, map_phiSeries, seriesEval_one_add_X_pow, seriesEval_mul, seriesEval_phi_at_root, summable_seriesEval_of_norm_coeff_le_one, norm_coeff_one_add_X_pow_mul_le_one, norm_coeff_phiSeries_le_one] (MeasureR: mahlerTransform, psi, one_def)
- Used by: unused in file
- Visibility: public
- Lines: 1065-1163 (proof 87 lines)
- Notes: OVER-50 (needs /decompose-proof)

### theorem exists_antideriv
- Type: `theorem exists_antideriv (B : PowerSeries K) : ∃ C, constantCoeff C = 0 ∧ (p:K) • ((1+X)·derivativeFun C) = B`
- What: The formal antiderivative over char-0 `K`: every series is `p·∂C` for some `C` vanishing at `0` (c₀-design existence half).
- How: Set `E := p⁻¹·(B·(1+X)⁻¹)` (`Ring.inverse`, `1+X` a unit by `isUnit_iff_constantCoeff`); define `C` by coefficient-wise division `coeff(n-1)(E)/n`; verify `constantCoeff C = 0` and `derivativeFun C = E` (`coeff_derivativeFun`, `div_mul_cancel₀`), then unwind `p • ((1+X)·E) = B` via `inverse_mul_cancel`.
- Hypotheses: `K` char-zero (from `charZero_of_qpAlgebra`); `omit IsUltrametricDist, CompleteSpace`.
- Uses from project: [] (uses charZero_of_qpAlgebra from project Toolbox)
- Used by: unused in file
- Visibility: public
- Lines: 1165-1190 (proof 18 lines)
- Notes: none

### theorem eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero
- Type: `theorem eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero (h : (1+X)·derivativeFun F = 0) : F = C (constantCoeff F)`
- What: W6b-b7: the kernel of `∂ = (1+T)d/dT` over char-0 `K` is the constants.
- How: `1+X` is a unit, so `derivativeFun F = 0` (`mul_right_eq_zero`); on `succ n`, `coeff_derivativeFun` gives `(n+1)·coeff_{n+1} F = 0` with `n+1 ≠ 0` in char 0, forcing higher coefficients to vanish.
- Hypotheses: `K` char-zero; `(1+X)·derivativeFun F = 0`; `omit IsUltrametricDist, CompleteSpace`; `include hp`.
- Uses from project: [] (charZero_of_qpAlgebra from Toolbox)
- Used by: `phiSeries_formalLog`
- Visibility: public
- Lines: 1192-1213 (proof 14 lines)
- Notes: none

### def formalLog
- Type: `noncomputable def formalLog (K : Type*) [NormedField K] : PowerSeries K`
- What: T618: the formal logarithm `Σ_{n≥1} (−1)^{n−1}·n⁻¹·X^n` over `K` (constant term `0`), the series-side of `padicLog (1 + ·)`.
- How: Definitional `PowerSeries.mk`.
- Hypotheses: `K` a `NormedField` (explicit argument).
- Uses from project: []
- Used by: `coeff_zero_formalLog`, `constantCoeff_formalLog`, `coeff_succ_formalLog`, `one_add_mul_derivative_formalLog`, `phiSeries_formalLog`
- Visibility: public
- Lines: 1215-1218 (def, no proof)
- Notes: none

### theorem coeff_zero_formalLog
- Type: `@[simp] theorem coeff_zero_formalLog : coeff 0 (formalLog K) = 0`
- What: The degree-`0` coefficient of `formalLog` is `0`.
- How: `coeff_mk`, `if_pos`.
- Hypotheses: `omit IsUltrametricDist, CompleteSpace`.
- Uses from project: [formalLog]
- Used by: `constantCoeff_formalLog`
- Visibility: public
- Lines: 1220-1223 (proof 1 line)
- Notes: none

### theorem constantCoeff_formalLog
- Type: `@[simp] theorem constantCoeff_formalLog : constantCoeff (formalLog K) = 0`
- What: The constant coefficient of `formalLog` is `0`.
- How: `coeff_zero_eq_constantCoeff` then `coeff_zero_formalLog`.
- Hypotheses: `omit IsUltrametricDist, CompleteSpace`.
- Uses from project: [formalLog, coeff_zero_formalLog]
- Used by: `phiSeries_formalLog`
- Visibility: public
- Lines: 1225-1228 (proof 1 line)
- Notes: none

### theorem coeff_succ_formalLog
- Type: `theorem coeff_succ_formalLog (n) : coeff (n+1) (formalLog K) = (−1:K)^n · ((n:K)+1)⁻¹`
- What: The degree-`(n+1)` coefficient of `formalLog` is `(−1)^n·(n+1)⁻¹`.
- How: `coeff_mk`, `if_neg`, `Nat.add_sub_cancel`, `Nat.cast_succ`.
- Hypotheses: `omit IsUltrametricDist, CompleteSpace`.
- Uses from project: [formalLog]
- Used by: `one_add_mul_derivative_formalLog`
- Visibility: public
- Lines: 1230-1234 (proof 2 lines)
- Notes: none

### theorem one_add_mul_derivative_formalLog
- Type: `theorem one_add_mul_derivative_formalLog : (1+X)·derivativeFun (formalLog K) = 1`
- What: T618: `(1+X)·∂(formalLog) = 1` over char-0 `K` — the formal identity `∂(log(1+X)) = 1/(1+X)`.
- How: `ext n`, split into the `X·∂` and `∂` parts (`add_mul`); case `n=0` directly; case `succ m` rewrite both coefficients via `coeff_succ_formalLog`, cancel the `(m+1)⁻¹` and `(m+2)⁻¹` factors (`inv_mul_cancel₀`), then `pow_succ`/`ring`.
- Hypotheses: `K` char-zero; `omit IsUltrametricDist, CompleteSpace`; `include hp`.
- Uses from project: [formalLog, coeff_succ_formalLog] (charZero_of_qpAlgebra from Toolbox)
- Used by: `phiSeries_formalLog`
- Visibility: public
- Lines: 1236-1261 (proof 22 lines)
- Notes: none

### theorem phiSeries_formalLog
- Type: `theorem phiSeries_formalLog : phiSeries p (formalLog K) = (p:K) • formalLog K`
- What: T618: `phiSeries p formalLog = p·formalLog` over char-0 `K`.
- How: Both `phiSeries(formalLog)` and `p•formalLog` solve `(1+X)·∂(·) = p•1`: LHS via `one_add_mul_derivative_phiSeries` + `one_add_mul_derivative_formalLog`; RHS via `derivativeFun_smul`. Their difference is in the kernel of `∂` (`eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero`) with constant coefficient `0`, hence zero.
- Hypotheses: `K` char-zero; `omit IsUltrametricDist, CompleteSpace`; `include hp`.
- Uses from project: [phiSeries, formalLog, one_add_mul_derivative_phiSeries, one_add_mul_derivative_formalLog, eq_C_constantCoeff_of_one_add_mul_derivative_eq_zero, constantCoeff_phiSeries, constantCoeff_formalLog] (charZero_of_qpAlgebra from Toolbox)
- Used by: unused in file
- Visibility: public
- Lines: 1263-1290 (proof 22 lines)
- Notes: none

---

## File Summary

Total declarations: 56 (10 defs / 45 lemmas+theorems / 1 instance).
- defs (10): `phiSeries`, `IsDigitDecomp`, `psiSeries`, `seriesEval`, `mahlerK`, `formalLog` (6 noncomputable/structural defs) plus 4 more counted below — recount: actual defs = `phiSeries`, `IsDigitDecomp`, `psiSeries`, `seriesEval`, `mahlerK`, `formalLog` = 6 defs; 49 lemmas/theorems; 1 instance. (Total 56.)

Corrected counts: **6 defs / 49 lemmas+theorems / 1 instance = 56 declarations.**

Key API (used by ≥3 declarations in this file):
- `phiSeries` — used by ~21 decls (the central operator).
- `seriesEval` — used by 12 decls.
- `IsDigitDecomp` — used by 10 decls.
- `psiSeries` — used by 8 decls.
- `hasSubst_one_add_X_pow_sub_one` — used by 10 decls.
- `coeff_substSeries_pow_eq_zero` — used by 5 decls.
- `norm_coeff_substSeries_pow_le_one` — used by 4 decls.
- `existsUnique_measure_digits` — used by 3 decls.
- `psi_dirac_neg_mul_sum` — used by 3 decls.
- `mahlerTransform_sum_dirac_mul_phi` — used by 3 decls.
- `mahlerK` — used by 4 decls.
- `formalLog` — used by 5 decls.
- `psiSeries_eq_of_isDigitDecomp` — used by 4 decls.
- `tendsto_natCast_succ_mul_pow` (private) — used by 2 (borderline).

Unused in this file (terminal API, likely consumed by ValuesAtOne.lean / c₀-design / downstream): `phiSeries_C_mul`, `psiSeries_C`, `psiSeries_add`, `psiSeries_C_mul`, `psiSeries_map`, `mahlerTransform_psi`, `seriesEval_zero_arg`, `seriesEval_sub`, `seriesEval_C`, `seriesEval_C_mul`, `mahlerK_sub`, `mahlerK_phi`, `norm_coeff_mahlerK_le_one`, `summable_prod_of_norm_coeff_le_linear`, `seriesEval_phi_at_root_of_summable`, `summable_seriesEval_of_norm_coeff_le_linear`, `norm_coeff_phiSeries_le_linear`, `sum_seriesEval_mahlerK`, `exists_antideriv`, `phiSeries_formalLog`, the `NonarchimedeanRing K` instance. (`norm_coeff_phiSeries_le_linear`, `summable_prod_of_norm_coeff_le_linear`, `summable_seriesEval_of_norm_coeff_le_linear` are the polynomial-growth variants reserved for the c₀ antiderivative design.)

Decls with `sorry`: NONE.

`set_option`: one — `seriesEval_mul` (`set_option maxHeartbeats 1000000`, lines 910-911, justified: nested tsum/Cauchy-product over `coeff` is heartbeat-heavy). No `sorry`/`admit`/`TODO`.

Proofs > 50 lines (OVER-50, need /decompose-proof) — 3:
- `mahlerTransform_phi` (66 lines, 205-278)
- `sum_seriesEval_mahlerK` (87 lines, 1065-1163)
- (no third over 50; `existsUnique_measure_digits` is 35 = long, not over-50)

Count of OVER-50: **2**.

Proofs 30-50 lines (long) — 6:
- `sum_charFn_pZp_sub_natCast` (31, 339-376)
- `existsUnique_measure_digits` (35, 395-431)
- `seriesEval_phi_of_summable_prod` (34, 700-744)
- `summable_prod_of_norm_coeff_le_one` (33, 791-833)
- `summable_prod_of_norm_coeff_le_linear` (33, 835-877)

Count of 30-50: **5**.

Notable: section `bridge` is the largest API surface (evaluation theory + the realised `Eqphipsi`). `mahlerTransform_phi` and `sum_seriesEval_mahlerK` are the two decomposition candidates. The `psiSeries` def carries an extensive replan-R6 docstring documenting that the digit decomposition is FALSE over fields where `p` is invertible — junk-totalised, with all soundness pushed onto the `∃!` hypotheses / `integerRing K` locus.
