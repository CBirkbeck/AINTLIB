# Inventory: PadicLFunctions/MeasureR/MahlerTransform.lean

File-level: `namespace PadicLFunctions`, then `noncomputable section`, then `namespace MeasureR`.
Shared variables: `p : ℕ` `[hp : Fact p.Prime]`; `K : Type*` `[NormedField K]` `[NormedAlgebra ℚ_[p] K]` `[IsUltrametricDist K]` `[CompleteSpace K]`.
The coefficient-general Mahler/Amice transform for measures valued in `R := integerRing K`: `𝓐_μ(T) = ∑_n (∫ binom(x,n) dμ) Tⁿ ∈ R⟦T⟧`, giving a linear equivalence `MeasureR K ℤ_[p] ≃ R⟦T⟧` (RJW §3.4, Thm 3.20).

---

### def mahlerCM
- Type: `mahlerCM (n : ℕ) : C(ℤ_[p], integerRing K)`
- What: The `n`-th Mahler basis function `x ↦ binom(x, n)`, viewed as an `R = integerRing K`-valued continuous function by pushing mathlib's `mahler n` through the isometric algebra map `ℤ_[p] → integerRing K`.
- How: Bundles `fun x => algebraMap ℤ_[p] (integerRing K) (mahler n x)` with a continuity proof composing the continuity of the isometric algebra map (`integerRing.isometry_algebraMap`) with `map_continuous` of the bundled `mahler n`.
- Hypotheses: `n : ℕ`; ambient field/algebra/ultrametric instances on `K` (does NOT need `CompleteSpace` but defined under it).
- Uses from project: [`integerRing`, `integerRing.isometry_algebraMap`]
- Used by: `mahlerCM_apply`, `mahlerTerm_eq`, `mahlerTransform`, `coeff_mahlerTransform`, `apply_eq_tsum`, `mahlerTransform_dirac`, `mahlerTransform_injective`, `fwdDiff_iter_mahlerCM_zero`, `mahlerTransform_ofPowerSeries`
- Visibility: public
- Lines: 41–45 (def, ~2-line body)
- Notes: none

### lemma mahlerCM_apply
- Type: `mahlerCM p K n x = algebraMap ℤ_[p] (integerRing K) (mahler n x)`
- What: Computes the value of the `R`-valued Mahler basis function at a point `x` as the algebra-map image of `mahler n x`.
- How: `rfl` (definitional unfolding of `mahlerCM`).
- Hypotheses: `n : ℕ`, `x : ℤ_[p]`; `CompleteSpace K` omitted.
- Uses from project: [`mahlerCM`]
- Used by: `mahlerTerm_eq`, `mahlerTransform_dirac`, `fwdDiff_iter_mahlerCM_zero`
- Visibility: public
- Lines: 47–50 (proof: `rfl`)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### lemma mahlerTerm_eq
- Type: `(PadicInt.mahlerTerm a n : C(ℤ_[p], integerRing K)) = a • mahlerCM p K n`
- What: Identifies mathlib's Mahler-expansion summand `mahlerTerm a n` with the `R`-scalar multiple `a • mahlerCM n`.
- How: `ext x`, then rewrite through `PadicInt.mahlerTerm_apply`, `ContinuousMap.smul_apply`, `smul_eq_mul`, `mahlerCM_apply`, and `Algebra.smul_def` with `mul_comm` to reconcile the scalar action with the algebra-map multiplication.
- Hypotheses: `a : integerRing K`, `n : ℕ`; `CompleteSpace K` omitted.
- Uses from project: [`mahlerCM`, `mahlerCM_apply`]
- Used by: `apply_eq_tsum`
- Visibility: private
- Lines: 54–61 (proof ~3 lines)
- Notes: `omit [CompleteSpace K]`

### def mahlerTransform
- Type: `mahlerTransform (μ : MeasureR K ℤ_[p]) : PowerSeries (integerRing K)`
- What: The Mahler/Amice transform `𝓐_μ(T) = ∑_n (∫ binom(x,n) dμ) Tⁿ`, the power series whose `n`-th coefficient is `μ (mahlerCM n)` (RJW Def 3.15).
- How: `PowerSeries.mk fun n => μ (mahlerCM p K n)`.
- Hypotheses: `μ : MeasureR K ℤ_[p]`.
- Uses from project: [`MeasureR`, `mahlerCM`]
- Used by: `coeff_mahlerTransform`, `mahlerTransformₗ`, `mahlerTransform_dirac`, `mahlerTransform_injective`, `mahlerTransform_ofPowerSeries`, `mahlerLinearEquiv` (left_inv), `mahlerTransform_smul`, `mahlerTransform_sub`, `mahlerLinearEquiv_apply`
- Visibility: public
- Lines: 65–68 (1-line body)
- Notes: none

### lemma coeff_mahlerTransform
- Type: `PowerSeries.coeff n (mahlerTransform p K μ) = μ (mahlerCM p K n)`
- What: The `n`-th power-series coefficient of the Mahler transform equals the measure applied to the `n`-th Mahler basis function.
- How: `simp [mahlerTransform]` (unfolds `PowerSeries.mk` / `coeff`).
- Hypotheses: `μ : MeasureR K ℤ_[p]`, `n : ℕ`; `CompleteSpace K` omitted.
- Uses from project: [`mahlerTransform`, `mahlerCM`, `MeasureR`]
- Used by: `mahlerTransform_dirac`, `mahlerTransform_injective`, `mahlerTransform_ofPowerSeries`, `mahlerLinearEquiv` (left_inv)
- Visibility: public
- Lines: 70–74 (proof: 1 line)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### def mahlerTransformₗ
- Type: `mahlerTransformₗ : MeasureR K ℤ_[p] →ₗ[integerRing K] PowerSeries (integerRing K)`
- What: The Mahler transform packaged as an `R`-linear map between the measure module and the power-series ring.
- How: Structure literal with `toFun := mahlerTransform p K`; `map_add'` and `map_smul'` each discharged by `ext n; simp [mahlerTransform]`.
- Hypotheses: ambient instances only.
- Uses from project: [`MeasureR`, `integerRing`, `mahlerTransform`]
- Used by: `mahlerLinearEquiv` (extends it), `mahlerTransform_smul`, `mahlerTransform_sub`
- Visibility: public
- Lines: 76–81 (proofs: 1 line each)
- Notes: none

### theorem apply_eq_tsum
- Type: `μ f = ∑' n, Δ_[1]^[n] (⇑f) 0 * μ (mahlerCM p K n)`
- What: Evaluation formula — any `R`-valued continuous functional `μ f` equals the sum over `n` of the `n`-th iterated forward difference of `f` at `0` times the `n`-th Mahler coefficient `μ (mahlerCM n)` (RJW Thm 3.20 proof).
- How: Obtains `h2 : HasSum (...) (μ f)` by applying mathlib's `PadicInt.hasSum_mahler f` and mapping the resulting sum through the continuous additive monoid hom `μ.toAddMonoidHom` (continuity from `MeasureR.continuous μ`); then `h2.tsum_eq.symm.trans (tsum_congr …)` rewriting each term via `mahlerTerm_eq`, `map_smul`, `smul_eq_mul`.
- Hypotheses: `μ : MeasureR K ℤ_[p]`, `f : C(ℤ_[p], integerRing K)`; needs the complete-ultrametric setting for `hasSum_mahler`.
- Uses from project: [`MeasureR`, `mahlerCM`, `MeasureR.continuous`, `mahlerTerm_eq`]
- Used by: `mahlerTransform_injective`, `mahlerLinearEquiv` (left_inv)
- Visibility: public
- Lines: 85–92 (proof ~4 lines)
- Notes: hinges on `PadicInt.hasSum_mahler` (mathlib) and `MeasureR.continuous`; none

### theorem mahlerTransform_dirac
- Type: `mahlerTransform p K (dirac K ℤ_[p] a) = PowerSeries.map (algebraMap ℤ_[p] (integerRing K)) (binomialSeries ℤ_[p] a)`
- What: The Mahler transform of the Dirac measure at `a` is the binomial series `(1+T)^a` pushed coefficientwise through the algebra map (RJW Ex 3.16).
- How: `ext n`, then rewrite the `n`-th coefficient through `coeff_mahlerTransform`, `PowerSeries.coeff_map`, `binomialSeries_coeff`, `dirac_apply`, `mahlerCM_apply`, `mahler_apply`, finishing with `smul_eq_mul`, `map_mul`, `map_one`, `mul_one`.
- Hypotheses: `a : ℤ_[p]`; `CompleteSpace K` omitted.
- Uses from project: [`mahlerTransform`, `dirac`, `coeff_mahlerTransform`, `mahlerCM_apply`, `dirac_apply`]
- Used by: unused in file
- Visibility: public
- Lines: 96–106 (proof ~3 lines)
- Notes: `omit [CompleteSpace K]`; `@[simp]`; references `binomialSeries`/`binomialSeries_coeff` (from mathlib `PowerSeries.Binomial`)

### theorem mahlerTransform_injective
- Type: `Function.Injective (mahlerTransform p K)`
- What: The Mahler transform is injective — a measure is uniquely determined by its Amice transform (RJW Thm 3.20, "uniquely determined").
- How: Given `μ ν` with equal transforms, use `LinearMap.ext fun f`, rewrite both sides via the evaluation formula `apply_eq_tsum`, then `tsum_congr`; the per-coefficient equality `μ (mahlerCM n) = ν (mahlerCM n)` is `congrArg (PowerSeries.coeff n) h` simplified.
- Hypotheses: ambient complete-ultrametric instances (uses `apply_eq_tsum`).
- Uses from project: [`mahlerTransform`, `apply_eq_tsum`, `mahlerCM`]
- Used by: unused in file
- Visibility: public
- Lines: 110–119 (proof ~6 lines)
- Notes: none

### lemma summable_fwdDiff_mul
- Type: `Summable fun n => Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g`
- What: The pairing series `∑ Δⁿf(0) · g_n` is summable, because Mahler coefficients of `f` tend to zero and the power-series coefficients (being elements of `integerRing K`) have norm `≤ 1`.
- How: Reduces to `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; rewrites cofinite to `atTop`; takes `h := PadicInt.fwdDiff_tendsto_zero f`, passes to norms, then `squeeze_zero` bounding `‖Δⁿf(0)·g_n‖ ≤ ‖Δⁿf(0)‖·‖g_n‖ ≤ ‖Δⁿf(0)‖·1 = ‖Δⁿf(0)‖` via `norm_mul_le`, `mul_le_mul_of_nonneg_left`, and the integrality bound `(PowerSeries.coeff n g).2`.
- Hypotheses: `f : C(ℤ_[p], integerRing K)`, `g : PowerSeries (integerRing K)`.
- Uses from project: []
- Used by: `ofPowerSeries`
- Visibility: private
- Lines: 121–135 (proof ~10 lines, incl. 3-step `calc`)
- Notes: hinges on `PadicInt.fwdDiff_tendsto_zero` and `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` (mathlib); none

### def ofPowerSeries
- Type: `ofPowerSeries (g : PowerSeries (integerRing K)) : MeasureR K ℤ_[p]`
- What: The measure attached to a power series `g`, defined by `f ↦ ∑' n, Δⁿf(0) · g_n` (the inverse construction of the Mahler transform; RJW Thm 3.20 converse).
- How: Structure literal: `toFun f := ∑' n, Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g`. Additivity uses `fwdDiff_iter_add`, `add_mul`, then `(summable_fwdDiff_mul f₁ g).tsum_add (summable_fwdDiff_mul f₂ g)`. Smul-compatibility uses `fwdDiff_iter_const_smul`, `mul_assoc`, then `(summable_fwdDiff_mul f g).tsum_mul_left c`.
- Hypotheses: `g : PowerSeries (integerRing K)`.
- Uses from project: [`MeasureR`, `summable_fwdDiff_mul`]
- Used by: `mahlerTransform_ofPowerSeries`, `mahlerLinearEquiv` (invFun), `mahlerLinearEquiv_symm_apply`
- Visibility: public
- Lines: 137–149 (proofs ~3 lines each)
- Notes: depends on `summable_fwdDiff_mul` for both `MeasureR` field proofs; none

### lemma fwdDiff_iter_mahlerCM_zero
- Type: `Δ_[1]^[n] (⇑(mahlerCM p K k)) 0 = if n = k then 1 else 0`
- What: The iterated forward difference of the `R`-valued `k`-th Mahler basis function at `0` is the Kronecker delta `δ_{nk}`, by transporting the `ℤ_p` statement through the algebra map.
- How: Establishes `key` equating the `R`-side forward difference with `algebraMap (Δⁿ(mahler k)(0))` by rewriting both via `fwdDiff_iter_eq_sum_shift`, `map_sum`, and `Finset.sum_congr` with `mahlerCM_apply`; then `rw [key, PadicMeasure.fwdDiff_iter_mahler_zero]` and `split <;> simp`.
- Hypotheses: `n k : ℕ`; `CompleteSpace K` omitted.
- Uses from project: [`mahlerCM`, `mahlerCM_apply`, `PadicMeasure.fwdDiff_iter_mahler_zero`]
- Used by: `mahlerTransform_ofPowerSeries`
- Visibility: private
- Lines: 153–165 (proof ~9 lines)
- Notes: `omit [CompleteSpace K]`; hinges on `PadicMeasure.fwdDiff_iter_mahler_zero` (project) and `fwdDiff_iter_eq_sum_shift` (mathlib); none

### theorem mahlerTransform_ofPowerSeries
- Type: `mahlerTransform p K (ofPowerSeries p K g) = g`
- What: The Mahler transform of `ofPowerSeries g` recovers `g` — the right inverse property ("Visibly 𝓐_{μ_g} = g", RJW Thm 3.20).
- How: `PowerSeries.ext fun k`, rewrite the `k`-th coefficient via `coeff_mahlerTransform`, `change` to the explicit tsum, then `simp_rw [fwdDiff_iter_mahlerCM_zero, ite_mul, one_mul, zero_mul]` collapses the Kronecker delta and finishes with `tsum_ite_eq k _`.
- Hypotheses: `g : PowerSeries (integerRing K)`.
- Uses from project: [`mahlerTransform`, `ofPowerSeries`, `coeff_mahlerTransform`, `mahlerCM`, `fwdDiff_iter_mahlerCM_zero`]
- Used by: `mahlerLinearEquiv` (right_inv)
- Visibility: public
- Lines: 167–177 (proof ~5 lines)
- Notes: `@[simp]`; none

### def mahlerLinearEquiv
- Type: `mahlerLinearEquiv : MeasureR K ℤ_[p] ≃ₗ[integerRing K] PowerSeries (integerRing K)`
- What: RJW Theorem 3.20 over `R`, linear part — the Mahler transform is an `R`-linear equivalence `ℳ(ℤ_p, R) ≃ R⟦T⟧`.
- How: Extends `mahlerTransformₗ p K` with `invFun := ofPowerSeries p K`; `left_inv` via `LinearMap.ext`, `change` to the tsum, `simp_rw [coeff_mahlerTransform]`, then `(apply_eq_tsum μ f).symm`; `right_inv := mahlerTransform_ofPowerSeries`.
- Hypotheses: ambient complete-ultrametric instances (uses `apply_eq_tsum`).
- Uses from project: [`MeasureR`, `integerRing`, `mahlerTransformₗ`, `ofPowerSeries`, `coeff_mahlerTransform`, `apply_eq_tsum`, `mahlerTransform`, `mahlerTransform_ofPowerSeries`]
- Used by: `mahlerLinearEquiv_apply`, `mahlerLinearEquiv_symm_apply`
- Visibility: public
- Lines: 179–192 (left_inv proof ~4 lines)
- Notes: none

### lemma mahlerTransform_smul
- Type: `mahlerTransform p K (w • μ) = PowerSeries.C w * mahlerTransform p K μ`
- What: The Mahler transform intertwines the `R`-scalar action `w • μ` with multiplication by the constant power series `C w`.
- How: `rw [← PowerSeries.smul_eq_C_mul]`, then `map_smul (mahlerTransformₗ p K) w μ`.
- Hypotheses: `w : integerRing K`, `μ : MeasureR K ℤ_[p]`; `CompleteSpace K` omitted.
- Uses from project: [`mahlerTransform`, `mahlerTransformₗ`, `integerRing`, `MeasureR`]
- Used by: unused in file
- Visibility: public
- Lines: 194–200 (proof: 2 lines)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### lemma mahlerTransform_sub
- Type: `mahlerTransform p K (μ - ν) = mahlerTransform p K μ - mahlerTransform p K ν`
- What: The Mahler transform commutes with subtraction of measures.
- How: `map_sub (mahlerTransformₗ p K) μ ν`.
- Hypotheses: `μ ν : MeasureR K ℤ_[p]`; `CompleteSpace K` omitted.
- Uses from project: [`mahlerTransform`, `mahlerTransformₗ`, `MeasureR`]
- Used by: unused in file
- Visibility: public
- Lines: 202–207 (proof: 1 line)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### lemma mahlerLinearEquiv_apply
- Type: `mahlerLinearEquiv p K μ = mahlerTransform p K μ`
- What: The forward direction of the linear equivalence is (definitionally) the Mahler transform.
- How: `rfl`.
- Hypotheses: `μ : MeasureR K ℤ_[p]`.
- Uses from project: [`mahlerLinearEquiv`, `mahlerTransform`, `MeasureR`]
- Used by: unused in file
- Visibility: public
- Lines: 209–211 (proof: `rfl`)
- Notes: `@[simp]`

### lemma mahlerLinearEquiv_symm_apply
- Type: `(mahlerLinearEquiv p K).symm g = ofPowerSeries p K g`
- What: The inverse direction of the linear equivalence is (definitionally) `ofPowerSeries`.
- How: `rfl`.
- Hypotheses: `g : PowerSeries (integerRing K)`.
- Uses from project: [`mahlerLinearEquiv`, `ofPowerSeries`]
- Used by: unused in file
- Visibility: public
- Lines: 213–215 (proof: `rfl`)
- Notes: `@[simp]`

---

## File Summary

- **Total declarations: 17** — defs: 5 (`mahlerCM`, `mahlerTransform`, `mahlerTransformₗ`, `ofPowerSeries`, `mahlerLinearEquiv`); lemmas+theorems: 12 (`mahlerCM_apply`, `mahlerTerm_eq`, `coeff_mahlerTransform`, `apply_eq_tsum`, `mahlerTransform_dirac`, `mahlerTransform_injective`, `summable_fwdDiff_mul`, `fwdDiff_iter_mahlerCM_zero`, `mahlerTransform_ofPowerSeries`, `mahlerTransform_smul`, `mahlerTransform_sub`, `mahlerLinearEquiv_apply`, `mahlerLinearEquiv_symm_apply` — note this lists 13; theorems among them: `apply_eq_tsum`, `mahlerTransform_dirac`, `mahlerTransform_injective`, `mahlerTransform_ofPowerSeries`); instances: 0.
- **Correction on counts:** defs 5 + lemmas/theorems 12 = 17 total decls; instances 0.
- **Key API (used by ≥3 in file):** `mahlerCM` (used by 9), `mahlerTransform` (used by 9), `coeff_mahlerTransform` (used by 4), `mahlerCM_apply` (used by 3). (`apply_eq_tsum` used by 2; `mahlerTransformₗ` used by 3 → also key.)
- **Unused in file (terminal/public API):** `mahlerTransform_dirac`, `mahlerTransform_injective`, `mahlerTransform_smul`, `mahlerTransform_sub`, `mahlerLinearEquiv_apply`, `mahlerLinearEquiv_symm_apply` (all are exported endpoints, not consumed internally).
- **Decls with `sorry`:** none.
- **`set_option`:** none.
- **Proofs >50 lines (OVER-50):** none (count 0).
- **Proofs 30–50 lines (long):** none (count 0).
- **Longest proofs:** `summable_fwdDiff_mul` (~10 lines), `fwdDiff_iter_mahlerCM_zero` (~9 lines), `mahlerTransform_injective` (~6 lines) — none require decomposition.
- **`omit [CompleteSpace K]`** appears on 7 decls (`mahlerCM_apply`, `mahlerTerm_eq`, `coeff_mahlerTransform`, `mahlerTransform_dirac`, `fwdDiff_iter_mahlerCM_zero`, `mahlerTransform_smul`, `mahlerTransform_sub`).
- **Private decls:** `mahlerTerm_eq`, `summable_fwdDiff_mul`, `fwdDiff_iter_mahlerCM_zero`.
- **Cross-file project dependencies:** `integerRing`, `integerRing.isometry_algebraMap`, `MeasureR`, `MeasureR.continuous`, `dirac`, `dirac_apply`, `PadicMeasure.fwdDiff_iter_mahler_zero` (the last from `PadicLFunctions/Measure/MahlerTransform.lean`, the `ℤ_p`-coefficient layer this file lifts).
