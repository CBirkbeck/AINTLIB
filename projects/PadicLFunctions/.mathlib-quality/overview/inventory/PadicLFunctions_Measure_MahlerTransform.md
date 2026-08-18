# Inventory: PadicLFunctions/Measure/MahlerTransform.lean

File namespace: `PadicMeasure`. Variables: `(p : ℕ) [hp : Fact p.Prime]`, in a `noncomputable section`.

Top-of-file imports: `PadicLFunctions.Measure.Basic`, `Mathlib.RingTheory.PowerSeries.Binomial`.
Open scopes: `fwdDiff`, `PowerSeries`.

---

### def mahlerCoeff
- Type: `mahlerCoeff (μ : PadicMeasure p ℤ_[p]) (n : ℕ) : ℤ_[p] := μ (mahler n)`
- What: The `n`-th Mahler coefficient of a measure `μ` on `ℤ_p`, namely `∫_{ℤ_p} binom(x,n) dμ(x)`, obtained by applying the measure to the `n`-th Mahler basis function `mahler n`.
- How: Direct definition — apply the measure functional `μ` to mathlib's `mahler n : C(ℤ_[p], ℤ_[p])`. No proof.
- Hypotheses: `μ` a `ℤ_[p]`-valued measure (continuous linear functional) on `C(ℤ_[p], ℤ_[p])`; `n` a natural number.
- Uses from project: [`PadicMeasure`]
- Used by: `mahlerTransform`, `apply_eq_tsum`, `mahlerTransform_injective`, `mahlerTransform_ofPowerSeries` (via the `change`)
- Visibility: public
- Lines: 33–37 (no proof)
- Notes: none

### def mahlerTransform
- Type: `mahlerTransform (μ : PadicMeasure p ℤ_[p]) : PowerSeries ℤ_[p] := PowerSeries.mk (mahlerCoeff p μ)`
- What: The Mahler/Amice transform `𝓐_μ(T) = ∑_{n≥0} (∫ binom(x,n) dμ) Tⁿ ∈ ℤ_p[[T]]`, the power series whose coefficients are the Mahler coefficients of `μ`.
- How: Direct definition via `PowerSeries.mk` applied to the coefficient function `mahlerCoeff p μ`. No proof.
- Hypotheses: `μ` a `ℤ_[p]`-valued measure on `ℤ_p`.
- Uses from project: [`PadicMeasure`, `mahlerCoeff`]
- Used by: `coeff_mahlerTransform`, `mahlerTransformₗ`, `mahlerTransform_dirac`, `mahlerTransform_injective`, `mahlerTransform_ofPowerSeries`, `mahlerLinearEquiv`, `mahlerLinearEquiv_apply`
- Visibility: public
- Lines: 39–44 (no proof)
- Notes: none

### lemma coeff_mahlerTransform
- Type: `coeff_mahlerTransform (μ : PadicMeasure p ℤ_[p]) (n : ℕ) : PowerSeries.coeff n (mahlerTransform p μ) = μ (mahler n)`
- What: The `n`-th power-series coefficient of `mahlerTransform p μ` equals `μ (mahler n)`, i.e. unfolds the transform's coefficient to the measure applied to the Mahler basis function.
- How: `simp [mahlerTransform, mahlerCoeff]` — unfolds the definitions and uses `PowerSeries.coeff_mk`.
- Hypotheses: `μ` a measure; `n : ℕ`.
- Uses from project: [`mahlerTransform`, `mahlerCoeff`, `PadicMeasure`]
- Used by: `mahlerTransform_ofPowerSeries`, `mahlerLinearEquiv` (left_inv)
- Visibility: public; `@[simp]`
- Lines: 46–49 (proof 1 line)
- Notes: none

### def mahlerTransformₗ
- Type: `mahlerTransformₗ : PadicMeasure p ℤ_[p] →ₗ[ℤ_[p]] PowerSeries ℤ_[p]` (structure literal: `toFun := mahlerTransform p`, with `map_add'`, `map_smul'`)
- What: The Mahler transform packaged as a `ℤ_[p]`-linear map from measures to power series.
- How: Builds the `LinearMap` structure; both `map_add'` and `map_smul'` are discharged by `ext n; simp [mahlerTransform, mahlerCoeff]`, reducing to additivity/`ℤ_[p]`-linearity of the measure functional coefficientwise.
- Hypotheses: none beyond the ambient `p`, `Fact p.Prime`.
- Uses from project: [`PadicMeasure`, `mahlerTransform`, `mahlerCoeff`]
- Used by: `mahlerLinearEquiv`
- Visibility: public
- Lines: 51–56 (proofs 1 line each)
- Notes: none

### theorem apply_eq_tsum
- Type: `apply_eq_tsum (μ : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) : μ f = ∑' n, Δ_[1]^[n] (⇑f) 0 * mahlerCoeff p μ n`
- What: Evaluation formula — integrating a continuous `f` against `μ` equals the convergent sum `∑' n, Δⁿf(0) · (∫ binom(x,n) dμ)`, pairing Mahler coefficients of `f` with those of `μ`; the uniqueness content of RJW Thm 3.20.
- How: Uses Mahler's theorem `PadicInt.hasSum_mahler f` (the Mahler expansion of `f`), pushes it through the continuous additive monoid hom `μ.toAddMonoidHom` via `HasSum.map` (needing `continuous p μ`), rewrites each term `μ (mahlerTerm a n) = a • μ (mahler n)` through the auxiliary identity `(mahlerTerm a n) = a • mahler n` and `map_smul`, then concludes with `tsum_eq`/`tsum_congr`.
- Hypotheses: `μ` a measure; `f` a continuous `ℤ_[p]`-valued function on `ℤ_[p]`.
- Uses from project: [`PadicMeasure`, `mahlerCoeff`, `continuous`]
- Used by: `mahlerTransform_injective`, `mahlerLinearEquiv` (left_inv)
- Visibility: public
- Lines: 58–72 (proof ~7 lines)
- Notes: none — hinges on mathlib `PadicInt.hasSum_mahler`, `PadicInt.mahlerTerm`, `HasSum.map`.

### theorem mahlerTransform_dirac
- Type: `mahlerTransform_dirac (a : ℤ_[p]) : mahlerTransform p (dirac p a) = binomialSeries ℤ_[p] a`
- What: The Mahler transform of the Dirac measure `δ_a` is the binomial power series `(1+T)^a` (RJW Ex. 3.16).
- How: `ext n` then `simp [binomialSeries_coeff, mahler_apply, smul_eq_mul]` — coefficientwise, `coeff n (𝓐_{δ_a}) = δ_a(mahler n) = mahler n a = binom(a,n) = coeff n (binomialSeries a)`.
- Hypotheses: `a : ℤ_[p]`.
- Uses from project: [`mahlerTransform`, `dirac`]
- Used by: unused in file
- Visibility: public; `@[simp]`
- Lines: 74–81 (proof 2 lines)
- Notes: none — relies on mathlib `dirac` apply simp lemmas, `binomialSeries_coeff`, `mahler_apply`.

### theorem mahlerTransform_injective
- Type: `mahlerTransform_injective : Function.Injective (mahlerTransform p)`
- What: The Mahler transform is injective — a measure killing every `binom(·,n)` (equivalently, with vanishing transform) is the zero measure; measures are determined by their Mahler coefficients.
- How: Given `μ`, `ν` with equal transforms, uses `LinearMap.ext` and `apply_eq_tsum` to write both `μ f` and `ν f` as `tsum`s of Mahler-coefficient pairings, then `tsum_congr` reduces to equality of coefficients `μ (mahler n) = ν (mahler n)`, obtained from `congrArg (PowerSeries.coeff n) h`.
- Hypotheses: none beyond ambient.
- Uses from project: [`mahlerTransform`, `apply_eq_tsum`, `mahlerCoeff`]
- Used by: unused in file
- Visibility: public
- Lines: 83–92 (proof ~6 lines)
- Notes: none — hinges on `apply_eq_tsum`.

### lemma summable_fwdDiff_mul
- Type: `summable_fwdDiff_mul (f : C(ℤ_[p], ℤ_[p])) (g : PowerSeries ℤ_[p]) : Summable fun n => Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g`
- What: The summand `Δⁿf(0)·gₙ` is summable, because the Mahler coefficients `Δⁿf(0)` tend to zero and the power-series coefficients have norm `≤ 1`.
- How: Reduces summability to `cofinite`/`atTop` tendsto-zero via `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`; uses `PadicInt.fwdDiff_tendsto_zero f`, converts to norm convergence (`tendsto_zero_iff_norm_tendsto_zero`), and `squeeze_zero` bounding `‖Δⁿf(0)·gₙ‖ = ‖Δⁿf(0)‖·‖gₙ‖ ≤ ‖Δⁿf(0)‖` via `PadicInt.norm_le_one`.
- Hypotheses: `f` continuous on `ℤ_[p]`; `g` a power series over `ℤ_[p]`.
- Uses from project: []
- Used by: `ofPowerSeries`
- Visibility: private
- Lines: 94–106 (proof ~9 lines)
- Notes: none — hinges on mathlib `PadicInt.fwdDiff_tendsto_zero`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `squeeze_zero`.

### def ofPowerSeries
- Type: `ofPowerSeries (g : PowerSeries ℤ_[p]) : PadicMeasure p ℤ_[p]` (structure literal: `toFun f := ∑' n, Δ_[1]^[n] (⇑f) 0 * PowerSeries.coeff n g`, with `map_add'`, `map_smul'`)
- What: The inverse construction — the measure `μ_g` attached to a power series `g`, defined by `φ ↦ ∑' n, Δⁿφ(0)·gₙ`; the converse direction of RJW Thm 3.20.
- How: Builds the `PadicMeasure` (a continuous `ℤ_[p]`-linear functional) structure. `map_add'` uses `fwdDiff_iter_add` + `summable_fwdDiff_mul`'s `.tsum_add`; `map_smul'` uses `fwdDiff_iter_const_smul` + `.tsum_mul_left`. Continuity/completeness comes from `summable_fwdDiff_mul`.
- Hypotheses: `g` a power series over `ℤ_[p]`.
- Uses from project: [`PadicMeasure`, `summable_fwdDiff_mul`]
- Used by: `mahlerTransform_ofPowerSeries`, `mahlerLinearEquiv` (invFun), `mahlerLinearEquiv_symm_apply`
- Visibility: public
- Lines: 108–121 (proofs ~2 lines each)
- Notes: none — note the `PadicMeasure` structure here supplies its own continuity field; the def relies on `summable_fwdDiff_mul`.

### lemma fwdDiff_iter_mahler_zero
- Type: `fwdDiff_iter_mahler_zero (n k : ℕ) : Δ_[1]^[n] (⇑(mahler k : C(ℤ_[p], ℤ_[p]))) 0 = if n = k then 1 else 0`
- What: The `n`-th iterated forward difference at `0` of the `k`-th Mahler function `binom(·,k)` over `ℤ_p` is the Kronecker delta `δ_{nk}`.
- How: Transports from mathlib's `fwdDiff_iter_choose_zero` (over `ℕ → ℤ`): rewrites both sides via `fwdDiff_iter_eq_sum_shift` to finite sums, matches summands using `mahler_natCast_eq` to identify `mahler k` evaluated at a cast natural with `binom(i,k)`, casting `ℤ → ℤ_[p]` (`push_cast`, `ring`); then `fwdDiff_iter_choose_zero` gives the delta and `split <;> simp` finishes.
- Hypotheses: `n k : ℕ`.
- Uses from project: []
- Used by: `mahlerTransform_ofPowerSeries`
- Visibility: public
- Lines: 123–140 (proof ~13 lines)
- Notes: none (proof 13 lines, under 30) — hinges on mathlib `fwdDiff_iter_choose_zero`, `fwdDiff_iter_eq_sum_shift`, `mahler_natCast_eq`.

### theorem mahlerTransform_ofPowerSeries
- Type: `mahlerTransform_ofPowerSeries (g : PowerSeries ℤ_[p]) : mahlerTransform p (ofPowerSeries p g) = g`
- What: The Mahler transform recovers the power series it was built from: `𝓐_{μ_g} = g`, i.e. `∫ binom(x,k) dμ_g = g_k` for all `k` (the "Visibly 𝓐_{μ_g} = g" step of RJW Thm 3.20).
- How: `ext k`, rewrite via `coeff_mahlerTransform`, `change` to the defining `tsum`, then `simp_rw [fwdDiff_iter_mahler_zero, ite_mul, one_mul, zero_mul, tsum_ite_eq]` — the Kronecker delta collapses the sum to the single `k`-th term.
- Hypotheses: `g` a power series over `ℤ_[p]`.
- Uses from project: [`mahlerTransform`, `ofPowerSeries`, `coeff_mahlerTransform`, `fwdDiff_iter_mahler_zero`, `mahlerCoeff` (via `change`)]
- Used by: `mahlerLinearEquiv` (right_inv)
- Visibility: public; `@[simp]`
- Lines: 142–152 (proof ~5 lines)
- Notes: none — hinges on `fwdDiff_iter_mahler_zero` and `tsum_ite_eq`.

### def mahlerLinearEquiv
- Type: `mahlerLinearEquiv : PadicMeasure p ℤ_[p] ≃ₗ[ℤ_[p]] PowerSeries ℤ_[p]` (extends `mahlerTransformₗ p`, with `invFun := ofPowerSeries p`, `left_inv`, `right_inv`)
- What: RJW Theorem 3.20 (linear part) — the Mahler transform is a `ℤ_[p]`-linear equivalence `ℳ(ℤ_p, ℤ_p) ≃ ℤ_p[[T]]` (upgraded to a ring iso in `Measure.Convolution`).
- How: Assembles the `≃ₗ` from `mahlerTransformₗ p` with inverse `ofPowerSeries p`. `left_inv` uses `LinearMap.ext`, `change` to the `tsum`, `coeff_mahlerTransform`, and `apply_eq_tsum`; `right_inv` is exactly `mahlerTransform_ofPowerSeries p`.
- Hypotheses: none beyond ambient.
- Uses from project: [`PadicMeasure`, `mahlerTransformₗ`, `ofPowerSeries`, `coeff_mahlerTransform`, `apply_eq_tsum`, `mahlerTransform`, `mahlerTransform_ofPowerSeries`]
- Used by: `mahlerLinearEquiv_apply`, `mahlerLinearEquiv_symm_apply`
- Visibility: public
- Lines: 154–165 (proof ~5 lines)
- Notes: none

### lemma mahlerLinearEquiv_apply
- Type: `mahlerLinearEquiv_apply (μ : PadicMeasure p ℤ_[p]) : mahlerLinearEquiv p μ = mahlerTransform p μ := rfl`
- What: The forward direction of the linear equivalence is definitionally the Mahler transform.
- How: `rfl`.
- Hypotheses: `μ` a measure.
- Uses from project: [`mahlerLinearEquiv`, `mahlerTransform`]
- Used by: unused in file
- Visibility: public; `@[simp]`
- Lines: 167–169 (proof rfl)
- Notes: none

### lemma mahlerLinearEquiv_symm_apply
- Type: `mahlerLinearEquiv_symm_apply (g : PowerSeries ℤ_[p]) : (mahlerLinearEquiv p).symm g = ofPowerSeries p g := rfl`
- What: The inverse direction of the linear equivalence is definitionally `ofPowerSeries`.
- How: `rfl`.
- Hypotheses: `g` a power series over `ℤ_[p]`.
- Uses from project: [`mahlerLinearEquiv`, `ofPowerSeries`]
- Used by: unused in file
- Visibility: public; `@[simp]`
- Lines: 171–173 (proof rfl)
- Notes: none

---

## File Summary

- **Total declarations: 13** — defs: 5 (`mahlerCoeff`, `mahlerTransform`, `mahlerTransformₗ`, `ofPowerSeries`, `mahlerLinearEquiv`) / lemmas+theorems: 8 (`coeff_mahlerTransform`, `apply_eq_tsum`, `mahlerTransform_dirac`, `mahlerTransform_injective`, `summable_fwdDiff_mul`, `fwdDiff_iter_mahler_zero`, `mahlerTransform_ofPowerSeries`, `mahlerLinearEquiv_apply`, `mahlerLinearEquiv_symm_apply` — note `mahlerLinearEquiv_apply`/`_symm_apply` are lemmas, 9 by that count; the headline count of declared lemma/theorem keywords is 8 `lemma`/`theorem` plus the rfl lemmas) / instances: 0.
  - Precise keyword tally: 5 `def`, 8 declarations introduced by `lemma`/`theorem` (`coeff_mahlerTransform`, `apply_eq_tsum`, `mahlerTransform_dirac`, `mahlerTransform_injective`, `summable_fwdDiff_mul`, `fwdDiff_iter_mahler_zero`, `mahlerTransform_ofPowerSeries`) + 2 trailing `lemma` (`mahlerLinearEquiv_apply`, `mahlerLinearEquiv_symm_apply`) = 10 lemma/theorem, 0 instances → **15 total decls** counting all keywords. (Headline: 13 named API objects; 5 defs + 10 lemmas/theorems = 15 by keyword.)
- **Key API (used by ≥3 within this file):**
  - `mahlerTransform` — used by 7 decls.
  - `mahlerCoeff` — used by 4 decls (`mahlerTransform`, `apply_eq_tsum`, `mahlerTransform_injective`, `mahlerTransform_ofPowerSeries`).
  - `PadicMeasure` (imported) — used by 6 decls.
- **Unused within file (likely consumed by `Measure.Convolution` / downstream):** `mahlerTransform_dirac`, `mahlerTransform_injective`, `mahlerLinearEquiv_apply`, `mahlerLinearEquiv_symm_apply`. (`mahlerLinearEquiv` itself is the file's terminal export.)
- **Decls with `sorry`:** none.
- **`set_option`:** none.
- **Proofs >50 lines (OVER-50):** none. Count: 0.
- **Proofs 30–50 lines (long):** none. Count: 0.
- Longest proof: `fwdDiff_iter_mahler_zero` at ~13 lines; all others ≤9 lines. No proof needs `/decompose-proof`.
