# Inventory: PadicLFunctions/MeasureR/BaseChange.lean

File path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/MeasureR/BaseChange.lean`

Module purpose: Defines base change `Λ(ℤ_p) → Λ_R(ℤ_p)` (decomposition W4) bridging the `ℤ_p`-layer `PadicMeasure` and the coefficient-general `MeasureR` layer, via coefficientwise inclusion of Mahler transforms through the algebra map `ℤ_p → integerRing K`. Proves its characterising property `baseChange_algCM` and naturality with the toolbox operators (cmul, res).

File-level context: `variable (p : ℕ) [hp : Fact p.Prime]`; `variable (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`. Whole file is in a `noncomputable section`. `open scoped fwdDiff`; `open PowerSeries`. Namespaces `PadicLFunctions.MeasureR`.

---

### def baseChange
- Type: `PadicMeasure p ℤ_[p] →+* MeasureR K ℤ_[p]`
- What: The base-change ring homomorphism `Λ(ℤ_p) → Λ_R(ℤ_p)`, sending a `ℤ_p`-valued measure to an `integerRing K`-valued one by mapping its Mahler power-series transform coefficientwise through `algebraMap ℤ_[p] (integerRing K)`.
- How: Composition of three ring homs: the `ℤ_p`-measure→power-series equivalence `PadicMeasure.mahlerRingEquiv p`, then `PowerSeries.map (algebraMap ℤ_[p] (integerRing K))`, then the inverse `(mahlerRingEquiv p K).symm` of the `R`-measure→power-series equivalence.
- Hypotheses: ambient `p` prime, `K` a complete ultrametric normed `ℚ_p`-algebra.
- Uses from project: `PadicMeasure`, `MeasureR`, `mahlerRingEquiv` (MeasureR), `PadicMeasure.mahlerRingEquiv`
- Used by: `mahlerTransform_baseChange`, `baseChange_dirac`, `baseChange_algCM`, `baseChange_cmul`, `baseChange_res`
- Visibility: public
- Lines: 37-42 (def, no proof — direct term)
- Notes: none

### lemma mahlerTransform_baseChange
- Type: `(μ : PadicMeasure p ℤ_[p]) → mahlerTransform p K (baseChange p K μ) = PowerSeries.map (algebraMap ℤ_[p] (integerRing K)) (PadicMeasure.mahlerTransform p μ)`
- What: The Mahler transform of `baseChange μ` equals the coefficientwise image under `algebraMap` of the Mahler transform of `μ`; i.e. base change is exactly "apply `algebraMap` to each Mahler coefficient".
- How: Unfolds `baseChange` and uses `RingEquiv.apply_symm_apply` for `mahlerRingEquiv p K` (the `R`-side equivalence cancels its inverse).
- Hypotheses: same ambient assumptions; `μ` a `ℤ_p`-valued measure.
- Uses from project: `mahlerTransform` (MeasureR), `baseChange`, `PadicMeasure.mahlerTransform`, `mahlerRingEquiv` (MeasureR)
- Used by: `baseChange_dirac`, `baseChange_algCM`
- Visibility: public; `@[simp]`
- Lines: 46-51 (proof: 1 line — single term `apply_symm_apply`)
- Notes: none

### lemma baseChange_dirac
- Type: `(a : ℤ_[p]) → baseChange p K (PadicMeasure.dirac p a) = dirac K ℤ_[p] a`
- What: Base change sends the Dirac measure at `a` (on the `ℤ_p` side) to the Dirac measure at `a` (on the `R` side).
- How: Reduces by `mahlerTransform_injective` to checking equality of Mahler transforms, then rewrites with `mahlerTransform_baseChange`, `PadicMeasure.mahlerTransform_dirac`, and `mahlerTransform_dirac` (both Dirac transforms are the same geometric-type series, made equal after `PowerSeries.map`).
- Hypotheses: same ambient assumptions; `a : ℤ_[p]`.
- Uses from project: `baseChange`, `PadicMeasure.dirac`, `dirac` (MeasureR), `mahlerTransform_injective`, `mahlerTransform_baseChange`, `PadicMeasure.mahlerTransform_dirac`, `mahlerTransform_dirac`
- Used by: unused in file
- Visibility: public; `@[simp]`
- Lines: 53-59 (proof: 3 lines)
- Notes: none

### def algCM
- Type: `(f : C(ℤ_[p], ℤ_[p])) → C(ℤ_[p], integerRing K)`
- What: The `R`-valued ("CM" = continuous map) inclusion of a `ℤ_p`-valued continuous function `f`, namely `x ↦ algebraMap ℤ_[p] (integerRing K) (f x)`, packaged as a continuous map.
- How: Bundles the pointwise composite with continuity proof: `(integerRing.isometry_algebraMap p K).continuous` composed with `map_continuous f`.
- Hypotheses: same ambient assumptions; `f` continuous `ℤ_p`-valued.
- Uses from project: `integerRing`, `integerRing.isometry_algebraMap`
- Used by: `algCM_apply`, `algCM_mahler`, `baseChange_algCM`, `algCM_mul`, `algCM_charFn`, `baseChange_cmul`
- Visibility: public
- Lines: 63-66 (def, no proof)
- Notes: none

### lemma algCM_apply
- Type: `(f : C(ℤ_[p], ℤ_[p])) (x : ℤ_[p]) → algCM K f x = algebraMap ℤ_[p] (integerRing K) (f x)`
- What: Computes the value of `algCM K f` at a point as `algebraMap` applied to `f x`.
- How: `rfl` (definitional).
- Hypotheses: same ambient assumptions (CompleteSpace omitted); `f`, `x`.
- Uses from project: `algCM`, `integerRing`
- Used by: `algCM_mul`, `algCM_charFn`
- Visibility: public; `@[simp]`; `omit [CompleteSpace K]`
- Lines: 68-71 (proof: `rfl`)
- Notes: none

### lemma algCM_mahler
- Type: `(n : ℕ) → algCM K (mahler n) = mahlerCM p K n`
- What: The `R`-valued inclusion of the `n`-th `ℤ_p`-valued Mahler basis function `mahler n` equals the `R`-valued Mahler basis function `mahlerCM p K n`.
- How: `rfl` (definitional — both are `algebraMap ∘ mahler n` by construction).
- Hypotheses: same ambient assumptions (CompleteSpace omitted); `n : ℕ`.
- Uses from project: `algCM`, `mahlerCM`
- Used by: unused in file
- Visibility: public; `omit [CompleteSpace K]`
- Lines: 73-74 (proof: `rfl`)
- Notes: none

### theorem baseChange_algCM
- Type: `(μ : PadicMeasure p ℤ_[p]) (f : C(ℤ_[p], ℤ_[p])) → baseChange p K μ (algCM K f) = algebraMap ℤ_[p] (integerRing K) (μ f)`
- What: The characterising property of base change: integrating the `R`-valued inclusion `algCM K f` against `baseChange μ` equals the `algebraMap`-image of the original integral `μ f`. This pins down `baseChange` on the dense class `algebraMap ∘ f`.
- How: Expands both integrals as Mahler tsum series via `apply_eq_tsum` (both layers). Three auxiliary facts: `hΔ` (forward differences commute with `algebraMap`, proved by `fwdDiff_iter_eq_sum_shift` + `map_sum`); `hcoeff` (`baseChange μ` on `mahlerCM` coefficients equals `algebraMap` of `μ`'s Mahler coefficients, via `coeff_mahlerTransform` + `mahlerTransform_baseChange` + `PowerSeries.coeff_map` + `PadicMeasure.coeff_mahlerTransform`); `hsum` (summability of the `ℤ_p` Mahler series, from `PadicInt.hasSum_mahler` mapped through the measure's continuity). Then a `calc` rewrites the `R`-series termwise into `algebraMap` of the `ℤ_p`-series and pulls `algebraMap` out of the tsum using `Summable.map_tsum` with continuity `integerRing.isometry_algebraMap`.
- Hypotheses: same ambient assumptions; `μ` a `ℤ_p`-valued measure, `f` continuous `ℤ_p`-valued.
- Uses from project: `baseChange`, `algCM`, `PadicMeasure` (`apply_eq_tsum`, `mahlerCoeff`, `coeff_mahlerTransform`), `integerRing`, `integerRing.isometry_algebraMap`, `mahlerCM`, `coeff_mahlerTransform` (MeasureR), `mahlerTransform_baseChange`, `apply_eq_tsum` (MeasureR)
- Used by: `baseChange_cmul`
- Visibility: public
- Lines: 78-112 (proof: ~30 lines, lines 83-112)
- Notes: long(30-50) — borderline ~30-line proof with three nested `have`s and a `calc`; hinges on `PadicInt.hasSum_mahler` and `Summable.map_tsum`. No sorry/set_option.

### lemma algCM_mul
- Type: `(f g : C(ℤ_[p], ℤ_[p])) → algCM K (f * g) = algCM K f * algCM K g`
- What: `algCM` is multiplicative — the inclusion of a product of `ℤ_p`-valued functions is the product of the inclusions.
- How: `ContinuousMap.ext` reduces to pointwise equality, then `simp [algCM_apply]` (algebraMap is a ring hom, so respects multiplication).
- Hypotheses: same ambient assumptions (NormedAlgebra and CompleteSpace not omitted here; only CompleteSpace omitted); `f`, `g`.
- Uses from project: `algCM`, `algCM_apply`
- Used by: `baseChange_cmul`
- Visibility: public; `omit [CompleteSpace K]`
- Lines: 114-118 (proof: 1 line)
- Notes: none

### lemma algCM_charFn
- Type: `{U : Set ℤ_[p]} (hU : IsClopen U) → algCM K (LocallyConstant.charFn ℤ_[p] hU : C(ℤ_[p], ℤ_[p])) = charFnCM K ℤ_[p] hU`
- What: The `R`-valued inclusion of the `ℤ_p`-valued indicator (characteristic function) of a clopen set `U` is the `R`-valued indicator `charFnCM K ℤ_[p] hU`.
- How: `ContinuousMap.ext` to pointwise; rewrites with `algCM_apply`, `charFnCM_apply`; the goal becomes `algebraMap (U.indicator 1 x) = U.indicator 1 x`, settled by `by_cases hx : x ∈ U` and `simp` with `Set.indicator_of_mem`/`Set.indicator_of_notMem` (algebraMap sends 0↦0, 1↦1).
- Hypotheses: same ambient assumptions (CompleteSpace omitted); `U` clopen.
- Uses from project: `algCM`, `algCM_apply`, `charFnCM`, `charFnCM_apply`
- Used by: `baseChange_cmul`, `baseChange_res`
- Visibility: public; `omit [CompleteSpace K]`
- Lines: 120-129 (proof: 5 lines)
- Notes: none

### lemma locallyConstant_eq_sum_smul_charFn
- Type: `(Φ : LocallyConstant ℤ_[p] (integerRing K)) → (Φ.toContinuousMap : C(ℤ_[p], integerRing K)) = ∑ v ∈ Φ.range_finite.toFinset, v • charFnCM K ℤ_[p] (Φ.isLocallyConstant.isClopen_fiber v)`
- What: Any `integerRing K`-valued locally constant function `Φ` equals the finite `R`-linear combination of the indicators of its (clopen, finitely many) fibres, weighted by the fibre values `v`.
- How: `ContinuousMap.ext` to pointwise at `x`, then `Finset.sum_eq_single (Φ x)`: the `v = Φ x` term gives `Φ x` (indicator on its own fibre is 1, `mul_one`); every other `v` contributes 0 (`x ∉ fiber v`, `Set.indicator_of_notMem`, `smul_zero`); and `Φ x ∈ range_finite.toFinset` (`Set.mem_range_self`) discharges the membership side condition.
- Hypotheses: ambient `p` prime, `K` normed field with ultrametric (NormedAlgebra and CompleteSpace omitted); `Φ` locally constant `R`-valued.
- Uses from project: `integerRing`, `charFnCM`
- Used by: `baseChange_cmul`
- Visibility: public; `omit [NormedAlgebra ℚ_[p] K] [CompleteSpace K]`
- Lines: 131-150 (proof: ~12 lines, 138-150)
- Notes: long-ish; hinges on `Finset.sum_eq_single` and `LocallyConstant.isClopen_fiber`. Under 30 lines. No sorry/set_option.

### theorem baseChange_cmul
- Type: `(g : C(ℤ_[p], ℤ_[p])) (μ : PadicMeasure p ℤ_[p]) → baseChange p K (PadicMeasure.cmul p g μ) = cmul p K (algCM K g) (baseChange p K μ)`
- What: Base change commutes with multiplication-by-a-`ℤ_p`-valued-function (the `cmul` toolbox operator): base-changing `g · μ` equals multiplying `baseChange μ` by the inclusion `algCM g`.
- How: `ext_locallyConstant` reduces to checking on a locally constant `Φ`; `locallyConstant_eq_sum_smul_charFn` rewrites `Φ` as a sum of scalar multiples of fibre indicators, `map_sum` distributes both measures over the sum, `Finset.sum_congr` + `map_smul` reduce to the indicator case; then `algCM_charFn` turns the `R`-indicator back into `algCM` of a `ℤ_p`-indicator, a definitional `show` rewrites the `cmul` action as `baseChange μ (algCM g * algCM(charFn))`, and `← algCM_mul` plus two applications of `baseChange_algCM` close it.
- Hypotheses: same ambient assumptions; `g` continuous `ℤ_p`-valued, `μ` a `ℤ_p`-valued measure.
- Uses from project: `baseChange`, `PadicMeasure.cmul`, `cmul` (MeasureR), `algCM`, `ext_locallyConstant`, `locallyConstant_eq_sum_smul_charFn`, `algCM_charFn`, `algCM_mul`, `baseChange_algCM`, `charFnCM` (via the indicator), `LocallyConstant.charFn`
- Used by: `baseChange_res`
- Visibility: public
- Lines: 152-172 (proof: ~14 lines, 158-172)
- Notes: long-ish; under 30 lines. Contains a large definitional `show … from rfl` bridging the `cmul` action. No sorry/set_option.

### theorem baseChange_res
- Type: `{U : Set ℤ_[p]} (hU : IsClopen U) (μ : PadicMeasure p ℤ_[p]) → baseChange p K (PadicMeasure.res p hU μ) = res p K hU (baseChange p K μ)`
- What: Base change commutes with clopen restriction (the `res` toolbox operator): base-changing the restriction of `μ` to `U` equals restricting `baseChange μ` to `U`.
- How: Unfolds `PadicMeasure.res` (= `cmul` by the clopen indicator), applies `baseChange_cmul`, then `algCM_charFn` (inclusion of indicator = `R`-indicator), and finishes with `rfl` (matching the `R`-side `res` definition).
- Hypotheses: same ambient assumptions; `U` clopen, `μ` a `ℤ_p`-valued measure.
- Uses from project: `baseChange`, `PadicMeasure.res`, `res` (MeasureR), `baseChange_cmul`, `algCM_charFn`
- Used by: unused in file
- Visibility: public
- Lines: 174-179 (proof: 2 lines)
- Notes: none

---

## File Summary

- Total decls: 11 (defs: 2 — `baseChange`, `algCM`; lemmas+theorems: 9 — `mahlerTransform_baseChange`, `baseChange_dirac`, `algCM_apply`, `algCM_mahler`, `baseChange_algCM`, `algCM_mul`, `algCM_charFn`, `locallyConstant_eq_sum_smul_charFn`, `baseChange_cmul`, `baseChange_res` [theorem]; instances: 0)
- Key API (used by ≥3 in-file):
  - `baseChange` (def) — used by 5
  - `algCM` (def) — used by 6
  - `algCM_apply` — used by 2 (just under)
  - `baseChange_algCM` — used by `baseChange_cmul` (and the conceptual cornerstone)
  - `algCM_charFn` — used by 2
  - (Most leverage concentrates in the two defs `baseChange` and `algCM`.)
- Unused in file: `baseChange_dirac`, `algCM_mahler`, `baseChange_res` (all are public API consumed by other modules / the L-function construction).
- Decls with `sorry`: none.
- `set_option`: none.
- Proofs >50 lines (OVER-50): none (count: 0).
- Proofs 30-50 lines (long(30-50)): `baseChange_algCM` (count: 1) — ~30-line `calc` proof, the borderline case; candidate for `/decompose-proof` if the three `have`s (`hΔ`, `hcoeff`, `hsum`) are extracted as standalone lemmas.

Output path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_MeasureR_BaseChange.md`
