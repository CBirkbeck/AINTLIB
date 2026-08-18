# Inventory: PadicLFunctions/MeasureR/UnitsZp.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/MeasureR/UnitsZp.lean`

Namespace: `PadicLFunctions.MeasureR` (inside a `noncomputable section`).

Common context for all decls:
- `p : ℕ`, `[hp : Fact p.Prime]`
- `K : Type*`, `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`
- `R := integerRing K` throughout (the integer ring / valuation subring of `K`).

---

### def extendByZero
- Type: `extendByZero : C(ℤ_[p]ˣ, integerRing K) →ₗ[integerRing K] C(ℤ_[p], integerRing K)`
- What: Extension-by-zero linear map sending a continuous `R`-valued function `g` on the units `ℤ_[p]ˣ` to the continuous function on all of `ℤ_[p]` that equals `g` on units (via `IsUnit.unit`) and `0` elsewhere.
- How: The `toFun` packages `fun x => if h : IsUnit x then g h.unit else 0` with a continuity proof by cases on `IsUnit x`: on the clopen units it equals `g ∘ unitsHomeo.symm` (a `ContinuousOn` argument restricted to the open units, hinging on `PadicMeasure.isClopen_units` and `PadicMeasure.unitsHomeo`); on the open complement it is locally constant `0` via `ContinuousOn.congr continuousOn_const`. `map_add'`/`map_smul'` are proved by `ext` + case split on `IsUnit x`.
- Hypotheses: `g` a continuous `R`-valued function on `ℤ_[p]ˣ`; standard field/prime context.
- Uses from project: `PadicMeasure.isClopen_units`, `PadicMeasure.unitsHomeo`
- Used by: `extendByZero_coe_unit`, `extendByZero_comp_val`, `iota_injective`, `extendByZero_comp_unitsVal`, `mem_range_iota_iff` (and `extendByZero_comp_val` indirectly)
- Visibility: public
- Lines: 30–65 (def body ~33 lines; continuity proof ~23 lines)
- Notes: `open Classical in`; proof length ok (none OVER-50); uses `dif_pos`/`dif_neg`.

### lemma extendByZero_coe_unit
- Type: `extendByZero p K g (u : ℤ_[p]) = g u` for `g : C(ℤ_[p]ˣ, integerRing K)`, `u : ℤ_[p]ˣ`
- What: Evaluating the zero-extension of `g` at the image `(u : ℤ_[p])` of a unit `u` recovers `g u`.
- How: Rewrites the `dite` via `dif_pos u.isUnit`, then `congr 1` reduces to `Units.ext` applied to `IsUnit.unit_spec` (the chosen unit of `(u : ℤ_[p])` agrees with `u`).
- Hypotheses: `u` a unit of `ℤ_[p]`; `g` continuous `R`-valued on units.
- Uses from project: `extendByZero`
- Used by: `extendByZero_comp_val`
- Visibility: public
- Lines: 69–78 (proof ~7 lines)
- Notes: `open Classical in`; `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`; `@[simp]`; none.

### def iota
- Type: `iota : MeasureR K ℤ_[p]ˣ →ₗ[integerRing K] MeasureR K ℤ_[p]`
- What: The embedding `ι : Λ_R(ℤ_p^×) → Λ_R(ℤ_p)`, defined as the pushforward of `R`-valued measures along the unit-inclusion `ℤ_[p]ˣ → ℤ_[p]` (RJW Rem 3.33).
- How: Direct definition as `pushforward K ℤ_[p]ˣ ℤ_[p] (PadicMeasure.unitsValCM p)`.
- Hypotheses: standard field/prime context.
- Uses from project: `MeasureR`, `pushforward`, `PadicMeasure.unitsValCM`
- Used by: `extendByZero_comp_val`? (no), `iota_injective`, `res_iota`, `mem_range_iota_iff`
- Visibility: public
- Lines: 82–84 (def, 1 line)
- Notes: none.

### lemma extendByZero_comp_val
- Type: `(extendByZero p K g).comp (PadicMeasure.unitsValCM p) = g` for `g : C(ℤ_[p]ˣ, integerRing K)`
- What: Restricting the zero-extension of `g` back to the units (precompose with the unit-value map) recovers the original `g`.
- How: `ContinuousMap.ext` reduces to pointwise equality `extendByZero_coe_unit g u`.
- Hypotheses: `g` continuous `R`-valued on units.
- Uses from project: `extendByZero`, `extendByZero_coe_unit`, `PadicMeasure.unitsValCM`
- Used by: `iota_injective`
- Visibility: public
- Lines: 88–92 (proof, 1-term line)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`; none.

### theorem iota_injective
- Type: `Function.Injective (iota p K)`
- What: The embedding `ι` is injective (so `Λ_R(ℤ_p^×)` is identified with its image in `Λ_R(ℤ_p)`), RJW Rem 3.33.
- How: Given `iota μ = iota ν`, apply the functional equality at `extendByZero p K g` and simplify with `pushforward_apply` and `extendByZero_comp_val` (so both sides become `μ g`, `ν g`); uses `LinearMap.congr_fun` / `LinearMap.ext`.
- Hypotheses: standard field/prime context.
- Uses from project: `iota`, `extendByZero`, `pushforward` (`pushforward_apply`), `extendByZero_comp_val`
- Used by: unused in file
- Visibility: public
- Lines: 94–101 (proof ~5 lines)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`; none.

### theorem res_iota
- Type: `res p K (PadicMeasure.isClopen_units p) (iota p K μ) = iota p K μ` for `μ : MeasureR K ℤ_[p]ˣ`
- What: Restricting a pushed-forward unit-measure `ι μ` to the clopen set of units leaves it unchanged (`Res_{ℤ_p^×} ∘ ι = ι`), RJW Rem 3.33.
- How: `LinearMap.ext`; after `change`, reduces to showing the test functions agree, i.e. `(charFnCM · * f).comp unitsValCM = f.comp unitsValCM`; `ext u` + simp unfolds `charFnCM_apply`/`unitsValCM`, then `Set.indicator_of_mem` (using `u.isUnit ∈ {IsUnit}`) and `one_mul` finish.
- Hypotheses: `μ` an `R`-valued measure on `ℤ_[p]ˣ`.
- Uses from project: `res`, `iota`, `PadicMeasure.isClopen_units`, `charFnCM` (`charFnCM_apply`), `PadicMeasure.unitsValCM`
- Used by: `mem_range_iota_iff`
- Visibility: public
- Lines: 103–116 (proof ~10 lines)
- Notes: `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`; none.

### lemma extendByZero_comp_unitsVal
- Type: `extendByZero p K (f.comp (PadicMeasure.unitsValCM p)) = charFnCM K ℤ_[p] (PadicMeasure.isClopen_units p) * f` for `f : C(ℤ_[p], integerRing K)`
- What: Zero-extending the restriction of `f` to units equals multiplying `f` by the indicator (characteristic function) of the unit clopen — "cutting `f` by the unit indicator".
- How: `ext x`, reduce via `congrArg Subtype.val`, then case split on `IsUnit x`. On units: `dif_pos`, simp `charFnCM_apply`/`unitsValCM`, `Set.indicator_of_mem`, `one_mul`, `IsUnit.unit_spec`. Off units: `dif_neg`, `Set.indicator_of_notMem`, `zero_mul`.
- Hypotheses: `f` continuous `R`-valued on `ℤ_[p]`.
- Uses from project: `extendByZero`, `PadicMeasure.unitsValCM`, `charFnCM` (`charFnCM_apply`), `PadicMeasure.isClopen_units`
- Used by: `mem_range_iota_iff`
- Visibility: public
- Lines: 118–137 (proof ~16 lines)
- Notes: `open Classical in`; `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]`; none.

### theorem mem_range_iota_iff
- Type: `μ ∈ Set.range (iota p K) ↔ psi p K μ = 0` for `μ : MeasureR K ℤ_[p]`
- What: The image of `ι` is exactly `ker ψ`: a measure on `ℤ_[p]` is a pushforward of a unit-measure iff it is killed by `ψ` (RJW Rem 3.33 / Cor 3.32).
- How: `(→)` destructs `μ = iota ν`, rewrites with `← isSupportedOn_units_iff_psi_eq_zero` and closes via `res_iota ν`. `(←)` builds the preimage `μ.comp (extendByZero p K)`; `LinearMap.ext`, `change`, `extendByZero_comp_unitsVal`, then `(isSupportedOn_units_iff_psi_eq_zero μ).2 h` applied via `LinearMap.congr_fun`.
- Hypotheses: `μ` an `R`-valued measure on `ℤ_[p]`.
- Uses from project: `iota`, `psi`, `isSupportedOn_units_iff_psi_eq_zero`, `res_iota`, `extendByZero`, `extendByZero_comp_unitsVal`, `PadicMeasure.unitsValCM`
- Used by: unused in file
- Visibility: public
- Lines: 139–151 (proof ~11 lines)
- Notes: none.

---

## File Summary

- **Total declarations: 8** — defs: 2 (`extendByZero`, `iota`); lemmas+theorems: 6 (`extendByZero_coe_unit`, `extendByZero_comp_val`, `iota_injective`, `res_iota`, `extendByZero_comp_unitsVal`, `mem_range_iota_iff`); instances: 0; structures/classes: 0.
- **Key API (used by ≥3 decls in file):** `extendByZero` (used by 5: `extendByZero_coe_unit`, `extendByZero_comp_val`, `iota_injective`, `extendByZero_comp_unitsVal`, `mem_range_iota_iff`); `iota` (used by 3: `iota_injective`, `res_iota`, `mem_range_iota_iff`). Project-external heavily-reused: `PadicMeasure.unitsValCM` (5×), `PadicMeasure.isClopen_units` (4×), `charFnCM` (3×).
- **Unused in file:** `iota_injective`, `mem_range_iota_iff` (terminal/exported results — no in-file consumers).
- **Decls with `sorry`:** none.
- **`set_option`:** none. (`open Classical in` on 3 decls; `omit [CompleteSpace K] [NormedAlgebra ℚ_[p] K]` on 6 decls.)
- **Proofs >50 lines (OVER-50):** none (count 0).
- **Proofs 30–50 lines (long):** none (count 0). Longest proof is `extendByZero`'s continuity obligation at ~23 lines.
