# Inventory: PadicLFunctions/MeasureR/Convolution.lean

File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/MeasureR/Convolution.lean`

Module context: RJW §3.3 over `R := integerRing K`. Builds the Iwasawa algebra `Λ_R(ℤ_p) = ℳ(ℤ_p, R)` as a commutative ring by transporting `R⟦T⟧`'s ring structure along the Mahler equivalence, gives the ring isomorphism `MeasureR K ℤ_[p] ≃+* R⟦T⟧`, and proves the convolution formula on the Mahler basis via Chu–Vandermonde. Mirrors the `ℤ_p`-layer `PadicLFunctions/Measure/Convolution.lean`.

Section variables: `p : ℕ` `[Fact p.Prime]`; `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`. Everything lives in `noncomputable section`, `namespace PadicLFunctions.MeasureR`.

---

### instance (Mul) `instMulMeasureR` (anonymous `Mul (MeasureR K ℤ_[p])`)
- Type: `instance : Mul (MeasureR K ℤ_[p])`
- What: Defines multiplication of two `R`-valued measures on `ℤ_p` by pulling them through the Mahler linear equivalence to `R⟦T⟧`, multiplying there, and pulling back via the inverse equivalence.
- How: Direct anonymous-constructor definition `μ ν ↦ (mahlerLinearEquiv p K).symm (mahlerLinearEquiv p K μ * mahlerLinearEquiv p K ν)` — transport of structure along `mahlerLinearEquiv`.
- Hypotheses: Full section variables (`K` a complete normed `ℚ_[p]`-algebra, ultrametric).
- Uses from project: [`mahlerLinearEquiv`]
- Used by: `mul_def`, `mahlerTransform_mul`, `CommRing` instance (and transitively all multiplicative results)
- Visibility: public
- Lines: 38–40 (definition body 2 lines)
- Notes: none

### instance (One) `instOneMeasureR` (anonymous `One (MeasureR K ℤ_[p])`)
- Type: `instance : One (MeasureR K ℤ_[p])`
- What: Defines the multiplicative identity of the measure algebra to be the Dirac measure at `0`.
- How: Anonymous constructor `⟨dirac K ℤ_[p] 0⟩`.
- Hypotheses: Full section variables.
- Uses from project: [`dirac`]
- Used by: `one_def`, `mahlerTransform_one`
- Visibility: public
- Lines: 42 (1 line)
- Notes: none

### lemma `mul_def`
- Type: `(μ ν : MeasureR K ℤ_[p]) : μ * ν = (mahlerLinearEquiv p K).symm (mahlerLinearEquiv p K μ * mahlerLinearEquiv p K ν)`
- What: Unfolds the definition of measure multiplication to its transported-from-`R⟦T⟧` formula.
- How: `rfl` — the `Mul` instance is definitionally this expression.
- Hypotheses: Full section variables; `μ ν` arbitrary measures.
- Uses from project: [`mahlerLinearEquiv`] (via `Mul` instance)
- Used by: `mahlerTransform_mul`, `mul_apply`
- Visibility: public
- Lines: 46–48 (proof 1 line, `rfl`)
- Notes: none

### lemma `one_def`
- Type: `(1 : MeasureR K ℤ_[p]) = dirac K ℤ_[p] 0`
- What: Identifies the ring `1` of the measure algebra with the Dirac measure at `0`.
- How: `rfl` — the `One` instance is definitionally `dirac K ℤ_[p] 0`.
- Hypotheses: Full section variables minus `[NormedAlgebra ℚ_[p] K]` and `[CompleteSpace K]` (both `omit`ted).
- Uses from project: [`dirac`] (via `One` instance)
- Used by: `mahlerTransform_one`
- Visibility: public
- Lines: 50–51 (proof 1 line, `rfl`); has `omit` clause
- Notes: none

### theorem `mahlerTransform_mul`
- Type: `(μ ν : MeasureR K ℤ_[p]) : mahlerTransform p K (μ * ν) = mahlerTransform p K μ * mahlerTransform p K ν`
- What: The Mahler transform is multiplicative (sends measure convolution to power-series product).
- How: Rewrites through `mul_def`, then uses `mahlerLinearEquiv_apply` (identifying `mahlerTransform` with the equiv) and `LinearEquiv.apply_symm_apply` to cancel the symm/forward round-trip.
- Hypotheses: Full section variables; `μ ν` arbitrary.
- Uses from project: [`mahlerTransform`, `mahlerLinearEquiv_apply`, `mul_def` (via `mul_def` rewrite)]
- Used by: `mahlerRingEquiv`, `mul_apply`, `dirac_mul_dirac`, the `CommRing` instance (all eight field proofs `simp` on it)
- Visibility: public; `@[simp]`
- Lines: 53–58 (proof 2 lines)
- Notes: none

### theorem `mahlerTransform_one`
- Type: `mahlerTransform p K (1 : MeasureR K ℤ_[p]) = 1`
- What: The Mahler transform sends the ring identity (Dirac at `0`) to the power-series `1`.
- How: Rewrites `one_def`, then `mahlerTransform_dirac` (transform of a Dirac is a binomial series), `binomialSeries_zero` (the `0`-binomial series is `1`), `map_one`.
- Hypotheses: Full section variables minus `[CompleteSpace K]` (`omit`ted).
- Uses from project: [`mahlerTransform`, `one_def`, `mahlerTransform_dirac`, `binomialSeries_zero`]
- Used by: `CommRing` instance (`one_mul`, `mul_one` via `simp`)
- Visibility: public; `@[simp]`
- Lines: 60–63 (proof 1 line); has `omit` clause
- Notes: none

### theorem `mahlerTransform_add`
- Type: `(μ ν : MeasureR K ℤ_[p]) : mahlerTransform p K (μ + ν) = mahlerTransform p K μ + mahlerTransform p K ν`
- What: The Mahler transform is additive.
- How: `ext n` then `simp` — additivity reduces coefficientwise to the linearity already known of the transform.
- Hypotheses: Full section variables minus `[CompleteSpace K]` (`omit`ted); `μ ν` arbitrary.
- Uses from project: [`mahlerTransform`]
- Used by: `CommRing` instance (`left_distrib`, `right_distrib`, `zero_mul`, `mul_zero` via `simp`)
- Visibility: public; `@[simp]`
- Lines: 65–70 (proof 2 lines); has `omit` clause
- Notes: none

### theorem `mahlerTransform_zero`
- Type: `mahlerTransform p K (0 : MeasureR K ℤ_[p]) = 0`
- What: The Mahler transform sends the zero measure to the zero power series.
- How: `ext n` then `simp` — coefficientwise the transform of `0` vanishes.
- Hypotheses: Full section variables minus `[CompleteSpace K]` (`omit`ted).
- Uses from project: [`mahlerTransform`]
- Used by: `CommRing` instance (`zero_mul`, `mul_zero` via `simp`)
- Visibility: public; `@[simp]`
- Lines: 72–76 (proof 2 lines); has `omit` clause
- Notes: none

### instance (CommRing) `instCommRingMeasureR` (anonymous `CommRing (MeasureR K ℤ_[p])`)
- Type: `instance : CommRing (MeasureR K ℤ_[p])`
- What: Equips the measure algebra `Λ_R(ℤ_p)` with a commutative ring structure, all laws inherited from `R⟦T⟧` through the Mahler bijection (RJW Rem 3.11).
- How: Each ring axiom (`mul_assoc`, `one_mul`, `mul_one`, distributivity, `zero_mul`, `mul_zero`, `mul_comm`) is discharged by `mahlerTransform_injective` applied to a `simp`-closed goal that transports the axiom to `R⟦T⟧` (e.g. `mul_assoc` via `simp [mul_assoc]`); hinges on injectivity of the transform plus the `@[simp]` lemmas `mahlerTransform_mul/_one/_add/_zero`.
- Hypotheses: Full section variables; the additive group / module structure on `MeasureR` is presupposed (only multiplicative + distributive + identity fields are supplied here).
- Uses from project: [`mahlerTransform_injective`, `mahlerTransform_mul`, `mahlerTransform_one`, `mahlerTransform_add`, `mahlerTransform_zero`]
- Used by: `mahlerRingEquiv`, `mul_apply`, `dirac_mul_dirac` (all rely on the ring structure)
- Visibility: public
- Lines: 80–90 (8 axiom proofs, each 1 line; total body ~8 lines)
- Notes: none

### def `mahlerRingEquiv`
- Type: `mahlerRingEquiv : MeasureR K ℤ_[p] ≃+* PowerSeries (integerRing K)`
- What: RJW Theorem 3.20 over `R`: the Mahler transform packaged as a ring isomorphism `ℳ(ℤ_p, 𝒪_L) ≅ 𝒪_L⟦T⟧`.
- How: Extends the linear equivalence `mahlerLinearEquiv p K` with the multiplicativity field `map_mul' := mahlerTransform_mul`.
- Hypotheses: Full section variables.
- Uses from project: [`mahlerLinearEquiv`, `mahlerTransform_mul`]
- Used by: unused in file
- Visibility: public
- Lines: 92–96 (definition body 2 lines)
- Notes: none

### def `convInner`
- Type: `(ν : MeasureR K ℤ_[p]) (f : C(ℤ_[p], integerRing K)) : C(ℤ_[p], integerRing K)`
- What: The inner-convolution integrand `x ↦ ∫ f(x+y) dν(y)`, returning a continuous function of `x` valued in `R`.
- How: `toFun x := ν (f.comp ⟨fun y => x+y, …⟩)`; continuity proved by rewriting the family of composed maps as `ContinuousMap.curry` of the jointly-continuous `(x,y) ↦ f(x+y)` (lemma `key` via `ContinuousMap.ext`), then composing `MeasureR.continuous ν` with `map_continuous` of the curried map.
- Hypotheses: Full section variables; `ν` a measure, `f` a continuous `R`-valued function.
- Uses from project: [`MeasureR.continuous`] (and `MeasureR` application/`ContinuousMap` infrastructure)
- Used by: `convInner_apply`, `mul_apply`
- Visibility: public
- Lines: 98–107 (proof of continuity ~6 lines)
- Notes: none

### lemma `convInner_apply`
- Type: `(ν : MeasureR K ℤ_[p]) (f : C(ℤ_[p], integerRing K)) (x : ℤ_[p]) : convInner p K ν f x = ν (f.comp ⟨fun y => x + y, by fun_prop⟩)`
- What: Computes the value of the inner-convolution integrand at a point `x` as the measure `ν` applied to the shifted function.
- How: `rfl` — unfolds `convInner.toFun`.
- Hypotheses: Full section variables minus `[NormedAlgebra ℚ_[p] K]` and `[CompleteSpace K]` (both `omit`ted).
- Uses from project: [`convInner`]
- Used by: `mul_apply` (inside the `key` computation)
- Visibility: public; `@[simp]`
- Lines: 111–114 (proof 1 line, `rfl`); has `omit` clause
- Notes: none

### theorem `mul_apply`
- Type: `(μ ν : MeasureR K ℤ_[p]) (f : C(ℤ_[p], integerRing K)) : (μ * ν) f = μ (convInner p K ν f)`
- What: The convolution formula over `R` (RJW Rem 3.11): integrating `f` against the product measure equals integrating against `μ` the inner convolution `x ↦ ∫ f(x+y) dν(y)`.
- How: Constructs the candidate measure `ρ := f ↦ μ(convInner ν f)` (proving its additivity/`smul`-linearity via `ContinuousMap.add_comp`/`smul_comp`), reduces `μ*ν = ρ` to equality after `mahlerTransform_injective`, and checks coefficientwise. The core is Chu–Vandermonde: `Ring.add_choose_eq` expands `mahlerCM p K n` composed with the shift `y ↦ x+y` as `∑_{(i,j)} Ring.choose x i • mahlerCM p K j` (lemma `hcomp`), feeding `coeff_mahlerTransform` and `PowerSeries.coeff_mul` on both sides; `algebraMap`/`Algebra.smul_def` move scalars through the `R = integerRing K` algebra map.
- Hypotheses: Full section variables; `μ ν` measures, `f` continuous `R`-valued.
- Uses from project: [`MeasureR`, `convInner`, `convInner_apply`, `mahlerTransform_mul`, `mahlerTransform_injective`, `coeff_mahlerTransform`, `mahlerCM`, `mahlerCM_apply`, `mul_def` (via construction)]
- Used by: unused in file
- Visibility: public
- Lines: 116–160 (proof ~41 lines)
- Notes: long(30-50) — proof is ~41 lines; relies on Chu–Vandermonde (`Ring.add_choose_eq`) and could be a `/decompose-proof` candidate; no `sorry`/`set_option`/`TODO`

### theorem `dirac_mul_dirac`
- Type: `(a b : ℤ_[p]) : dirac K ℤ_[p] a * dirac K ℤ_[p] b = dirac K ℤ_[p] (a + b)`
- What: The product of Dirac measures at `a` and `b` is the Dirac measure at `a+b` (`[a]·[b] = [a+b]`, RJW Ex 3.12/3.16).
- How: `mahlerTransform_injective`, then rewrite both sides' transforms via `mahlerTransform_mul` and three `mahlerTransform_dirac`, and use `binomialSeries_add` (binomial series multiply additively in the exponent) with `← map_mul`.
- Hypotheses: Full section variables; `a b` arbitrary `p`-adic integers.
- Uses from project: [`dirac`, `mahlerTransform_injective`, `mahlerTransform_mul`, `mahlerTransform_dirac`, `binomialSeries_add`]
- Used by: unused in file
- Visibility: public; `@[simp]`
- Lines: 162–168 (proof 3 lines)
- Notes: none

---

## File Summary

- **Total declarations: 14** — defs: 2 (`mahlerRingEquiv`, `convInner`); lemmas+theorems: 9 (`mul_def`, `one_def`, `mahlerTransform_mul`, `mahlerTransform_one`, `mahlerTransform_add`, `mahlerTransform_zero`, `convInner_apply`, `mul_apply`, `dirac_mul_dirac`); instances: 3 (`Mul`, `One`, `CommRing`).
- **Key API (used by ≥3 in-file):**
  - `mahlerTransform_mul` — used by `mahlerRingEquiv`, `mul_apply`, `dirac_mul_dirac`, and all 8 `CommRing` axiom proofs.
  - `mahlerTransform_injective` (project-external, from MahlerTransform) — used by the `CommRing` instance, `mul_apply`, `dirac_mul_dirac`.
  - The Mul/One instances and `mahlerLinearEquiv` underpin most multiplicative results.
- **Unused in file (likely public API exported upward):** `mahlerRingEquiv`, `mul_apply`, `dirac_mul_dirac` (the three headline "Main results", consumed by other modules), plus `mahlerTransform_add`/`mahlerTransform_zero`/`mahlerTransform_one`/`convInner_apply` used only within `CommRing`/`mul_apply`.
- **Declarations with `sorry`: none.**
- **`set_option`: none.**
- **Proofs >50 lines (OVER-50): 0.**
- **Proofs 30–50 lines (long): 1** — `mul_apply` (~41 lines, lines 116–160; Chu–Vandermonde core, `/decompose-proof` candidate).
- **TODO markers: none.**

Output path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_MeasureR_Convolution.md`
