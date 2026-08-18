# Inventory: PadicLFunctions/MeasureR/Basic.lean

Path: `/Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/PadicLFunctions/MeasureR/Basic.lean`

Header context: the coefficient-general layer of the measure theory of RJW §3, for a nonarchimedean normed field `K` with integer ring `R := integerRing K`. An `R`-valued measure on a compact space `X` is an `R`-linear functional on `C(X, R)`. Imports `PadicLFunctions.Coefficients` and `PadicLFunctions.Measure.Fubini`.

File-level variables: `(K : Type*) [NormedField K] [IsUltrametricDist K]`, `(X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]`. Inside `section compact`: `{K X}` made implicit and `[CompactSpace X]` added.

---

### abbrev MeasureR
- Type: `abbrev MeasureR := C(X, integerRing K) →ₗ[integerRing K] integerRing K`
- What: An `integerRing K`-valued measure on `X`, defined as an `integerRing K`-linear functional on the continuous `integerRing K`-valued functions on `X` (RJW Def 3.6 with the `𝒪_L`-integrality convention).
- How: A reducible abbreviation for the linear-map type, so mathlib's `LinearMap` API applies transparently (mirroring the `ℤ_p` case).
- Hypotheses: `K` a nonarchimedean (ultrametric) normed field; `X` a topological space.
- Uses from project: [`integerRing`]
- Used by: `dirac`, `compRight`, `pushforward`, `pushforward_apply`, `pushforward_dirac`, `charFnCM`, `charFnCM_apply`, `norm_apply_le`, `continuous`, `ext_locallyConstant`
- Visibility: public
- Lines: 46–50 (no proof; abbrev)
- Notes: none

### def dirac
- Type: `def dirac (x : X) : MeasureR K X` (record: `toFun f := f x`, `map_add'`, `map_smul'`)
- What: The Dirac measure at a point `x : X`, i.e. evaluation of a continuous function at `x` (RJW Ex. 3.7).
- How: Bundles the evaluation functional `f ↦ f x` as a linear map; additivity and `integerRing K`-linearity hold by `rfl`.
- Hypotheses: `x` a point of `X`.
- Uses from project: [`MeasureR`]
- Used by: `dirac_apply`, `pushforward_dirac`
- Visibility: public
- Lines: 54–58 (proof: 2 `rfl` field-fillers)
- Notes: none

### lemma dirac_apply
- Type: `lemma dirac_apply (x : X) (f : C(X, integerRing K)) : dirac K X x f = f x`
- What: Computes the Dirac measure at `x` applied to `f` as the value `f x`.
- How: Definitional unfolding; proved by `rfl`. Tagged `@[simp]`.
- Hypotheses: `x : X`, `f` a continuous `integerRing K`-valued function.
- Uses from project: [`dirac`]
- Used by: unused in file
- Visibility: public
- Lines: 60–61 (proof: `rfl`, 1 line)
- Notes: none

### def compRight
- Type: `def compRight (m : C(X, Y)) : C(Y, integerRing K) →ₗ[integerRing K] C(X, integerRing K)` (record with `toFun f := f.comp m`)
- What: Precomposition with a continuous map `m : X → Y`, sending `f : C(Y, R)` to `f ∘ m : C(X, R)`; auxiliary for `pushforward`.
- How: Bundles `f ↦ f.comp m` as a linear map; `map_add'`/`map_smul'` proved pointwise by `ext; simp`.
- Hypotheses: `m` a continuous map `X → Y`.
- Uses from project: [] (uses `integerRing` only via the type; no project decl referenced in body)
- Used by: `compRight_apply`, `pushforward`
- Visibility: public
- Lines: 63–68 (proof: 2 one-line `ext; simp` field-fillers)
- Notes: none

### lemma compRight_apply
- Type: `lemma compRight_apply (m : C(X, Y)) (f : C(Y, integerRing K)) : compRight K X Y m f = f.comp m`
- What: Computes `compRight … m` applied to `f` as the composite `f.comp m`.
- How: Definitional unfolding; `rfl`. Tagged `@[simp]`.
- Hypotheses: `m : C(X, Y)`, `f : C(Y, integerRing K)`.
- Uses from project: [`compRight`]
- Used by: unused in file
- Visibility: public
- Lines: 70–72 (proof: `rfl`, 1 line)
- Notes: none

### def pushforward
- Type: `def pushforward (m : C(X, Y)) : MeasureR K X →ₗ[integerRing K] MeasureR K Y` (record with `toFun μ := μ.comp (compRight K X Y m)`)
- What: Pushforward of a measure along a continuous map `m : X → Y`, sending `μ` to the measure `f ↦ μ (f ∘ m)` (RJW §3.5.4 / Rem 3.33).
- How: Postcomposes a measure with `compRight K X Y m` as a linear map; `map_add'`/`map_smul'` hold by `rfl`.
- Hypotheses: `m` a continuous map `X → Y`.
- Uses from project: [`MeasureR`, `compRight`]
- Used by: `pushforward_apply`, `pushforward_dirac`
- Visibility: public
- Lines: 74–79 (proof: 2 `rfl` field-fillers)
- Notes: none

### lemma pushforward_apply
- Type: `lemma pushforward_apply (m : C(X, Y)) (μ : MeasureR K X) (f : C(Y, integerRing K)) : pushforward K X Y m μ f = μ (f.comp m)`
- What: Computes the pushforward measure applied to `f` as `μ` evaluated at `f.comp m`.
- How: Definitional unfolding; `rfl`. Tagged `@[simp]`.
- Hypotheses: `m : C(X, Y)`, `μ` a measure on `X`, `f : C(Y, integerRing K)`.
- Uses from project: [`pushforward`, `MeasureR`]
- Used by: unused in file
- Visibility: public
- Lines: 81–83 (proof: `rfl`, 1 line)
- Notes: none

### lemma pushforward_dirac
- Type: `lemma pushforward_dirac (m : C(X, Y)) (x : X) : pushforward K X Y m (dirac K X x) = dirac K Y (m x)`
- What: The pushforward of a Dirac measure at `x` along `m` is the Dirac measure at `m x` (functoriality of Dirac).
- How: Both sides reduce to evaluation `f ↦ f (m x)`; `rfl`. Tagged `@[simp]`.
- Hypotheses: `m : C(X, Y)`, `x : X`.
- Uses from project: [`pushforward`, `dirac`]
- Used by: unused in file
- Visibility: public
- Lines: 85–87 (proof: `rfl`, 1 line)
- Notes: none

### def charFnCM
- Type: `noncomputable def charFnCM {U : Set X} (hU : IsClopen U) : C(X, integerRing K)` `:= (LocallyConstant.charFn (integerRing K) hU : C(X, integerRing K))`
- What: The indicator (characteristic) function of a clopen subset `U`, valued in `integerRing K`, as a continuous map.
- How: Coerces mathlib's `LocallyConstant.charFn (integerRing K) hU` (parametric in the value ring) to a `ContinuousMap`.
- Hypotheses: `U` a clopen subset of `X` (`IsClopen U`).
- Uses from project: [] (mathlib `LocallyConstant.charFn`; `integerRing` only via the type)
- Used by: `charFnCM_apply`
- Visibility: public (noncomputable)
- Lines: 89–92 (no tactic proof; direct term)
- Notes: none

### lemma charFnCM_apply
- Type: `lemma charFnCM_apply {U : Set X} (hU : IsClopen U) (x : X) : charFnCM K X hU x = U.indicator 1 x`
- What: Evaluates the clopen indicator at `x` as the set indicator `U.indicator 1 x`.
- How: Definitional unfolding of `charFn`; `rfl`. Tagged `@[simp]`.
- Hypotheses: `U` clopen in `X`, `x : X`.
- Uses from project: [`charFnCM`]
- Used by: unused in file
- Visibility: public
- Lines: 94–96 (proof: `rfl`, 1 line)
- Notes: none

### theorem norm_apply_le
- Type: `theorem norm_apply_le (μ : MeasureR K X) (f : C(X, integerRing K)) : ‖μ f‖ ≤ ‖f‖`
- What: **Automatic boundedness**: every `integerRing K`-linear functional on `C(X, integerRing K)` over a compact `X` has operator norm at most one, i.e. `‖μ f‖ ≤ ‖f‖` (RJW Def 3.6 footnote).
- How: Case-splits on `X` empty/nonempty and `f = 0`/`f ≠ 0`; for the main case the sup norm is attained at some `x₀` via `isCompact_univ.exists_isMaxOn`, then writes `f = f x₀ • g` where `g x = (f x)/(f x₀)` has all values in the unit ball (`hbound`), so `μ f = f x₀ * μ g` with `‖μ g‖ ≤ 1` (integrality of `μ g`), and `‖f‖ = ‖f x₀‖`; concludes by `mul_le_mul_of_nonneg_left`. Hinges on `IsCompact.exists_isMaxON`, `ContinuousMap.norm_le`, `ContinuousMap.norm_coe_le_norm`, and the membership-norm bound `(μ g).2`.
- Hypotheses: `X` compact; `μ` an `integerRing K`-valued measure; `f` a continuous `integerRing K`-valued function. (Ambient field `K` ultrametric normed.)
- Uses from project: [`MeasureR`]
- Used by: `continuous`, `ext_locallyConstant`
- Visibility: public (in `section compact`)
- Lines: 102–144 (proof body ~36 lines, 108–144)
- Notes: long(30-50) — proof is ~36 lines (needs review/possible decompose); no sorry / set_option / TODO.

### theorem continuous
- Type: `theorem continuous (μ : MeasureR K X) : Continuous μ`
- What: Every `integerRing K`-valued measure on a compact `X` is automatically continuous as a function `C(X, integerRing K) → integerRing K` (TeX 765).
- How: Shows `μ` is `LipschitzWith 1` via `LipschitzWith.of_dist_le_mul`, rewriting distances as norms and reducing `‖μ f − μ g‖ = ‖μ (f − g)‖` (using `← map_sub`) bounded by `‖f − g‖` through `norm_apply_le`; `.continuous` extracts continuity.
- Hypotheses: `X` compact; `μ` a measure.
- Uses from project: [`MeasureR`, `norm_apply_le`]
- Used by: unused in file
- Visibility: public (in `section compact`)
- Lines: 146–150 (proof: ~4 lines, term-mode with inline tactic)
- Notes: none

### theorem ext_locallyConstant
- Type: `theorem ext_locallyConstant {μ ν : MeasureR K X} (h : ∀ Φ : LocallyConstant X (integerRing K), μ Φ.toContinuousMap = ν Φ.toContinuousMap) : μ = ν`
- What: Two measures that agree on all locally constant functions are equal (the density half of RJW Rem 3.8).
- How: Reduces to showing `μ f = ν f` for every `f` via `LinearMap.ext` and `eq_of_forall_dist_le`; for `ε > 0` picks a locally constant `Φ` with `‖f − Φ‖ ≤ ε` using `PadicMeasure.exists_locallyConstant_norm_sub_le'`, rewrites `μ f − ν f = μ(f − Φ) + −(ν(f − Φ))` (the `Φ`-terms cancel by `h`), and bounds via the ultrametric `IsUltrametricDist.norm_add_le_max` together with `norm_apply_le` applied to `μ` and `ν`. Hinges on `PadicMeasure.exists_locallyConstant_norm_sub_le'` and `norm_apply_le`.
- Hypotheses: `X` compact; `μ, ν` measures agreeing on every locally constant `integerRing K`-valued function.
- Uses from project: [`MeasureR`, `PadicMeasure.exists_locallyConstant_norm_sub_le'`, `norm_apply_le`]
- Used by: unused in file
- Visibility: public (in `section compact`)
- Lines: 152–168 (proof body ~11 lines, 158–168)
- Notes: none

---

## File Summary

- **Total declarations: 12** — defs: 4 (`dirac`, `compRight`, `pushforward`, `charFnCM`) + 1 abbrev (`MeasureR`); lemmas+theorems: 7 (`dirac_apply`, `compRight_apply`, `pushforward_apply`, `pushforward_dirac`, `charFnCM_apply`, `norm_apply_le`, `continuous`, `ext_locallyConstant` — i.e. 4 `@[simp]` computation lemmas + 3 substantive theorems + `charFnCM_apply`); instances: 0; structures/classes/inductives: 0. (Counting `MeasureR` abbrev separately: 1 abbrev + 4 defs + 7 lemmas/theorems = 12.)
- **Key API (used by ≥3 in this file):** `MeasureR` (referenced by 10 decls); `norm_apply_le` (used by `continuous`, `ext_locallyConstant`). No other decl reaches 3 in-file users.
- **Unused in file:** `dirac_apply`, `compRight_apply`, `pushforward_apply`, `pushforward_dirac`, `charFnCM_apply`, `continuous`, `ext_locallyConstant` (these are public API for downstream files / other modules). `dirac`, `compRight`, `pushforward`, `charFnCM`, `MeasureR` are used internally.
- **Decls with sorry:** none.
- **set_option:** none.
- **Proofs >50 lines (OVER-50):** none (count: 0).
- **Proofs 30–50 lines:** 1 — `norm_apply_le` (~36 lines).
- **External-project dependency note:** `ext_locallyConstant` depends on `PadicMeasure.exists_locallyConstant_norm_sub_le'` (the `ℤ_p`/general approximation lemma from another module).
