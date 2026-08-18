# Inventory: PadicLFunctions/MeasureR/Fubini.lean

File-level context: Fubini for `MeasureR K`-measures over `R := integerRing K`,
where `K` is a complete ultrametric normed `ℚ_[p]`-algebra. Implements the "one
checks" of RJW Rem 3.11 (TeX 910): the two iterated integrals of a continuous
`F : C(X × Y, integerRing K)` against measures `μ` on `X` and `ν` on `Y` agree.
Mirrors the `ℤ_p`-layer `PadicLFunctions/Measure/Fubini.lean`.

Namespaces: `PadicLFunctions.MeasureR`. Section is `noncomputable`.
Module variables: `p : ℕ` `[Fact p.Prime]`; `K` a `NormedField` with
`[NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K]`;
`X Y : Type*` topological spaces.

---

### def innerInt
- Type: `[CompactSpace Y] (ν : MeasureR K Y) (F : C(X × Y, integerRing K)) : C(X, integerRing K)`
- What: The inner (partial) integral `x ↦ ∫ F(x, y) dν(y) = ν (F.curry x)`, packaged as a continuous map `X → integerRing K`.
- How: Builds the `ContinuousMap` from `fun x => ν (F.curry x)`; continuity is the composition of `MeasureR.continuous ν` with `map_continuous F.curry` (the currying map `X → C(Y, integerRing K)` is continuous).
- Hypotheses: `Y` compact (so `F.curry x` is a continuous map on a compact space, integrable against `ν`); `ν` a `MeasureR K Y`.
- Uses from project: `MeasureR`, `integerRing`, `MeasureR.continuous`
- Used by: `innerInt_apply`, `innerInt_add`, `innerInt_smul`, `innerInt_measure_add`, `innerInt_measure_zero`, `integral_swap`
- Visibility: public
- Lines: 31-34 (definition body 1 line)
- Notes: none

### lemma innerInt_apply
- Type: `[CompactSpace Y] (ν : MeasureR K Y) (F : C(X × Y, integerRing K)) (x : X) : innerInt K ν F x = ν (F.curry x)`
- What: Definitional unfolding: applying `innerInt K ν F` at `x` equals `ν (F.curry x)`.
- How: `rfl` (the `ContinuousMap` coercion reduces to its defining function).
- Hypotheses: `Y` compact; `ν` a measure; `x : X`.
- Uses from project: `innerInt`, `MeasureR`, `integerRing`
- Used by: `integral_swap` (used in both `hL` and `hR` error bounds)
- Visibility: public
- Lines: 38-41 (proof: `rfl`)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### lemma innerInt_add
- Type: `[CompactSpace Y] (ν : MeasureR K Y) (F G : C(X × Y, integerRing K)) : innerInt K ν (F + G) = innerInt K ν F + innerInt K ν G`
- What: `innerInt` is additive in the integrand `F`.
- How: `ContinuousMap.ext` pointwise, then `simp` using the fact `(F + G).curry x = F.curry x + F.curry x` (definitional `rfl`) plus `map_add` of the measure `ν`.
- Hypotheses: `Y` compact; `ν` a measure; `F G` integrands.
- Uses from project: `innerInt`, `MeasureR`, `integerRing`
- Used by: unused in file
- Visibility: public
- Lines: 43-48 (proof 2 lines)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### lemma innerInt_smul
- Type: `[CompactSpace Y] (c : integerRing K) (ν : MeasureR K Y) (F : C(X × Y, integerRing K)) : innerInt K ν (c • F) = c • innerInt K ν F`
- What: `innerInt` is `integerRing K`-linear (commutes with scalar multiplication) in the integrand.
- How: `ContinuousMap.ext` pointwise, then `simp` using `(c • F).curry x = c • F.curry x` (definitional `rfl`) plus `map_smul` of `ν`.
- Hypotheses: `Y` compact; scalar `c : integerRing K`; `ν` a measure; `F` integrand.
- Uses from project: `innerInt`, `integerRing`, `MeasureR`
- Used by: unused in file
- Visibility: public
- Lines: 50-56 (proof 2 lines)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### lemma innerInt_measure_add
- Type: `[CompactSpace Y] (ν₁ ν₂ : MeasureR K Y) (F : C(X × Y, integerRing K)) : innerInt K (ν₁ + ν₂) F = innerInt K ν₁ F + innerInt K ν₂ F`
- What: `innerInt` is additive in the measure argument `ν`.
- How: `ContinuousMap.ext` pointwise; each point reduces by `rfl` (`(ν₁ + ν₂)` applied to `F.curry x` is by definition `ν₁ (F.curry x) + ν₂ (F.curry x)`).
- Hypotheses: `Y` compact; measures `ν₁ ν₂`; `F` integrand.
- Uses from project: `innerInt`, `MeasureR`, `integerRing`
- Used by: unused in file
- Visibility: public
- Lines: 58-63 (proof 1 line, `rfl` per point)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### lemma innerInt_measure_zero
- Type: `[CompactSpace Y] (F : C(X × Y, integerRing K)) : innerInt K (0 : MeasureR K Y) F = 0`
- What: The inner integral against the zero measure is the zero map.
- How: `ContinuousMap.ext` pointwise; each point reduces by `rfl` (zero measure sends every map to `0`).
- Hypotheses: `Y` compact; `F` integrand.
- Uses from project: `innerInt`, `MeasureR`, `integerRing`
- Used by: unused in file
- Visibility: public
- Lines: 65-69 (proof 1 line, `rfl` per point)
- Notes: `omit [CompleteSpace K]`; `@[simp]`

### theorem integral_swap
- Type: `[CompactSpace X] [CompactSpace Y] (μ : MeasureR K X) (ν : MeasureR K Y) (F : C(X × Y, integerRing K)) : μ (innerInt K ν F) = ν (innerInt K μ (F.comp ⟨Prod.swap, continuous_swap⟩))`
- What: **Fubini over `R`** (RJW Rem 3.11, TeX 910): the two iterated integrals of `F` — integrate `y` first then `x`, vs. integrate `x` first then `y` (after swapping coordinates) — coincide.
- How: Ultrametric `ε`-approximation argument. `eq_of_forall_dist_le` reduces to bounding the distance by every `ε > 0`. Get a locally constant `Φ` with `‖F.curry - Φ‖ ≤ ε` via `PadicMeasure.exists_locallyConstant_norm_sub_le'`. Let `R` be `Φ`'s finite range; define the common finite sum `S = ∑_{g ∈ R} μ(charFn of fiber Φ⁻¹{g}) · ν(g)`. A pointwise collapse lemma (`hcollapse`, via `Finset.sum_eq_single`) shows the characteristic-function sum picks out only the `g = Φ x` term. Then both sides are within `ε` of `S`: LHS via intermediate `mid₁ = ∑ ν(g) • charFn(fiber g)` with `μ mid₁ = S` and `‖innerInt ν F − mid₁‖ ≤ ε` (hinging on `norm_apply_le ν` and `hΦ`); RHS symmetrically via `mid₂ = ∑ μ(charFn(fiber g)) • g` (hinging on `norm_apply_le μ`, then `norm_apply_le ν`/`hΦ` again). Closed by the ultrametric `dist_triangle_max` plus `max_le`.
- Hypotheses: `X`, `Y` both compact; `μ` a `MeasureR K X`, `ν` a `MeasureR K Y`; `F` a continuous integrand on `X × Y`. (Implicitly uses `‖μ‖, ‖ν‖ ≤ 1`, realized via `norm_apply_le`.)
- Uses from project: `MeasureR`, `integerRing`, `innerInt`, `innerInt_apply`, `PadicMeasure.exists_locallyConstant_norm_sub_le'`, `charFnCM`, `charFnCM_apply`, `norm_apply_le`
- Used by: unused in file
- Visibility: public
- Lines: 71-178 (proof ~102 lines)
- Notes: OVER-50 (proof ~102 lines; candidate for `/decompose-proof`). `omit [CompleteSpace K]`. Uses `classical`. Internal structure: `hcollapse` (pointwise collapse), `hL` (LHS ≈ S), `hR` (RHS ≈ S), final `calc` via `dist_triangle_max`. No `sorry`/`set_option`/`TODO`.

---

## File Summary

- **Total declarations: 7** — defs: 1 (`innerInt`); lemmas/theorems: 6 (5 `innerInt_*` simp lemmas + `integral_swap`); instances: 0; structures/classes/abbrevs/inductives: 0.
- **Key API (used by ≥3 in-file):** `innerInt` (def) — referenced by all 5 simp lemmas and `integral_swap` (6 in-file consumers). No other decl reaches the ≥3 threshold internally (`innerInt_apply` is used twice inside `integral_swap`).
- **Unused in file:** `innerInt_add`, `innerInt_smul`, `innerInt_measure_add`, `innerInt_measure_zero` (4 simp lemmas — exported API, no in-file consumer); `integral_swap` (top-level theorem, no in-file consumer). `innerInt` and `innerInt_apply` are used.
- **Decls with `sorry`:** none.
- **`set_option`:** none. (`omit [CompleteSpace K]` on all 6 lemmas/theorem; `classical` inside `integral_swap`.)
- **Proofs > 50 lines: 1** — `integral_swap` (~102 lines) → OVER-50, needs `/decompose-proof`.
- **Proofs 30-50 lines: 0.**

Output path: /Users/mcu22seu/Documents/GitHub/aintlib-main/projects/PadicLFunctions/.mathlib-quality/overview/inventory/PadicLFunctions_MeasureR_Fubini.md
