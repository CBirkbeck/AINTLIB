# Inventory: PadicLFunctions/Measure/Fubini.lean

A Fubini theorem for `ℤ_[p]`-valued (p-adic) measures on compact spaces: the iterated
integrals `∫_X (∫_Y F dν) dμ` and `∫_Y (∫_X F dμ) dν` agree. This is the engine behind
commutativity/associativity of convolution on the Iwasawa algebra `Λ(ℤ_p^×)`. The whole
file lives in `namespace PadicMeasure` under a `noncomputable section`, with
`variable (p : ℕ) [hp : Fact p.Prime]` and `variable {X Y : Type*} [TopologicalSpace X]
[TopologicalSpace Y]`.

---

### def innerInt
- Type: `[CompactSpace Y] (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) : C(X, ℤ_[p])`
- What: The inner integral `x ↦ ∫ F(x, y) dν(y)` packaged as a continuous map `X → ℤ_[p]`; its underlying function is `fun x => ν (F.curry x)`.
- How: Bundles the pointwise function with a continuity proof obtained by composing the continuity of the measure `ν` (`continuous p ν`) with the continuity of currying (`map_continuous F.curry`).
- Hypotheses: `Y` is a compact space; `ν` a p-adic measure on `Y`; `F` a continuous `ℤ_[p]`-valued map on the product `X × Y`.
- Uses from project: [`PadicMeasure`, `continuous`]
- Used by: `innerInt_apply`, `innerInt_add`, `innerInt_smul`, `innerInt_measure_add`, `innerInt_measure_zero`, `integral_swap`
- Visibility: public
- Lines: 33-36 (def, no tactic proof)
- Notes: none

### lemma innerInt_apply
- Type: `[CompactSpace Y] (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) (x : X) : innerInt p ν F x = ν (F.curry x)`
- What: Computation/unfolding lemma stating the inner-integral map evaluated at `x` equals `ν` applied to the curried slice `F.curry x`.
- How: Holds definitionally; proof is `rfl`. Tagged `@[simp]`.
- Hypotheses: `Y` compact; `ν` a measure on `Y`; `F` continuous on the product; `x` a point of `X`.
- Uses from project: [`innerInt`]
- Used by: `integral_swap` (used inside both `hL` and `hR` bounds)
- Visibility: public
- Lines: 38-40 (proof `rfl`, 1 line)
- Notes: none

### lemma innerInt_add
- Type: `[CompactSpace Y] (ν : PadicMeasure p Y) (F G : C(X × Y, ℤ_[p])) : innerInt p ν (F + G) = innerInt p ν F + innerInt p ν G`
- What: The inner-integral construction is additive in the integrand `F`.
- How: `ContinuousMap.ext` reduces to a pointwise identity, then `simp` using the fact that `(F + G).curry x = F.curry x + F.curry x` (proved via `ContinuousMap.ext` with `rfl` fibrewise) plus additivity of the measure. Tagged `@[simp]`.
- Hypotheses: `Y` compact; `ν` a measure on `Y`; `F`, `G` continuous integrands on `X × Y`.
- Uses from project: [`innerInt`]
- Used by: unused in file
- Visibility: public
- Lines: 42-46 (proof ~2 lines)
- Notes: none

### lemma innerInt_smul
- Type: `[CompactSpace Y] (c : ℤ_[p]) (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) : innerInt p ν (c • F) = c • innerInt p ν F`
- What: The inner-integral construction is `ℤ_[p]`-scalar-linear in the integrand.
- How: `ContinuousMap.ext` to a pointwise goal, then `simp` using `(c • F).curry x = c • F.curry x` (fibrewise `rfl`) and scalar-linearity of the measure. Tagged `@[simp]`.
- Hypotheses: `Y` compact; scalar `c : ℤ_[p]`; `ν` a measure on `Y`; `F` continuous integrand.
- Uses from project: [`innerInt`]
- Used by: unused in file
- Visibility: public
- Lines: 48-53 (proof ~2 lines)
- Notes: none

### lemma innerInt_measure_add
- Type: `[CompactSpace Y] (ν₁ ν₂ : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) : innerInt p (ν₁ + ν₂) F = innerInt p ν₁ F + innerInt p ν₂ F`
- What: The inner-integral construction is additive in the *measure* argument `ν`.
- How: `ContinuousMap.ext` reduces to a pointwise goal that is `rfl` (the sum measure acts as the sum of actions). Tagged `@[simp]`.
- Hypotheses: `Y` compact; two measures `ν₁, ν₂` on `Y`; `F` continuous integrand.
- Uses from project: [`innerInt`]
- Used by: unused in file
- Visibility: public
- Lines: 55-59 (proof 1 line, `rfl` under ext)
- Notes: none

### lemma innerInt_measure_zero
- Type: `[CompactSpace Y] (F : C(X × Y, ℤ_[p])) : innerInt p (0 : PadicMeasure p Y) F = 0`
- What: Integrating against the zero measure on `Y` gives the zero inner-integral map.
- How: `ContinuousMap.ext` to a pointwise `rfl` (the zero measure sends everything to `0`). Tagged `@[simp]`.
- Hypotheses: `Y` compact; `F` continuous integrand on `X × Y`.
- Uses from project: [`innerInt`]
- Used by: unused in file
- Visibility: public
- Lines: 61-64 (proof 1 line, `rfl` under ext)
- Notes: none

### theorem exists_locallyConstant_norm_sub_le'
- Type: `[CompactSpace X] {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E] (f : C(X, E)) {ε : ℝ} (hε : 0 < ε) : ∃ Φ : LocallyConstant X E, ∀ x, ‖f x - Φ x‖ ≤ ε`
- What: Density of locally constant maps for a general ultrametric target: any continuous map from a compact space into an ultrametric seminormed additive group is uniformly approximated (within `ε`) by a locally constant map. Generalises mathlib's `ℤ_[p]`-valued `exists_locallyConstant_norm_sub_le`. Flagged as a mathlib PR candidate.
- How: Case-split on emptiness of `X` (empty case builds a trivial locally constant map). Otherwise: for each `x` take the clopen `ε`-closed-ball preimage `f ⁻¹' closedBall (f x) ε` — clopen because in an ultrametric space closed balls are open (`IsUltrametricDist.isOpen_closedBall`) and closed balls are closed, both pulled back by `map_continuous f`. Extract a finite subcover via `IsCompact.elim_finite_subcover` on `isCompact_univ`. Encode each point by its boolean membership pattern `P x c = decide (x ∈ U c)` over the finite cover; prove `P` locally constant (`IsLocallyConstant`) by writing each fibre as a finite intersection of clopen/co-clopen sets. Define `h` to pick a representative value `f (chosen center)` from each pattern and bound the error by `hUapprox`.
- Hypotheses: `X` compact; `E` a seminormed add comm group with ultrametric distance; `f` continuous `X → E`; `ε > 0`.
- Uses from project: [] (purely topology/mathlib; no PadicLFunctions decls)
- Used by: `integral_swap`
- Visibility: public
- Lines: 66-115 (proof ~42 lines)
- Notes: long(30-50) — proof body is ~42 lines; uses `classical`. No sorry/set_option/TODO.

### theorem integral_swap
- Type: `[CompactSpace X] [CompactSpace Y] (μ : PadicMeasure p X) (ν : PadicMeasure p Y) (F : C(X × Y, ℤ_[p])) : μ (innerInt p ν F) = ν (innerInt p μ (F.comp ⟨Prod.swap, continuous_swap⟩))`
- What: Fubini/Tonelli for p-adic measures — the two iterated integrals of a continuous `ℤ_[p]`-valued `F` on `X × Y` agree: `∫_X (∫_Y F dν) dμ = ∫_Y (∫_X F dμ) dν`. The right side integrates the swapped map `F ∘ Prod.swap`.
- How: Reduce to "approximately equal within every `ε`" via `eq_of_forall_dist_le`. Approximate the curried map `F.curry : X → C(Y, ℤ_[p])` uniformly within `ε` by a locally constant `Φ` using `exists_locallyConstant_norm_sub_le'`. `Φ` has finitely many values (`Φ.range_finite`), so set the common finite sum `S = ∑_g μ(𝟙_{Φ=g}) · ν g` over clopen fibres (`isClopen_fiber`, `LocallyConstant.charFn`). Key collapse lemma `hcollapse`: for any weight `w`, `∑_g 𝟙_{Φ=g}(x) · w g = w (Φ x)`, proved by `Finset.sum_eq_single` with the characteristic function evaluating to `1` on its fibre and `0` off it. Then bound each iterated integral against `S` by an explicit intermediate `mid₁`/`mid₂` (linear combinations of characteristic functions / the `g`'s) using measure linearity (`map_sum`, `map_smul`, `map_sub`) and the operator-norm bound `norm_apply_le p μ`/`norm_apply_le p ν` together with `ContinuousMap.norm_le` and the uniform `ε`-bound `hΦ`. Finally combine the two `≤ ε` bounds with the ultrametric triangle inequality `dist_triangle_max`.
- Hypotheses: `X` and `Y` both compact spaces; `μ` a p-adic measure on `X`; `ν` on `Y`; `F` a continuous `ℤ_[p]`-valued map on `X × Y`.
- Uses from project: [`innerInt`, `innerInt_apply`, `norm_apply_le`, `PadicMeasure`, `exists_locallyConstant_norm_sub_le'`]
- Used by: unused in file (terminal result of the file)
- Visibility: public
- Lines: 117-235 (proof ~108 lines)
- Notes: OVER-50 — proof body ~108 lines, needs /decompose-proof. Uses `classical`. No sorry/set_option/TODO.

---

## File Summary

- Total declarations: 8 — defs: 1 (`innerInt`); lemmas/theorems: 7 (`innerInt_apply`, `innerInt_add`, `innerInt_smul`, `innerInt_measure_add`, `innerInt_measure_zero`, `exists_locallyConstant_norm_sub_le'`, `integral_swap`); instances: 0.
- Key API (used by ≥3 decls in file): `innerInt` (used by all 6 other decls + itself's lemmas — 6 uses).
- Unused in file: `innerInt_add`, `innerInt_smul`, `innerInt_measure_add`, `innerInt_measure_zero` (the four `@[simp]` algebra lemmas), and `integral_swap` (terminal export). `exists_locallyConstant_norm_sub_le'` is used only by `integral_swap`.
- Declarations with `sorry`: none.
- `set_option`: none.
- Proofs >50 lines: 1 — `integral_swap` (~108 lines).
- Proofs 30-50 lines: 1 — `exists_locallyConstant_norm_sub_le'` (~42 lines).
- Cross-file project dependencies (from `PadicLFunctions.Measure.Basic`): `PadicMeasure`, `continuous`, `norm_apply_le`.
- Notable: `exists_locallyConstant_norm_sub_le'` is flagged in its docstring as a mathlib PR candidate (generalises mathlib's `exists_locallyConstant_norm_sub_le`).
