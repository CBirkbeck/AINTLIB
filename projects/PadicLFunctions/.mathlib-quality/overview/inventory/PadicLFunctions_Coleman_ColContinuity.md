# Inventory: PadicLFunctions/Coleman/ColContinuity.lean

File builds the topology/continuity layer (RJW §13 / IMC analytic core) crossing from the dense
`ℤ_p[𝒢]`-span of Dirac scalars to the full `Λ(𝒢)` action, closing `Col '' 𝒞_{∞,1} = I(𝒢)ζ_p`.
Two namespaces: `PadicMeasure` (target weak-* topology) and `PadicLFunctions.Coleman`
(source inverse-limit topology + continuity of `Col`).

---

## namespace PadicMeasure

### instance PadicMeasure.instTopologicalSpace
- Type: `TopologicalSpace (PadicMeasure p X)` := `TopologicalSpace.induced DFunLike.coe inferInstance`
- What: The weak-* topology on `Λ(X) = C(X,ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]` — coarsest topology making every evaluation `μ ↦ μ f` continuous (pointwise convergence on functionals), induced from the product topology on `C(X,ℤ_[p]) → ℤ_[p]` by the coercion.
- How: Topology induced along `DFunLike.coe` from the product/Pi topology.
- Hypotheses: `p` prime; `X` a topological space.
- Uses from project: [`PadicMeasure`]
- Used by: `continuous_eval`, `continuous_iff_eval`, `instT2Space`, `tendsto_approxDirac`, `isClosed_range_coe`, `instCompactSpace`
- Visibility: public (instance)
- Lines: 46-47 (def, no proof)
- Notes: none

### theorem PadicMeasure.continuous_eval
- Type: `(f : C(X, ℤ_[p])) : Continuous (fun μ : PadicMeasure p X => μ f)`
- What: Evaluation `μ ↦ μ f` at a fixed test function is weak-* continuous.
- How: Composition `(continuous_apply f).comp continuous_induced_dom` — projection of the inducing map.
- Hypotheses: `f` a continuous `ℤ_[p]`-valued function on `X`.
- Uses from project: [`PadicMeasure`, `instTopologicalSpace`]
- Used by: `continuous_mul_right`
- Visibility: public
- Lines: 50-52 (proof ~1 line)
- Notes: none

### theorem PadicMeasure.continuous_iff_eval
- Type: `(g : Y → PadicMeasure p X) : Continuous g ↔ ∀ f : C(X, ℤ_[p]), Continuous (fun y => g y f)`
- What: A map into `PadicMeasure` is continuous iff every evaluation `y ↦ g y f` is.
- How: `continuous_induced_rng` then `continuous_pi_iff`, closed by `rfl`.
- Hypotheses: `Y` a topological space; `g : Y → PadicMeasure p X`.
- Uses from project: [`PadicMeasure`, `instTopologicalSpace`]
- Used by: `continuous_mul_right`, `continuous_smul_scalar`, `continuous_colemanPipe2`, `continuous_Col` (via `continuous_iff_eval` call in `continuous_colemanPipe2`)
- Visibility: public
- Lines: 55-58 (proof ~2 lines)
- Notes: none

### instance PadicMeasure.instT2Space
- Type: `T2Space (PadicMeasure p X)`
- What: `PadicMeasure p X` is Hausdorff in the weak-* topology: two measures equal at every `f` are equal.
- How: `separated_by_continuous continuous_induced_dom` plus `DFunLike.coe_injective`.
- Hypotheses: `p` prime; `X` topological space.
- Uses from project: [`PadicMeasure`, `instTopologicalSpace`]
- Used by: `isClosed_span_singleton` (Hausdorffness for compact⟹closed)
- Visibility: public (instance)
- Lines: 61-63 (proof ~2 lines)
- Notes: none

### theorem PadicMeasure.continuous_mul_right
- Type: `(ν : PadicMeasure p ℤ_[p]ˣ) : Continuous (fun s : PadicMeasure p ℤ_[p]ˣ => s * ν)`
- What: Right multiplication `s ↦ s * ν` is weak-* continuous on `Λ(ℤ_p^×)`.
- How: Via the convolution formula `(s*ν) f = s(innerInt ν (f.comp mulCM₂))`, it is the continuous evaluation `continuous_eval` of `s` at a fixed function independent of `s`; uses `units_mul_apply`.
- Hypotheses: `ν` a fixed measure on `ℤ_p^×`.
- Uses from project: [`PadicMeasure`, `continuous_iff_eval`, `units_mul_apply`, `continuous_eval`, `innerInt`, `unitsMulCM₂`]
- Used by: `mul_mem_of_dirac_mul_mem`, `isClosed_span_singleton`
- Visibility: public
- Lines: 68-73 (proof ~4 lines)
- Notes: none

### theorem PadicMeasure.continuous_smul_scalar
- Type: `(μ : PadicMeasure p X) : Continuous (fun c : ℤ_[p] => c • μ)`
- What: Scalar multiplication `c ↦ c • μ` (fixed `μ`) is weak-* continuous in the scalar `c : ℤ_[p]`.
- How: `(c • μ) f = c * (μ f)` is continuous in `c`; `continuous_id.mul continuous_const`.
- Hypotheses: `μ` a fixed measure.
- Uses from project: [`PadicMeasure`, `continuous_iff_eval`]
- Used by: `smul_mem_of_isClosed_subgroup`
- Visibility: public
- Lines: 77-82 (proof ~4 lines)
- Notes: none

### theorem PadicMeasure.smul_mem_of_isClosed_subgroup
- Type: `{H : AddSubgroup (PadicMeasure p X)} (hH : IsClosed H) (c : ℤ_[p]) {x} (hx : x ∈ H) : c • x ∈ H`
- What: A closed additive subgroup of `Λ` is a `ℤ_[p]`-submodule: `c • x ∈ H` for `x ∈ H`.
- How: `ℕ • x ⊆ H` (`nsmul_mem`), `ℕ ↪ ℤ_[p]` dense (`PadicInt.denseRange_natCast`), and `c ↦ c•x` continuous (`continuous_smul_scalar`) give `c•x ∈ closure H = H`; hinges on `image_closure_subset_closure_image` and `Nat.cast_smul_eq_nsmul`.
- Hypotheses: `H` a closed additive subgroup; `c` a `p`-adic integer; `x ∈ H`.
- Uses from project: [`PadicMeasure`, `continuous_smul_scalar`]
- Used by: `mul_mem_of_dirac_mul_mem`
- Visibility: public
- Lines: 86-106 (proof ~17 lines)
- Notes: long argument but under 30 lines; none

### def PadicMeasure.approxDirac
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) (n : ℕ) : PadicMeasure p ℤ_[p]ˣ`
- What: Level-`n` Dirac approximation `D_n(μ) = ∑_{g∈(ℤ/p^n)ˣ} μ(𝟙_g-fibre)·[rep g]`, a `ℤ_[p]`-combination of Dirac masses agreeing with `μ` on every level-`n` indicator; `0` if `n = 0`.
- How: `dite 0 < n` then a `Finset.sum` over `(ZMod (p^n))ˣ` of `μ (levelChar p n g) • dirac p (rep g)`.
- Hypotheses: `μ` a measure on `ℤ_p^×`; level `n`.
- Uses from project: [`PadicMeasure`, `levelChar`, `dirac`, `unitsToZModPow_surjective`]
- Used by: `approxDirac_levelChar`, `approxDirac_apply_eq`, `tendsto_approxDirac`, `mul_mem_of_dirac_mul_mem`
- Visibility: public
- Lines: 113-117 (def)
- Notes: none

### theorem PadicMeasure.approxDirac_levelChar
- Type: `{μ} {n} (hn : 0 < n) (h : (ZMod (p^n))ˣ) : approxDirac p μ n (levelChar p n h) = μ (levelChar p n h)`
- What: `D_n(μ)` agrees with `μ` on the level-`n` indicators: `D_n(μ)(𝟙_h) = μ(𝟙_h)`.
- How: Expand the sum applied to the indicator via `LinearMap.sum_apply`, then `Finset.sum_eq_single h` killing off-diagonal terms via `dirac_apply` + `levelChar_apply_eq`/`levelChar_apply_ne` and the `choose_spec` of the surjection.
- Hypotheses: `0 < n`; `h` a level-`n` character index.
- Uses from project: [`PadicMeasure`, `approxDirac`, `levelChar`, `dirac`, `dirac_apply`, `levelChar_apply_eq`, `levelChar_apply_ne`, `unitsToZModPow_surjective`]
- Used by: `approxDirac_apply_eq`
- Visibility: public
- Lines: 120-134 (proof ~13 lines)
- Notes: none

### theorem PadicMeasure.approxDirac_apply_eq
- Type: `{μ} {n} (hn : 0 < n) {g : LocallyConstant ℤ_[p]ˣ ℤ_[p]} (hfac : g factors through level n) : approxDirac p μ n (g : C) = μ (g : C)`
- What: `D_n(μ)` agrees with `μ` on any locally constant `g` that factors through level `n` (constant on level-`n` fibres).
- How: Decompose `g = ∑_c g(rep c) • 𝟙_c` (level-`n` indicator decomposition, cf. `levelMap_jointly_injective`) via `Finset.sum_eq_single`, then `map_sum`/`map_smul` and `approxDirac_levelChar`.
- Hypotheses: `0 < n`; `g` locally constant factoring through level `n`.
- Uses from project: [`PadicMeasure`, `approxDirac`, `approxDirac_levelChar`, `levelChar`, `levelChar_apply_eq`, `levelChar_apply_ne`, `unitsToZModPow`, `unitsToZModPow_surjective`]
- Used by: `tendsto_approxDirac`
- Visibility: public
- Lines: 138-162 (proof ~22 lines)
- Notes: none

### theorem PadicMeasure.tendsto_approxDirac
- Type: `(μ : PadicMeasure p ℤ_[p]ˣ) : Filter.Tendsto (fun n => approxDirac p μ n) Filter.atTop (nhds μ)`
- What: The Dirac span is weak-* dense: the level-`n` Dirac approximations converge to `μ` (`D_n(μ) f → μ f` for every test `f`).
- How: Reduce to pointwise convergence (`nhds_induced`, `tendsto_pi_nhds`); given `ε`, approximate `f` by an lc `g` (`exists_locallyConstant_norm_sub_le`) factoring through level `N` (`exists_level_factorization`); for `n ≥ N`, `approxDirac_apply_eq` gives agreement on `g`, and the ultrametric bound `IsUltrametricDist.norm_add_le_max` + operator bound `norm_apply_le` close it.
- Hypotheses: `μ` a measure on `ℤ_p^×`.
- Uses from project: [`PadicMeasure`, `instTopologicalSpace`, `approxDirac`, `approxDirac_apply_eq`, `exists_locallyConstant_norm_sub_le`, `exists_level_factorization`, `unitsToZModPow`, `unitsToZModPow_le`, `norm_apply_le`]
- Used by: `mul_mem_of_dirac_mul_mem`
- Visibility: public
- Lines: 168-196 (proof ~28 lines)
- Notes: none

### theorem PadicMeasure.mul_mem_of_dirac_mul_mem
- Type: `{H : AddSubgroup (PadicMeasure p ℤ_[p]ˣ)} (hH : IsClosed H) {ν} (hν : ∀ a : ℤ_[p]ˣ, dirac p a * ν ∈ H) (r) : r * ν ∈ H`
- What: Closure-crossing for a principal ideal: a closed additive subgroup `H` containing `[a]·ν` for every group element `a` contains the whole principal ideal `r·ν`.
- How: Each `D_n(r)·ν ∈ H` (finite `ℤ_[p]`-combination of `[a]·ν` using `smul_mem_of_isClosed_subgroup`, `AddSubgroup.sum_mem`); `D_n(r)·ν → r·ν` by `continuous_mul_right` ∘ `tendsto_approxDirac`; so `r·ν ∈ closure H = H` (`mem_closure_of_tendsto`).
- Hypotheses: `H` closed additive subgroup; `ν` a measure; `H` contains `dirac a · ν` for all `a ∈ ℤ_p^×`; `r` arbitrary.
- Uses from project: [`PadicMeasure`, `approxDirac`, `smul_mem_of_isClosed_subgroup`, `dirac`, `tendsto_approxDirac`, `continuous_mul_right`]
- Used by: unused in file
- Visibility: public
- Lines: 204-224 (proof ~16 lines)
- Notes: none

### theorem PadicMeasure.isClosed_range_coe
- Type: `IsClosed (Set.range (DFunLike.coe : PadicMeasure p ℤ_[p]ˣ → (C(ℤ_[p]ˣ,ℤ_[p]) → ℤ_[p])))`
- What: The coercion `DFunLike.coe` has closed range: its image is exactly the additive, `ℤ_[p]`-homogeneous functionals (two closed conditions).
- How: Rewrite range as `{F | additive} ∩ {F | homogeneous}` (a `LinearMap` reconstruction), then `IsClosed.inter` of intersections of `isClosed_eq` of `continuous_apply` evaluations.
- Hypotheses: `p` prime.
- Uses from project: [`PadicMeasure`, `instTopologicalSpace`]
- Used by: `instCompactSpace`
- Visibility: public
- Lines: 231-249 (proof ~18 lines)
- Notes: none

### instance PadicMeasure.instCompactSpace
- Type: `CompactSpace (PadicMeasure p ℤ_[p]ˣ)`
- What: `Λ(ℤ_p^×)` is weak-* compact (a p-adic Banach–Alaoglu).
- How: The coercion is inducing onto the compact product `∏_f ℤ_[p]` (Tychonoff: `ℤ_[p]` compact) with closed range (`isClosed_range_coe`), so `Λ` is a closed subspace of a compact space; `Topology.IsInducing.isCompact_iff`.
- Hypotheses: `p` prime.
- Uses from project: [`PadicMeasure`, `instTopologicalSpace`, `isClosed_range_coe`]
- Used by: `isClosed_span_singleton` (compactness of `Λ` via `isCompact_univ`)
- Visibility: public (instance)
- Lines: 254-259 (proof ~5 lines)
- Notes: none

### theorem PadicMeasure.isClosed_span_singleton
- Type: `(ν : PadicMeasure p ℤ_[p]ˣ) : IsClosed ((Ideal.span {ν}) : Set (PadicMeasure p ℤ_[p]ˣ))`
- What: Every principal ideal `(ν)` of `Λ(ℤ_p^×)` is weak-* closed.
- How: `(ν) = range (r ↦ r·ν)`, the image of compact `Λ` (`instCompactSpace`) under continuous `continuous_mul_right`, hence compact (`isCompact_univ.image`), hence closed (`Λ` Hausdorff via `instT2Space`).
- Hypotheses: `ν` a measure on `ℤ_p^×`.
- Uses from project: [`PadicMeasure`, `instCompactSpace`, `instT2Space`, `continuous_mul_right`]
- Used by: `isClosed_zetaIdeal`
- Visibility: public
- Lines: 264-273 (proof ~9 lines)
- Notes: none

### theorem PadicMeasure.isClosed_zetaIdeal
- Type: `(hp2 : p ≠ 2) : IsClosed ((zetaIdeal p hp2) : Set (PadicMeasure p ℤ_[p]ˣ))`
- What: The Iwasawa ideal `I(𝒢)ζ_p` is weak-* closed (the closedness half of `⊆` in the §12.5 image computation).
- How: By the principal description `zetaIdeal_eq_span` (the `([a₀]−1)·ζ_p`-witness `zetaNum a₀` at topological generator `a₀`, requiring `hb_gen` zpowers-generation and `hνeq` via `IsLocalization.mk'_spec'`/`padicZeta`), it is principal, hence closed by `isClosed_span_singleton`.
- Hypotheses: `p ≠ 2`.
- Uses from project: [`PadicMeasure`, `isClosed_span_singleton`, `zetaIdeal`, `zetaIdeal_eq_span`, `exists_nat_topological_generator`, `unitsToZModPow`, `dirac`, `QuotientField`, `padicZeta`, `zetaNum`]
- Used by: unused in file
- Visibility: public
- Lines: 280-293 (proof ~13 lines)
- Notes: none

---

## namespace PadicLFunctions.Coleman

### instance (anonymous) SequentialSpace (PowerSeries ℤ_[p])
- Type: `SequentialSpace (PowerSeries ℤ_[p])`
- What: `PowerSeries ℤ_[p]` with the coefficientwise topology is sequential (so continuity = sequential continuity), as the countable product `(Unit →₀ ℕ) → ℤ_[p]`.
- How: `inferInstanceAs (SequentialSpace ((Unit →₀ ℕ) → ℤ_[p]))`.
- Hypotheses: `p` prime.
- Uses from project: []
- Used by: `continuous_evalPi`
- Visibility: public (instance, anonymous)
- Lines: 306-307 (def)
- Notes: none

### theorem Coleman.continuous_evalPi
- Type: `{n : ℕ} (hn : 1 ≤ n) : Continuous (fun f : PowerSeries ℤ_[p] => evalPi p f n)`
- What: Evaluation at `π_n` is continuous (`n ≥ 1`): `f ↦ f(π_n)` is continuous on `ℤ_p⟦T⟧`.
- How: Reduce continuity to sequential continuity (`SeqContinuous.continuous`, the sequential space instance), then `tendsto_evalPi_of_tendsto`.
- Hypotheses: `1 ≤ n`.
- Uses from project: [`evalPi`, `tendsto_evalPi_of_tendsto`]
- Used by: `continuous_colEval`, `colSec`/`continuous_colSec` chain, `isCompact_colemanPairSet`
- Visibility: public
- Lines: 311-314 (proof ~2 lines)
- Notes: none

### local instance Coleman.instNormedAlgebra_K_Cp
- Type: `(n : ℕ) : NormedAlgebra (K p n) ℂ_[p]`
- What: `ℂ_[p]` is a normed `K_n`-algebra (`K_n ⊆ ℂ_[p]` with restricted norm, scalar action is multiplication).
- How: `norm_smul_le` via `Algebra.smul_def`, `norm_mul`, then `rfl`.
- Hypotheses: level `n`.
- Uses from project: [`K`]
- Used by: `continuous_levelNorm` (instance synthesis)
- Visibility: scoped (local instance)
- Lines: 332-334 (proof ~1 line)
- Notes: none

### local instance Coleman.instNNF_extendScalars
- Type: `(n : ℕ) : NontriviallyNormedField (IntermediateField.extendScalars (K_le_succ p n))`
- What: The relative extension `K_{n+1} = extendScalars(K_n ≤ K_{n+1})` is a nontrivially normed field for the `K_n`-structure (same `ℂ_[p]`-subspace norm).
- How: `SubfieldClass.toNormedField` for the field structure; `non_trivial` from a nontrivial element of `K p n` pushed through `algebraMap`.
- Hypotheses: level `n`.
- Uses from project: [`K`, `K_le_succ`]
- Used by: `continuous_levelNorm` (instance synthesis)
- Visibility: scoped (local instance)
- Lines: 339-345 (proof ~5 lines)
- Notes: none

### local instance Coleman.instNS_extendScalars
- Type: `(n : ℕ) : NormedSpace (K p n) (IntermediateField.extendScalars (K_le_succ p n))`
- What: `K_{n+1} = extendScalars(K_n ≤ K_{n+1})` is a normed `K_n`-space (restricted `ℂ_[p]` norm; multiplicative scalar action).
- How: `norm_smul_le` via `Algebra.smul_def`, `norm_mul`, then `rfl`.
- Hypotheses: level `n`.
- Uses from project: [`K`, `K_le_succ`]
- Used by: `continuous_levelNorm` (instance synthesis)
- Visibility: scoped (local instance)
- Lines: 349-353 (proof ~3 lines)
- Notes: none

### local instance Coleman.instComplete_K
- Type: `(n : ℕ) : CompleteSpace (K p n)`
- What: `K_n` is complete (finite-dimensional over the complete `ℚ_[p]`).
- How: `FiniteDimensional.complete ℚ_[p] (K p n)` using `IsCyclotomicExtension.finiteDimensional`.
- Hypotheses: level `n`.
- Uses from project: [`K`]
- Used by: `continuous_levelNorm` (instance synthesis)
- Visibility: scoped (local instance)
- Lines: 356-360 (proof ~4 lines)
- Notes: none

### theorem Coleman.continuous_levelNorm
- Type: `(n : ℕ) : Continuous (fun x : K p (n + 1) => (levelNorm p n (x : ℂ_[p]) : ℂ_[p]))`
- What: ST3a — the level norm `N_{n+1,n}` is continuous on `K_{n+1}` (with the `ℂ_[p]`-subspace topology); the tower-descent gateway.
- How: `N_{n+1,n} = Algebra.norm (K_n) = det ∘ lmul` on the finite extension `K_{n+1}/K_n`; both `lmul` (`ContinuousLinearMap.mul`) and `det` (`ContinuousLinearMap.continuous_det`) are continuous, the carrier maps `K_{n+1} ↪ E`, `K_n ↪ ℂ_[p]` continuous (`continuous_induced_dom`), and `levelNorm_apply` rewrites; uses `FiniteDimensional.right`, `IsCyclotomicExtension.finiteDimensional`.
- Hypotheses: level `n`.
- Uses from project: [`K`, `K_le_succ`, `levelNorm`, `levelNorm_apply`, plus local instances above]
- Used by: `continuousOn_levelNorm`
- Visibility: public
- Lines: 372-397 (proof ~25 lines)
- Notes: set_option synthInstance.maxHeartbeats 1000000; set_option maxHeartbeats 1000000 (both bumps, lines 362/365)

### def Coleman.elemsCoe
- Type: `(u : NormCompatUnits p) : ℕ → ℂ_[p]` := `fun n => ((u.elems n : ℂ_[p]ˣ) : ℂ_[p])`
- What: The coordinate map `u ↦ (n ↦ (u.elems n : ℂ_[p]))` of a norm-compatible unit system into the product `∏ n, ℂ_[p]`; the inverse-limit topology is induced along it.
- How: Pointwise coercion `Units.val` of the level elements.
- Hypotheses: `u` a norm-compatible unit system.
- Uses from project: [`NormCompatUnits`]
- Used by: `instTopologicalSpace` (Coleman), `continuous_elems`, `continuous_iff_elems`, `mem_closure_iff_elemsCoe`, `mem_closure_of_levelwise`, `Col_mem_closure_image_of_levelwise`
- Visibility: public
- Lines: 410 (def)
- Notes: none

### instance Coleman.instTopologicalSpace
- Type: `TopologicalSpace (NormCompatUnits p)` := `TopologicalSpace.induced (elemsCoe p) inferInstance`
- What: The inverse-limit topology on `𝒰_∞ = NormCompatUnits` — coarsest making every level coordinate `u ↦ (u.elems n : ℂ_[p])` continuous (source-side analogue of `PadicMeasure.instTopologicalSpace`).
- How: Topology induced along `elemsCoe` from the product topology on `∏ n, ℂ_[p]`.
- Hypotheses: `p` prime.
- Uses from project: [`NormCompatUnits`, `elemsCoe`]
- Used by: `continuous_elems`, `continuous_iff_elems`, `instT2Space` (Coleman), `mem_closure_iff_elemsCoe`, `continuous_Col`, etc.
- Visibility: public (instance)
- Lines: 416-417 (def)
- Notes: none

### theorem Coleman.continuous_elems
- Type: `(n : ℕ) : Continuous (fun u : NormCompatUnits p => ((u.elems n : ℂ_[p]ˣ) : ℂ_[p]))`
- What: The level coordinate `u ↦ (u.elems n : ℂ_[p])` is continuous on `𝒰_∞`.
- How: `(continuous_apply n).comp (continuous_induced_dom (f := elemsCoe p))`.
- Hypotheses: level `n`.
- Uses from project: [`NormCompatUnits`, `instTopologicalSpace`, `elemsCoe`]
- Used by: `continuous_elemsUnits`, `continuous_colSec`
- Visibility: public
- Lines: 420-422 (proof ~1 line)
- Notes: none

### theorem Coleman.continuous_iff_elems
- Type: `(g : Y → NormCompatUnits p) : Continuous g ↔ ∀ n, Continuous (fun y => (((g y).elems n : ℂ_[p]ˣ) : ℂ_[p]))`
- What: Continuity into `𝒰_∞` is coordinatewise (source-side analogue of `PadicMeasure.continuous_iff_eval`).
- How: `continuous_induced_rng` then `continuous_pi_iff`, closed by `rfl`.
- Hypotheses: `Y` topological; `g : Y → NormCompatUnits p`.
- Uses from project: [`NormCompatUnits`, `instTopologicalSpace`, `elemsCoe`]
- Used by: `continuous_colEval`, `continuous_colSec`, `continuous_inv_NCU`
- Visibility: public
- Lines: 427-430 (proof ~2 lines)
- Notes: none

### instance Coleman.instT2Space
- Type: `T2Space (NormCompatUnits p)`
- What: `𝒰_∞` is Hausdorff: systems agreeing at every level coordinate are equal.
- How: `separated_by_continuous continuous_induced_dom` plus `NormCompatUnits.ext` + `Units.ext`.
- Hypotheses: `p` prime.
- Uses from project: [`NormCompatUnits`, `instTopologicalSpace`]
- Used by: unused in file (supports closed-embedding/T2 reasoning indirectly)
- Visibility: public (instance)
- Lines: 434-437 (proof ~3 lines)
- Notes: none

### theorem Coleman.continuous_elemsUnits
- Type: `(n : ℕ) : Continuous (fun u : NormCompatUnits p => u.elems n)`
- What: The unit-valued level coordinate `u ↦ u.elems n : ℂ_[p]ˣ` is continuous on `𝒰_∞`.
- How: `Units.val` is a topological embedding on the normed field `ℂ_[p]` (`Units.isEmbedding_val₀`), so reduce to `continuous_elems`.
- Hypotheses: level `n`.
- Uses from project: [`NormCompatUnits`, `continuous_elems`]
- Used by: `continuous_inv_NCU`, `isClosed_cycloTower1`
- Visibility: public
- Lines: 443-446 (proof ~2 lines)
- Notes: none

### theorem Coleman.mem_closure_iff_elemsCoe
- Type: `{S : Set (NormCompatUnits p)} {u} : u ∈ closure S ↔ elemsCoe p u ∈ closure (elemsCoe p '' S)`
- What: T1220 — the inverse-limit closure bridge: closure membership in `𝒰_∞` transfers to the product `ℕ → ℂ_[p]` (foundation for the levelwise density characterisation).
- How: `closure_induced` (topology is induced along `elemsCoe`).
- Hypotheses: `S` a set; `u` a system.
- Uses from project: [`NormCompatUnits`, `instTopologicalSpace`, `elemsCoe`]
- Used by: `mem_closure_of_levelwise`
- Visibility: public
- Lines: 452-454 (proof ~1 line)
- Notes: none

### theorem Coleman.Col_eq_of_elems_eq
- Type: `{u v : NormCompatUnits p} (h : ∀ n, 1 ≤ n → u.elems n = v.elems n) : Col p u = Col p v`
- What: T1220b — `Col` is insensitive to the level-`0` coordinate: `Col u = Col v` when the systems agree at every `n ≥ 1`.
- How: `Col` factors through `colemanSeries`, pinned by the `n ≥ 1` interpolation data (`colemanSeries_eq_iff`); unfold `Col` and rewrite.
- Hypotheses: `u, v` agree at all levels `n ≥ 1`.
- Uses from project: [`NormCompatUnits`, `Col`, `colemanSeries`, `colemanSeries_eq_iff`]
- Used by: `Col_mem_closure_image_of_levelwise`
- Visibility: public
- Lines: 461-465 (proof ~3 lines)
- Notes: none

### private theorem Coleman.continuousOn_levelNorm
- Type: `(n : ℕ) : ContinuousOn (levelNorm p n) (K p (n + 1) : Set ℂ_[p])`
- What: `levelNorm p n` is continuous on `K_{n+1}` as a map of ambient `ℂ_[p]` values (ST3a recast through `ContinuousOn`, so the `ε`-`δ` lives in the ambient metric).
- How: `continuousOn_iff_continuous_restrict` then `continuous_levelNorm`.
- Hypotheses: level `n`.
- Uses from project: [`K`, `levelNorm`, `continuous_levelNorm`]
- Used by: `exists_delta_descent`
- Visibility: private
- Lines: 469-472 (proof ~2 lines)
- Notes: none

### private theorem Coleman.exists_delta_descent
- Type: `(u : NormCompatUnits p) : ∀ N, 1 ≤ N → ∀ ε > 0, ∃ δ > 0, ∀ s, ‖(s.elems N − u.elems N : ℂ_[p])‖ < δ → ∀ n, 1 ≤ n → n ≤ N → ‖(s.elems n − u.elems n : ℂ_[p])‖ < ε`
- What: Descent control: matching another system `s` to `u` at the top level `N` within a suitable `δ` controls every level `1 ≤ n ≤ N`.
- How: `Nat.le_induction` on `N`, threading the tolerance one `levelNorm`-step at a time via `Metric.continuousOn_iff` of `continuousOn_levelNorm` and the norm-compatibility `compat` (rewriting `s.compat`/`u.compat`).
- Hypotheses: `u` a system; `N ≥ 1`; `ε > 0`.
- Uses from project: [`NormCompatUnits`, `K`, `continuousOn_levelNorm`, `NormCompatUnits.compat`, `NormCompatUnits.mem`]
- Used by: `mem_closure_of_levelwise`, `Col_mem_closure_image_of_levelwise`
- Visibility: private
- Lines: 478-504 (proof ~26 lines)
- Notes: none

### theorem Coleman.mem_closure_of_levelwise
- Type: `{S : Subgroup (NormCompatUnits p)} {u} (h0 : ∀ s ∈ S, (s.elems 0 : ℂ_[p]) = (u.elems 0 : ℂ_[p])) (h : ∀ n, 1 ≤ n → (u.elems n : ℂ_[p]) ∈ closure (level-n image of S)) : u ∈ closure S`
- What: T1221 — the inverse-limit (levelwise) density characterisation (RJW LemmaGeneratorCinfty1 inverse-limit step): under a shared level-`0` value and closure of each higher level, `u ∈ closure S`.
- How: `mem_closure_iff_elemsCoe` + `mem_closure_iff_nhds`; reduce a basic Pi-neighbourhood box to a finite index set `I`, take infimum radius `ε`, get `δ` from `exists_delta_descent`, pick a single `s ∈ S` close at top level `max b 1` (`Metric.mem_closure_iff`), match level `0` by `h0` and higher levels by the descent.
- Hypotheses: `S` a subgroup whose members share `u`'s level-`0` coordinate; each higher level of `u` in the closure of `S`'s image.
- Uses from project: [`NormCompatUnits`, `instTopologicalSpace`, `elemsCoe`, `mem_closure_iff_elemsCoe`, `exists_delta_descent`]
- Used by: unused in file
- Visibility: public
- Lines: 512-550 (proof ~38 lines)
- Notes: long(30-50); none

### theorem Coleman.continuous_ofPowerSeries_apply
- Type: `(ψ : C(ℤ_[p], ℤ_[p])) : Continuous (fun g : PowerSeries ℤ_[p] => PadicMeasure.ofPowerSeries p g ψ)`
- What: `g ↦ (μ_g)(ψ)` is coefficientwise-continuous for a fixed test function `ψ`: `(ofPowerSeries g)(ψ) = ∑'_n Δⁿψ(0)·gₙ` is a uniform-in-`g` limit of its finite partial sums.
- How: `continuous_of_uniform_approx_of_continuous`; the partial sums `S_N` are continuous (`PowerSeries.WithPiTopology.continuous_coeff`), the tail is `∑'_{n} Δ^{n+N}ψ(0)·g_{n+N}` with norm `≤ ε/2` via `IsUltrametricDist.norm_tsum_le_of_forall_le`, `‖gₙ‖ ≤ 1` (`PadicInt.norm_le_one`) and `Δⁿψ(0) → 0` (`PadicInt.fwdDiff_tendsto_zero`); summability via `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`.
- Hypotheses: `ψ` a continuous `ℤ_[p]`-valued function.
- Uses from project: [`PadicMeasure.ofPowerSeries`, `PadicInt.fwdDiff_tendsto_zero`]
- Used by: `continuous_colemanPipe2`
- Visibility: public
- Lines: 558-599 (proof ~40 lines)
- Notes: long(30-50); none

### def Coleman.colemanPipe2
- Type: `(f finv : PowerSeries ℤ_[p]) : PadicMeasure p ℤ_[p]ˣ`
- What: The measure-side Coleman pipeline (paired form): `x⁻¹ · Res_{ℤ_p^×}(𝒜⁻¹((1+T)·f′·finv))`, i.e. `Col` with `Ring.inverse f` replaced by the supplied `finv` (sidesteps the discontinuity of `Ring.inverse`).
- How: `unitsCmul invCM` of `((mahlerLinearEquiv).symm ((1+X)·derivativeFun f·finv)).comp (extendByZero)`.
- Hypotheses: two series `f`, `finv`.
- Uses from project: [`PadicMeasure`, `PadicMeasure.unitsCmul`, `PadicMeasure.invCM`, `PadicMeasure.mahlerLinearEquiv`, `PadicMeasure.extendByZero`, `PowerSeries.derivativeFun`]
- Used by: `colemanPipe2_eq_Col`, `continuous_colemanPipe2`, `continuous_Col`, `col_image_eq_pipe_image`, `isCompact_col_image`
- Visibility: public
- Lines: 606-610 (def)
- Notes: none

### theorem Coleman.colemanPipe2_eq_Col
- Type: `(u : NormCompatUnits p) : colemanPipe2 p (colemanSeries p u) (Ring.inverse (colemanSeries p u)) = Col p u`
- What: At `(f, finv) = (colemanSeries u, (colemanSeries u)⁻¹)` the paired pipeline equals `Col u` (since `dlog f = (1+T)·f′·(Ring.inverse f)` by definition).
- How: `rfl` (definitional unfolding of `Col`).
- Hypotheses: `u` a norm-compatible system.
- Uses from project: [`NormCompatUnits`, `colemanPipe2`, `colemanSeries`, `Col`]
- Used by: `continuous_Col`, `col_image_eq_pipe_image`
- Visibility: public
- Lines: 615-616 (proof: rfl)
- Notes: none

### theorem Coleman.continuous_colemanPipe2
- Type: `Continuous (Function.uncurry (colemanPipe2 p))`
- What: The paired pipeline `(f, finv) ↦ colemanPipe2 f finv` is jointly continuous.
- How: `PadicMeasure.continuous_iff_eval`; for fixed `φ`, `(colemanPipe2 f finv)(φ) = (ofPowerSeries ((1+T)·f′·finv))(ψ)`, continuous in the series via `continuous_ofPowerSeries_apply`, and `(1+T)·f′·finv` is continuous in `(f, finv)` coefficientwise (`continuous_of_coeff`, `PowerSeries.coeff_derivativeFun`, `PowerSeries.WithPiTopology.continuous_coeff`).
- Hypotheses: `p` prime.
- Uses from project: [`colemanPipe2`, `PadicMeasure.continuous_iff_eval`, `continuous_ofPowerSeries_apply`, `PowerSeries.derivativeFun`, `PowerSeries.coeff_derivativeFun`]
- Used by: `continuous_Col`, `isCompact_col_image`
- Visibility: public
- Lines: 623-634 (proof ~11 lines)
- Notes: none

### def Coleman.normFixedUnits
- Type: `Set (PowerSeries ℤ_[p])` := `{f | IsUnit f ∧ normOp f = f}`
- What: The `𝒩`-fixed unit power series `𝒲ˣ` (the image of `colemanSeries`).
- How: Set-builder with the two conditions.
- Hypotheses: `p` prime.
- Uses from project: [`normOp`]
- Used by: `isClosed_normFixedUnits`, `instCompactSpace_normFixedUnits`, `colEval`, `colSec`, and the whole compact-embedding chain
- Visibility: public
- Lines: 663 (def)
- Notes: none

### theorem Coleman.isClosed_normFixedUnits
- Type: `IsClosed (normFixedUnits p)`
- What: `𝒲ˣ` is closed in `ℤ_p⟦T⟧`.
- How: `{IsUnit}` is closed (`isClosed_isUnit`) and `{𝒩 f = f}` is closed (`isClosed_eq` of `normOp_continuous`, `continuous_id`); intersection.
- Hypotheses: `p` prime.
- Uses from project: [`normFixedUnits`, `normOp`, `normOp_continuous`]
- Used by: `instCompactSpace_normFixedUnits`
- Visibility: public
- Lines: 667-671 (proof ~5 lines)
- Notes: none

### instance Coleman.instCompactSpace_normFixedUnits
- Type: `CompactSpace (normFixedUnits p)`
- What: `𝒲ˣ` is compact (a closed subset of the Tychonoff-compact `ℤ_p⟦T⟧`).
- How: `isCompact_iff_compactSpace` then `(isClosed_normFixedUnits p).isCompact` (uses `Coleman.instCompactSpace` for `ℤ_p⟦T⟧`).
- Hypotheses: `p` prime.
- Uses from project: [`normFixedUnits`, `isClosed_normFixedUnits`, `Coleman.instCompactSpace` (PowerSeries)]
- Used by: closed-embedding step in `continuous_colSec` (compact→T2)
- Visibility: public (instance)
- Lines: 675-677 (proof ~2 lines)
- Notes: none

### def Coleman.colEval
- Type: `(f : normFixedUnits p) : NormCompatUnits p` := `invColeman p f.1 f.2.1 f.2.2`
- What: The evaluation `E : 𝒲ˣ → 𝒰_∞`, `f ↦ invColeman f`: a `𝒩`-fixed unit gives the norm-compatible system of its values `(f(π_n))_n`.
- How: Apply `invColeman` to the underlying series and its unit/fixed proofs.
- Hypotheses: `f` a `𝒩`-fixed unit.
- Uses from project: [`normFixedUnits`, `NormCompatUnits`, `invColeman`]
- Used by: `colemanSeries_colEval`, `continuous_colEval`, `injective_colEval`, `continuous_colSec`
- Visibility: public
- Lines: 682-683 (def)
- Notes: none

### theorem Coleman.colemanSeries_colEval
- Type: `(f : normFixedUnits p) : colemanSeries p (colEval p f) = (f : PowerSeries ℤ_[p])`
- What: `colemanSeries (E f) = f` (the banked `colemanSeries_invColeman`: `E` is a section, `colemanSeries` undoes it).
- How: Direct application of `colemanSeries_invColeman`.
- Hypotheses: `f` a `𝒩`-fixed unit.
- Uses from project: [`normFixedUnits`, `colEval`, `colemanSeries`, `colemanSeries_invColeman`]
- Used by: `injective_colEval`
- Visibility: public
- Lines: 687-689 (proof ~1 line)
- Notes: none

### theorem Coleman.continuous_colEval
- Type: `Continuous (colEval p)`
- What: `E` is continuous.
- How: `continuous_iff_elems`; each level coordinate is `f ↦ f(π_n) = evalPi f n` (`continuous_evalPi`) for `n ≥ 1`, constant `1` at level `0`; `.congr` against the `invColeman`/`dif_pos`/`dif_neg` definition.
- Hypotheses: `p` prime.
- Uses from project: [`colEval`, `continuous_iff_elems`, `invColeman`, `continuous_evalPi`]
- Used by: `continuous_colSec`
- Visibility: public
- Lines: 694-701 (proof ~7 lines)
- Notes: none

### theorem Coleman.injective_colEval
- Type: `Function.Injective (colEval p)`
- What: `E` is injective.
- How: If `invColeman f = invColeman g`, their level values agree, so `f = colemanSeries (E f) = colemanSeries (E g) = g` via `colemanSeries_colEval` and `evalPi_injective`; `Subtype.ext`.
- Hypotheses: `p` prime.
- Uses from project: [`colEval`, `colemanSeries_colEval`, `evalPi_injective`]
- Used by: `continuous_colSec`
- Visibility: public
- Lines: 706-709 (proof ~3 lines)
- Notes: none

### def Coleman.colSec
- Type: `(u : NormCompatUnits p) : normFixedUnits p` := `⟨colemanSeries p u, colemanSeries_isUnit p u, normOp_colemanSeries p u⟩`
- What: The section `u ↦ colemanSeries u` packaged into `𝒲ˣ` (`colemanSeries` lands in the `𝒩`-fixed units).
- How: Subtype constructor using `colemanSeries_isUnit` + `normOp_colemanSeries`.
- Hypotheses: `u` a norm-compatible system.
- Uses from project: [`NormCompatUnits`, `normFixedUnits`, `colemanSeries`, `colemanSeries_isUnit`, `normOp_colemanSeries`]
- Used by: `continuous_colSec`, `continuous_colemanSeries`
- Visibility: public
- Lines: 713-714 (def)
- Notes: none

### theorem Coleman.continuous_colSec
- Type: `Continuous (colSec p)`
- What: The section `colSec` is continuous.
- How: `E` is a closed embedding (`continuous_colEval` + `injective_colEval`, compact→T2 `Continuous.isClosedEmbedding`), hence an embedding, so `colSec` continuous iff `E ∘ colSec` is (`IsEmbedding.continuous_iff`); `(E (colSec u)).elems n = u.elems n` for `n ≥ 1` (`evalPi_colemanSeries`), constant `1` at level `0` — continuous by `continuous_iff_elems` + `continuous_elems`.
- Hypotheses: `p` prime.
- Uses from project: [`colSec`, `colEval`, `continuous_colEval`, `injective_colEval`, `continuous_iff_elems`, `continuous_elems`, `invColeman`, `evalPi_colemanSeries`]
- Used by: `continuous_colemanSeries`
- Visibility: public
- Lines: 721-733 (proof ~12 lines)
- Notes: none

### theorem Coleman.continuous_colemanSeries
- Type: `Continuous (colemanSeries p)`
- What: `colemanSeries : 𝒰_∞ → ℤ_p⟦T⟧` is continuous (coefficientwise / `WithPiTopology`).
- How: It is `Subtype.val ∘ colSec` with `colSec` continuous (`continuous_colSec`); `continuous_subtype_val.comp`.
- Hypotheses: `p` prime.
- Uses from project: [`colemanSeries`, `colSec`, `continuous_colSec`]
- Used by: `continuous_Col`
- Visibility: public
- Lines: 739-740 (proof ~1 line)
- Notes: none

### theorem Coleman.colemanSeries_one'
- Type: `colemanSeries p (1 : NormCompatUnits p) = 1`
- What: `colemanSeries 1 = 1` (the trivial system maps to the unit series).
- How: Both are `𝒩`-fixed units interpolating `1`, so equal by `coleman_existsUnique`'s uniqueness; uses `isUnit_one`, `normOp_one`, `evalPi_one`.
- Hypotheses: `p` prime.
- Uses from project: [`NormCompatUnits`, `colemanSeries`, `coleman_existsUnique`, `normOp_one`, `evalPi_one`]
- Used by: `inverse_colemanSeries`
- Visibility: public
- Lines: 744-747 (proof ~4 lines)
- Notes: none

### theorem Coleman.inverse_colemanSeries
- Type: `(u : NormCompatUnits p) : Ring.inverse (colemanSeries p u) = colemanSeries p u⁻¹`
- What: Identifies the `Ring.inverse` factor of `Col` with the continuous `colemanSeries (·⁻¹)`.
- How: Multiplicativity (`colemanSeries_mul`, `colemanSeries_one'`) gives `colemanSeries u · colemanSeries u⁻¹ = 1`, so `colemanSeries u⁻¹` is the inverse of the unit; `left_inv_eq_right_inv` + `Ring.inverse_mul_cancel`.
- Hypotheses: `u` a norm-compatible system.
- Uses from project: [`NormCompatUnits`, `colemanSeries`, `colemanSeries_mul`, `colemanSeries_one'`, `colemanSeries_isUnit`]
- Used by: `continuous_Col`
- Visibility: public
- Lines: 754-758 (proof ~3 lines)
- Notes: none

### theorem Coleman.continuous_inv_NCU
- Type: `Continuous (fun u : NormCompatUnits p => u⁻¹)`
- What: Inversion `u ↦ u⁻¹` is continuous on `𝒰_∞` (a `CommGroup` with pointwise inverse).
- How: `continuous_iff_elems`; each level coordinate is `u ↦ (u.elems n)⁻¹`, continuous as `val ∘ inv` of the continuous unit coordinate `continuous_elemsUnits` (`ℂ_[p]ˣ` a topological group).
- Hypotheses: `p` prime.
- Uses from project: [`NormCompatUnits`, `continuous_iff_elems`, `continuous_elemsUnits`]
- Used by: `continuous_Col`
- Visibility: public
- Lines: 764-767 (proof ~3 lines)
- Notes: none

### theorem Coleman.continuous_Col
- Type: `Continuous (Col p)`
- What: ST2 — `Col` is continuous (inverse-limit topology on `𝒰_∞`, weak-* on `Λ(ℤ_p^×)`).
- How: Write `Col = colemanPipe2 ∘ (colemanSeries, Ring.inverse ∘ colemanSeries)` (`colemanPipe2_eq_Col`); the pairing is continuous (`continuous_colemanSeries`, and `Ring.inverse ∘ colemanSeries = colemanSeries ∘ (·⁻¹)` via `inverse_colemanSeries` ∘ `continuous_inv_NCU`), and `colemanPipe2` jointly continuous (`continuous_colemanPipe2`).
- Hypotheses: `p` prime.
- Uses from project: [`Col`, `colemanSeries`, `continuous_colemanSeries`, `inverse_colemanSeries`, `continuous_inv_NCU`, `colemanPipe2`, `colemanPipe2_eq_Col`, `continuous_colemanPipe2`]
- Used by: `Col_mem_closure_image_of_levelwise`
- Visibility: public
- Lines: 775-786 (proof ~11 lines)
- Notes: none

### theorem Coleman.isClosed_KCp
- Type: `(n : ℕ) : IsClosed (X := ℂ_[p]) (K p n : Set ℂ_[p])`
- What: `K_n` is closed in `ℂ_[p]` (re-derived; the `Theorem.lean` version is private).
- How: A finite-dimensional `ℚ_[p]`-subspace of a normed space over the complete `ℚ_[p]` is complete, hence closed (`Submodule.closed_of_finiteDimensional`); finite-dimensionality via `IntermediateField.adjoin.finiteDimensional` of the integral primitive root (`zetaSys_primitiveRoot`, `Polynomial.monic_X_pow_sub_C`).
- Hypotheses: level `n`.
- Uses from project: [`K`, `zetaSys`, `zetaSys_primitiveRoot`]
- Used by: `isClosed_OCp`
- Visibility: public
- Lines: 793-800 (proof ~8 lines)
- Notes: none

### theorem Coleman.isClosed_OCp
- Type: `(n : ℕ) : IsClosed (X := ℂ_[p]) (O p n : Set ℂ_[p])`
- What: `O_n` is closed in `ℂ_[p]`.
- How: `O p n = K p n ∩ {‖x‖ ≤ 1}`, intersection of `isClosed_KCp` with the closed unit ball (`isClosed_le`).
- Hypotheses: level `n`.
- Uses from project: [`O`, `K`, `isClosed_KCp`]
- Used by: `isClosed_localUnits`
- Visibility: public
- Lines: 803-805 (proof ~2 lines)
- Notes: none

### theorem Coleman.isClosed_localUnits
- Type: `(n : ℕ) : IsClosed (localUnits p n : Set ℂ_[p]ˣ)`
- What: `localUnits p n` is closed in `ℂ_[p]ˣ`.
- How: Both `(u : ℂ_[p]) ∈ O p n` and `(u⁻¹ : ℂ_[p]) ∈ O p n` are closed (preimages of the closed `O p n` under `Units.continuous_val` / `val∘inv`); intersection.
- Hypotheses: level `n`.
- Uses from project: [`localUnits`, `O`, `isClosed_OCp`]
- Used by: `isClosed_localUnitsOne`, `isClosed_cycloClosureOne`
- Visibility: public
- Lines: 809-815 (proof ~4 lines)
- Notes: none

### theorem Coleman.isClosed_localUnitsOne
- Type: `(n : ℕ) : IsClosed (localUnitsOne p n : Set ℂ_[p]ˣ)`
- What: `localUnitsOne p n` is closed in `ℂ_[p]ˣ`.
- How: `localUnits` closed ∩ the closed condition `‖(u:ℂ_[p])−1‖ < 1`, the preimage of the clopen ultrametric ball `B(1,1)` (`IsUltrametricDist.isClosed_ball`).
- Hypotheses: level `n`.
- Uses from project: [`localUnitsOne`, `localUnits`, `isClosed_localUnits`]
- Used by: `isClosed_cycloClosureOne`
- Visibility: public
- Lines: 819-829 (proof ~10 lines)
- Notes: none

### theorem Coleman.isClosed_cycloClosureOne
- Type: `(n : ℕ) : IsClosed (cycloClosureOne p n : Set ℂ_[p]ˣ)`
- What: `cycloClosureOne p n` (= `𝒞_{n,1}`) is closed in `ℂ_[p]ˣ`.
- How: Intersection of the (closed) topological closure of the cyclotomic units (`Subgroup.isClosed_topologicalClosure`) with the closed `localUnits`/`localUnitsOne`.
- Hypotheses: level `n`.
- Uses from project: [`cycloClosureOne`, `cycloClosure`, `cycloUnits`, `localUnits`, `localUnitsOne`, `isClosed_localUnits`, `isClosed_localUnitsOne`]
- Used by: `isClosed_cycloTower1`, `isClosed_val_cycloClosureOne`
- Visibility: public
- Lines: 833-841 (proof ~8 lines)
- Notes: none

### theorem Coleman.isClosed_cycloTower1
- Type: `IsClosed (cycloTower1 p : Set (NormCompatUnits p))`
- What: `𝒞_{∞,1}` is closed in `𝒰_∞` (the inverse-limit topology ST1).
- How: It is `⋂_{n≥1}` of the preimages, under the continuous unit coordinate `u ↦ u.elems n` (`continuous_elemsUnits`), of the closed level sets `cycloClosureOne p n` (`isClosed_cycloClosureOne`); `isClosed_iInter`.
- Hypotheses: `p` prime.
- Uses from project: [`cycloTower1`, `NormCompatUnits`, `cycloClosureOne`, `isClosed_cycloClosureOne`, `continuous_elemsUnits`]
- Used by: unused in file
- Visibility: public
- Lines: 847-856 (proof ~9 lines)
- Notes: none

### theorem Coleman.isClosed_val_cycloClosureOne
- Type: `(n : ℕ) : IsClosed ((fun u : ℂ_[p]ˣ => (u : ℂ_[p])) '' (cycloClosureOne p n : Set ℂ_[p]ˣ))`
- What: The value set `C_n := val '' 𝒞_{n,1}` is closed in `ℂ_[p]`.
- How: `isSeqClosed_iff_isClosed`; a convergent sequence `x k = val(u k)` lands in the clopen ball `B(1,1)` (`IsUltrametricDist.isClosed_ball`), so the limit `y` is a unit (`‖y−1‖<1` ⟹ `y≠0`), `u k → y.unit` in `ℂ_[p]ˣ` (`Units.isEmbedding_val₀.tendsto_nhds_iff`), and `𝒞_{n,1}` is seq-closed (`isClosed_cycloClosureOne`).
- Hypotheses: level `n`.
- Uses from project: [`cycloClosureOne`, `localUnitsOne`, `mem_localUnitsOne_iff`, `isClosed_cycloClosureOne`]
- Used by: `isCompact_colemanPairSet`
- Visibility: public
- Lines: 863-900 (proof ~37 lines)
- Notes: long(30-50); none

### def Coleman.colemanPairSet
- Type: `Set (PowerSeries ℤ_[p] × PowerSeries ℤ_[p])`
- What: The compact set of Coleman-series pairs realising `𝒞_{∞,1}`: pairs `(f, finv)` with `f·finv = 1`, `f` `𝒩`-fixed, and `f(π_n) ∈ C_n := val '' 𝒞_{n,1}` for all `n ≥ 1`.
- How: Set-builder with the three conditions (`normOp`, `evalPi`, image-of-`cycloClosureOne`).
- Hypotheses: `p` prime.
- Uses from project: [`normOp`, `evalPi`, `cycloClosureOne`]
- Used by: `isCompact_colemanPairSet`, `col_image_eq_pipe_image`, `isCompact_col_image`
- Visibility: public
- Lines: 904-907 (def)
- Notes: none

### theorem Coleman.isCompact_colemanPairSet
- Type: `IsCompact (colemanPairSet p)`
- What: `colemanPairSet` is closed in `ℤ_p⟦T⟧ × ℤ_p⟦T⟧` (hence compact).
- How: `IsClosed.isCompact`; the three conditions are closed — `f·finv = 1` (`isClosed_eq`, continuous `*` into T2 ring), `𝒩 f = f` (`normOp_continuous`), and `⋂_{n≥1}` of `f(π_n) ∈ C_n` (`continuous_evalPi` ∘ `fst`, `isClosed_val_cycloClosureOne`).
- Hypotheses: `p` prime.
- Uses from project: [`colemanPairSet`, `normOp`, `normOp_continuous`, `evalPi`, `continuous_evalPi`, `cycloClosureOne`, `isClosed_val_cycloClosureOne`]
- Used by: `isCompact_col_image`
- Visibility: public
- Lines: 913-936 (proof ~23 lines)
- Notes: none

### theorem Coleman.col_image_eq_pipe_image
- Type: `Col p '' (cycloTower1 p) = Function.uncurry (colemanPipe2 p) '' colemanPairSet p`
- What: `Col '' 𝒞_{∞,1} = colemanPipe2 '' colemanPairSet`.
- How: Two-sided subset. `⊆`: `c ↦ (colemanSeries c, (colemanSeries c)⁻¹)` lands in `colemanPairSet` (`Ring.mul_inverse_cancel`, `normOp_colemanSeries`, `evalPi_colemanSeries`) and maps to `Col c` (`colemanPipe2_eq_Col`). `⊇`: `(f, finv)` has `f` a `𝒩`-fixed unit (`IsUnit.of_mul_eq_one`, `finv = Ring.inverse f`), so `invColeman f ∈ 𝒞_{∞,1}` (`colemanSeries_invColeman`, `Units.ext`) with `colemanPipe2 f finv = Col (invColeman f)`.
- Hypotheses: `p` prime.
- Uses from project: [`Col`, `cycloTower1`, `colemanPipe2`, `colemanPairSet`, `colemanSeries`, `colemanSeries_isUnit`, `normOp_colemanSeries`, `evalPi_colemanSeries`, `colemanPipe2_eq_Col`, `invColeman`, `colemanSeries_invColeman`]
- Used by: `isCompact_col_image`
- Visibility: public
- Lines: 943-973 (proof ~30 lines)
- Notes: long(30-50); none

### theorem Coleman.isCompact_col_image
- Type: `IsCompact (Col p '' (cycloTower1 p : Set (NormCompatUnits p)))`
- What: `Col '' 𝒞_{∞,1}` is compact (continuous image of the compact `colemanPairSet`).
- How: `col_image_eq_pipe_image` then `(isCompact_colemanPairSet p).image (continuous_colemanPipe2 p)`.
- Hypotheses: `p` prime.
- Uses from project: [`Col`, `cycloTower1`, `col_image_eq_pipe_image`, `isCompact_colemanPairSet`, `continuous_colemanPipe2`]
- Used by: `isClosed_col_image`
- Visibility: public
- Lines: 977-980 (proof ~2 lines)
- Notes: none

### theorem Coleman.isClosed_col_image
- Type: `IsClosed (Col p '' (cycloTower1 p : Set (NormCompatUnits p)))`
- What: `Col '' 𝒞_{∞,1}` is closed in the weak-* topology on `Λ(ℤ_p^×)`.
- How: `(isCompact_col_image p).isClosed` (compact in Hausdorff ⟹ closed).
- Hypotheses: `p` prime.
- Uses from project: [`Col`, `cycloTower1`, `isCompact_col_image`]
- Used by: unused in file
- Visibility: public
- Lines: 982-984 (proof ~1 line)
- Notes: none

### def Coleman.glueLevel0
- Type: `(m u : NormCompatUnits p) : NormCompatUnits p`
- What: Re-glue at level `0`: keeps `m`'s levels `≥ 1` but takes `u`'s level-`0` coordinate; used to re-set a witness's free level-`0` coordinate (which `Col` ignores) to land in a neighbourhood box.
- How: Structure with `elems k := if k = 0 then u.elems 0 else m.elems k`, and `mem`/`inv_mem`/`compat` discharged by case split on `k = 0` (`u`'s data at 0, `m`'s otherwise).
- Hypotheses: `m, u` norm-compatible systems.
- Uses from project: [`NormCompatUnits`, `NormCompatUnits.compat`/`.mem`/`.inv_mem`]
- Used by: `glueLevel0_elems_zero`, `glueLevel0_elems_of_pos`, `Col_mem_closure_image_of_levelwise`
- Visibility: public
- Lines: 989-1001 (def/structure-build ~13 lines)
- Notes: none

### theorem Coleman.glueLevel0_elems_zero
- Type: `(m u : NormCompatUnits p) : (glueLevel0 p m u).elems 0 = u.elems 0`
- What: `glueLevel0 m u` takes `u`'s level-`0` element.
- How: `simp [glueLevel0]`.
- Hypotheses: `m, u` systems.
- Uses from project: [`NormCompatUnits`, `glueLevel0`]
- Used by: `Col_mem_closure_image_of_levelwise`
- Visibility: public (`@[simp]`)
- Lines: 1003-1004 (proof ~1 line)
- Notes: none

### theorem Coleman.glueLevel0_elems_of_pos
- Type: `(m u : NormCompatUnits p) {n} (hn : 1 ≤ n) : (glueLevel0 p m u).elems n = m.elems n`
- What: At levels `n ≥ 1`, `glueLevel0 m u` agrees with `m`.
- How: `simp` with `if_neg (n ≠ 0)`.
- Hypotheses: `1 ≤ n`.
- Uses from project: [`NormCompatUnits`, `glueLevel0`]
- Used by: `Col_mem_closure_image_of_levelwise`
- Visibility: public
- Lines: 1006-1008 (proof ~1 line)
- Notes: none

### theorem Coleman.Col_mem_closure_image_of_levelwise
- Type: `{S : Subgroup (NormCompatUnits p)} {u} (h : ∀ n, 1 ≤ n → (u.elems n : ℂ_[p]) ∈ closure (level-n image of S)) : Col p u ∈ closure (Col p '' S)`
- What: The level-`0`-saturated Col-density (drives RJW LemmaGeneratorCinfty1's inverse-limit step): if every level-`n` (`n≥1`) coordinate of `u` is in the closure of `S`'s level-`n` image, then `Col u ∈ closure(Col '' S)`. No level-`0` hypothesis needed.
- How: `mem_closure_iff_nhds`; pull a weak-* neighbourhood `W` of `Col u` back through `continuous_Col` to a Pi box; reduce to finite `I`, infimum radius `ε`, `δ` from `exists_delta_descent`; a witness `m ∈ S` matching `u` on levels `≥ 1` (`Metric.mem_closure_iff`) is re-glued at level `0` (`glueLevel0`) without changing `Col` (`Col_eq_of_elems_eq`), landing in the box.
- Hypotheses: `S` a subgroup; each higher level (`n≥1`) of `u` in the closure of `S`'s level-`n` image.
- Uses from project: [`NormCompatUnits`, `Col`, `continuous_Col`, `elemsCoe`, `exists_delta_descent`, `Col_eq_of_elems_eq`, `glueLevel0`, `glueLevel0_elems_zero`, `glueLevel0_elems_of_pos`]
- Used by: unused in file
- Visibility: public
- Lines: 1016-1056 (proof ~40 lines)
- Notes: long(30-50); none

---

## File Summary

- **Total declarations: 51** — defs: 8 (`approxDirac`, `elemsCoe`, `colemanPipe2`, `normFixedUnits`, `colEval`, `colSec`, `colemanPairSet`, `glueLevel0`); lemmas+theorems: 36; instances: 7 (`PadicMeasure.instTopologicalSpace`, `instT2Space`; `Coleman` `SequentialSpace`, `instTopologicalSpace`, `instT2Space`, plus the 4 local `NormedAlgebra`/`NNF`/`NS`/`CompleteSpace` instances + `instCompactSpace`, `instCompactSpace_normFixedUnits` — note `PadicMeasure.instCompactSpace` is also an instance). (Counting all `instance` keywords: 9.)
- **Key API (used by ≥3 in-file):**
  - `PadicMeasure.instTopologicalSpace` — used by ≥6 (continuous_eval, continuous_iff_eval, instT2Space, tendsto_approxDirac, isClosed_range_coe, instCompactSpace)
  - `PadicMeasure.approxDirac` — used by 4
  - `Coleman.elemsCoe` — used by ≥5
  - `Coleman.instTopologicalSpace` (Coleman) — used by ≥4
  - `Coleman.continuous_iff_elems` — used by 3 (continuous_colEval, continuous_colSec, continuous_inv_NCU)
  - `Coleman.colemanPipe2` — used by 5
  - `Coleman.normFixedUnits` — used by ≥5
  - `Coleman.colEval` — used by 4
  - `Coleman.continuous_evalPi` — used by ≥3
  - `Coleman.cycloClosureOne`/`isClosed_cycloClosureOne` — used by 3
  - `Coleman.colemanPairSet` — used by 3
- **Unused in file (terminal / exported API):** `PadicMeasure.mul_mem_of_dirac_mul_mem`, `PadicMeasure.isClosed_zetaIdeal`, `Coleman.instT2Space` (Coleman), `Coleman.mem_closure_of_levelwise`, `Coleman.isClosed_cycloTower1`, `Coleman.isClosed_col_image`, `Coleman.Col_mem_closure_image_of_levelwise`. (These are the file's exported endpoints for downstream §12.5 / LemmaGeneratorCinfty1 use.)
- **Declarations with `sorry`: NONE.**
- **`set_option`:** `continuous_levelNorm` (lines 362, 365) — `synthInstance.maxHeartbeats 1000000` and `maxHeartbeats 1000000`.
- **Proofs >50 lines (OVER-50): 0.**
- **Proofs 30-50 lines (long): 5** — `mem_closure_of_levelwise` (~38), `continuous_ofPowerSeries_apply` (~40), `isClosed_val_cycloClosureOne` (~37), `col_image_eq_pipe_image` (~30), `Col_mem_closure_image_of_levelwise` (~40).
