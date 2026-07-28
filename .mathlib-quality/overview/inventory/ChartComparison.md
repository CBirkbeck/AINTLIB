# Inventory: `projects/AdicSpaces/Adic spaces/FarguesFontaine/ChartComparison.lean`

632 lines. Namespace `FarguesFontaine`. File-level `set_option linter.overlappingInstances false` (line 33); `noncomputable section` (line 35).

Imports: `«Adic spaces».FarguesFontaine.SheafyBI`, `«Adic spaces».FarguesFontaine.ChartData`,
`Mathlib.Analysis.SpecialFunctions.Pow.NNReal`, `«Adic spaces».RingEquivPresheafTransport`,
`«Adic spaces».SheafyRingEquivTransport`.

Shared `variable` block (lines 70–74): `p : ℕ` `[Fact p.Prime]`; `F` a perfectoid field of
characteristic `p` (topological, uniform, nonarchimedean); `ϖ : PseudoUniformizer F`;
implicit radii `{ρ₁ ρ₂ : NNReal}` with implicit positivity/`< 1` hypotheses
`{hρ₁0 hρ₁1 hρ₂0 hρ₂1}` (these are *implicit named* arguments, hence the pervasive
`(hρ₁0 := hρ₁0) …` call syntax throughout).

Local instance (line 76): `DecidableEq (Ainf p F) := Classical.decEq _` (unnamed local instance).

---

### `theorem isTateRing_congr`
- **Type**: `{A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) [IsTateRing A] : IsTateRing B`
- **What**: Being a Tate ring is invariant under a bicontinuous ring isomorphism: if `A` is Tate and `e : A ≃+* B` is a homeomorphism, then `B` is Tate.
- **How**: Transports the two Tate data separately — the pair of definition via `IsHuberRing.exists_pairOfDefinition … |>.mapRingEquiv e he he'`, and the topologically nilpotent unit via `Units.map e.toRingHom.toMonoidHom`, whose powers are `e ((u : A) ^ n)` by `Units.coe_map` + `map_pow`, so `(he.tendsto 0).comp hu` gives convergence to `e 0 = 0`.
- **Hypotheses**: `e` a ring equivalence with both `e` and `e.symm` continuous; `A` a Tate ring (hence Huber).
- **Uses from project**: `IsTateRing`, `IsHuberRing.exists_pairOfDefinition`, `PairOfDefinition.mapRingEquiv`, `IsTateRing.exists_topologicallyNilpotent_unit`
- **Used by**: unused in file (general-purpose transport lemma, exported for downstream `𝒪_Y(U) ≅ B^I` transport)
- **Visibility**: public
- **Lines**: 39–59 (proof ≈ 16 lines)
- **Notes**: general utility lemma, not about charts; the `hfun` `funext`/`rfl` step exists because `Units.map` coercion is not syntactically a power of the image.

### `theorem completeSpace_right_presheafValue`
- **Type**: `{A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (D : RationalLocData A) : @CompleteSpace (presheafValue D) (IsTopologicalAddGroup.rightUniformSpace (presheafValue D))`
- **What**: The value of the rational-localization presheaf at a datum `D` is complete for the *right* uniformity of its additive group.
- **How**: Since `presheafValue D` is a uniform additive group, `IsUniformAddGroup.rightUniformSpace_eq` identifies the right uniformity with the canonical one, after which the ambient completeness instance applies.
- **Hypotheses**: `A` a topological commutative ring; `D` a `RationalLocData A`.
- **Uses from project**: `presheafValue`, `RationalLocData`
- **Used by**: unused in file (bridging lemma for the `𝒪_Y(U)`-side completeness)
- **Visibility**: public
- **Lines**: 61–68 (proof 2 lines)
- **Notes**: uses `@CompleteSpace` with an explicitly supplied uniformity, since the canonical instance would otherwise be picked up.

### `theorem chartToBIProd_mem_BISub`
- **Type**: `(b : ℕ) (hb : 0 < b) (z : Localization.Away (chartS p F ϖ 1 b)) : chartToBIProd p F ϖ … b hb z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: The chart map into the product `hatK × hatK` actually takes values in the subring `B^I`.
- **How**: `B^I` is by definition the topological closure of the range of `BIProd`, and the chart map factors through `BIProd` via the ring equivalence `blocEquivAwayChartS`; so membership follows from `Subring.range.le_topologicalClosure`.
- **Hypotheses**: `0 < b`; ambient radii hypotheses `hρ₁0 hρ₁1 hρ₂0 hρ₂1`.
- **Uses from project**: `chartToBIProd`, `BISub`, `BIProd`, `blocEquivAwayChartS`, `chartS`
- **Used by**: `chartToBI`
- **Visibility**: public
- **Lines**: 78–85 (term-mode, 2 lines)
- **Notes**: `[]`

### `def chartToBI`
- **Type**: `(b : ℕ) (hb : 0 < b) : Localization.Away (chartS p F ϖ 1 b) →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: **The finite-level comparison map**: the chart localization `A_inf[1/(p[ϖ]^b)]` mapped into the interval ring `B^I`, obtained by corestricting `chartToBIProd`.
- **How**: `RingHom.codRestrict` of `chartToBIProd` along the membership proof `chartToBIProd_mem_BISub`.
- **Hypotheses**: `0 < b`; the radii hypotheses.
- **Uses from project**: `chartToBIProd`, `chartToBIProd_mem_BISub`, `BISub`, `chartS`
- **Used by**: `chartToBI_coe`, `denseRange_chartToBI`, `tendsto_chartToBI`, `comap_nhds_zero_chartToBI_le`, `comap_nhds_zero_chartToBI`, `isInducing_chartToBI`, `isUniformInducing_chartToBI`, and (indirectly) the completion-level API
- **Visibility**: public, `noncomputable`
- **Lines**: 87–93 (def)
- **Notes**: headline definition of the file.

### `theorem chartToBI_coe`
- **Type**: `@[simp] (b : ℕ) (hb : 0 < b) (z : …) : (↑(chartToBI … b hb z) : hatK p F hρ₁0 hρ₁1 × hatK p F hρ₂0 hρ₂1) = chartToBIProd … b hb z`
- **What**: The underlying element of `chartToBI z` in the product is `chartToBIProd z` — the defining computation rule for the corestriction.
- **How**: `rfl` (codRestrict is definitionally the same function).
- **Hypotheses**: `0 < b`; radii hypotheses.
- **Uses from project**: `chartToBI`, `chartToBIProd`, `hatK`
- **Used by**: `denseRange_chartToBI`
- **Visibility**: public, `@[simp]`
- **Lines**: 95–102 (proof `rfl`)
- **Notes**: `@[simp]`.

### `theorem denseRange_chartToBI`
- **Type**: `(b : ℕ) (hb : 0 < b) : DenseRange (chartToBI p F ϖ … b hb)`
- **What**: The comparison map has dense image in `B^I` — the completion of the chart localization surjects onto `B^I`.
- **How**: Rewrites density as `closure = univ` and pushes it through the subtype embedding using `Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image`; the image of the range is shown equal to `Set.range (BIProd …)` (using `blocEquivAwayChartS` and its `RingEquiv.apply_symm_apply` in both directions), and the closure of that range is `BISub` by definition (`rfl`).
- **Hypotheses**: `0 < b`; radii hypotheses.
- **Uses from project**: `chartToBI`, `chartToBI_coe`, `blocEquivAwayChartS`, `BIProd`, `BISub`, `hatK`
- **Used by**: unused in file (headline export; consumed downstream for the `𝒪_Y(U) ≅ B^I` identification)
- **Visibility**: public
- **Lines**: 104–133 (proof ≈ 25 lines)
- **Notes**: >10-line proof; the `himg` sub-proof duplicates `range_chartToBIProd` (lines 249–263) almost verbatim — see the repeated-preamble note in the summary.

### `theorem tendsto_chartToBI`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 : perfectoidValuation p F ϖ ≤ ρᵢ) (hr1 : ρ₁ ^ a ≤ v(ϖ) ^ b) (hr2 : ρ₂ ^ a ≤ v(ϖ) ^ b) : Filter.Tendsto (chartToBI … b hb) (@nhds _ (chartTopology p F ϖ a b) 0) (nhds 0)`
- **What**: The corestricted chart map is continuous at `0` when the chart topology is measured against the interval `[ρ₁, ρ₂]` compatible with `ϖ`.
- **How**: `tendsto_subtype_rng` reduces convergence in the subtype `B^I` to convergence of the coordinates, which is exactly `tendsto_chartToBIProd_coe`, matched up to `rfl` via `Filter.Tendsto.congr`.
- **Hypotheses**: `0 < b`; `v(ϖ) ≤ ρ₁`, `v(ϖ) ≤ ρ₂` and the two radius bounds `ρᵢ ^ a ≤ v(ϖ) ^ b` (the interval-containment conditions).
- **Uses from project**: `chartToBI`, `tendsto_chartToBIProd_coe`, `chartTopology`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `comap_nhds_zero_chartToBI`
- **Visibility**: public
- **Lines**: 136–149 (proof 3 lines)
- **Notes**: `[]`

### `theorem comap_nhds_zero_chartToBI_le`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hexact1 : v(ϖ) = ρ₁) (hexact2 : ρ₂ ^ a = v(ϖ) ^ b) : Filter.comap (chartToBI … b hb) (nhds 0) ≤ @nhds _ (chartTopology p F ϖ a b) 0`
- **What**: Every chart-topology neighborhood of `0` contains the pullback of a `B^I`-neighborhood — the "backward" half of the two-sided basis comparison.
- **How**: Puts the chart `nhds 0` in the `locNhd` basis via `locBasis … .hasBasis_nhds_zero` (rewritten through `chartData p F ϖ 1 b a b |>.topology`), then for each basis index `n` exhibits the explicit `wI`-ball of radius `min ρ₁ ρ₂ ^ n * v(ϖ) ^ b` (positive by `mul_pos`/`pow_pos`) using `wI_ball_mem_nhds_BISub`, and concludes with `ball_le_locNhd`.
- **Hypotheses**: `0 < a`, `0 < b`; the *exactness* conditions `v(ϖ) = ρ₁` and `ρ₂ ^ a = v(ϖ) ^ b` (i.e. `I` is exactly the chart interval).
- **Uses from project**: `chartToBI`, `chartTopology`, `chartData`, `chartT`, `chartS`, `podAinf`, `locNhd`, `locBasis`, `wI_ball_mem_nhds_BISub`, `ball_le_locNhd`, `perfectoidValuation`
- **Used by**: `comap_nhds_zero_chartToBI`
- **Visibility**: public
- **Lines**: 151–177 (proof ≈ 19 lines)
- **Notes**: >10-line proof; keyed on `ball_le_locNhd` (the quantitative comparison imported from the interval-ring side).

### `theorem comap_nhds_zero_chartToBI`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 : v(ϖ) = ρ₁) (hexact2 : ρ₂ ^ a = v(ϖ) ^ b) : Filter.comap (chartToBI … b hb) (nhds 0) = @nhds _ (chartTopology p F ϖ a b) 0`
- **What**: **The chart neighborhood filter at `0` is exactly the comap of the `B^I` one** — the topologies agree, packaged as a filter identity.
- **How**: `le_antisymm` of `comap_nhds_zero_chartToBI_le` (backward) against `Filter.tendsto_iff_comap.mp (tendsto_chartToBI …)` (forward); the four hypotheses of `tendsto_chartToBI` are derived from `hexact1`/`hexact2` by a `calc` on `vπ ^ (a*b) ≤ ρ₂ ^ (a*b)` using `pow_le_pow_of_le_one` and `le_of_pow_le_pow_left₀`.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, and the two exactness equations.
- **Uses from project**: `chartToBI`, `chartTopology`, `comap_nhds_zero_chartToBI_le`, `tendsto_chartToBI`, `perfectoidValuation`, `PseudoUniformizer.toOF`
- **Used by**: `isInducing_chartToBI`
- **Visibility**: public
- **Lines**: 179–208 (proof ≈ 21 lines)
- **Notes**: >10-line proof; the `hπ2` derivation is the only place `hab : b ≤ a` is genuinely used.

### `theorem isInducing_chartToBI`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : @Topology.IsInducing _ _ (chartTopology p F ϖ a b) _ (chartToBI … b hb)`
- **What**: The comparison map is a topological embedding-of-topologies: the chart topology is the topology induced from `B^I`.
- **How**: Both sides are topological additive groups, so `IsTopologicalAddGroup.ext` reduces equality of topologies to equality of `nhds 0`; the induced-group structure comes from `topologicalAddGroup_induced` and the chart side from `chartTopologicalRing`, and the `nhds` comparison is `comap_nhds_zero_chartToBI` after `nhds_induced`/`map_zero`.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness `hexact1`, `hexact2`.
- **Uses from project**: `chartToBI`, `chartTopology`, `chartTopologicalRing`, `comap_nhds_zero_chartToBI`, `chartS`
- **Used by**: `isUniformInducing_chartToBI`
- **Visibility**: public
- **Lines**: 210–228 (proof ≈ 11 lines)
- **Notes**: `[]`

### `theorem isUniformInducing_chartToBI`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : @IsUniformInducing _ _ (chartUniformity p F ϖ a b) _ (chartToBI … b hb)`
- **What**: **The uniform-space heart of the comparison**: the chart uniformity is the uniformity induced from `B^I`, so the completion of the chart ring embeds as `B^I`.
- **How**: For uniform additive groups a topological inducing additive map is uniformly inducing — `AddMonoidHom.isUniformInducing_of_isInducing` applied to `isInducing_chartToBI`, with the two `IsUniformAddGroup` instances supplied by `chartIsUniformAddGroup` and `isUniformAddGroup_BISub`.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness `hexact1`, `hexact2`.
- **Uses from project**: `chartToBI`, `chartUniformity`, `chartIsUniformAddGroup`, `isUniformAddGroup_BISub`, `isInducing_chartToBI`, `BISub`, `chartS`
- **Used by**: unused in file (headline export named in the module docstring)
- **Visibility**: public
- **Lines**: 230–247 (proof ≈ 10 lines)
- **Notes**: `[]`

### `theorem range_chartToBIProd`
- **Type**: `(b : ℕ) (hb : 0 < b) : Set.range (⇑(chartToBIProd … b hb)) = Set.range (⇑(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))`
- **What**: The chart map and the diagonal `Bloc → hatK × hatK` map have the same image in the product.
- **How**: Double inclusion via the ring equivalence `blocEquivAwayChartS`: forward by composing, backward by feeding `(blocEquivAwayChartS …).symm y` and cancelling with `RingEquiv.apply_symm_apply`.
- **Hypotheses**: `0 < b`; radii hypotheses.
- **Uses from project**: `chartToBIProd`, `BIProd`, `blocEquivAwayChartS`
- **Used by**: (see later chunks)
- **Visibility**: public
- **Lines**: 249–263 (proof ≈ 10 lines)
- **Notes**: this is the standalone form of the `himg` block inside `denseRange_chartToBI`.

### `theorem presheafChartToBIProd_mem_BISub`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : …) (x : presheafValue (chartData p F ϖ 1 b a b)) : presheafChartToBIProd … a b hb hπ1 hπ2 hr1 hr2 x ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: The *completion-level* chart map (defined on the presheaf value `A_inf⟨T/s⟩`, a uniform completion) also lands in `B^I`.
- **How**: Continuity plus density: `UniformSpace.Completion.denseRange_coe` puts every `x` in the closure of the image of the coercion, `UniformSpace.Completion.continuous_extension` gives continuity, and `image_closure_subset_closure_image` pushes the closure across; the image of the coercion's range is identified with `Set.range (chartToBIProd …)` via `presheafChartToBIProd_coe`, and then `range_chartToBIProd` rewrites it to `Set.range (BIProd …)`, whose closure is `BISub` by definition.
- **Hypotheses**: `0 < b`; `v(ϖ) ≤ ρ₁`, `v(ϖ) ≤ ρ₂`, `ρ₁ ^ a ≤ v(ϖ) ^ b`, `ρ₂ ^ a ≤ v(ϖ) ^ b`.
- **Uses from project**: `presheafChartToBIProd`, `presheafChartToBIProd_coe`, `chartToBIProd`, `range_chartToBIProd`, `BISub`, `chartData`, `chartUniformity`, `chartS`, `presheafValue`, `RationalLocData.coeRingHom`, `RationalLocData.uniformSpace`
- **Used by**: `presheafChartToBI`
- **Visibility**: public
- **Lines**: 265–307 (proof ≈ 31 lines)
- **Notes**: >30-line proof; the `letI : UniformSpace … := chartUniformity p F ϖ a b` opener recurs across this half of the file (see the repeated-preamble note).

### `def chartBIPkg`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 : v(ϖ) = ρ₁) (hexact2 : ρ₂ ^ a = v(ϖ) ^ b) : @AbstractCompletion (Localization.Away (chartS p F ϖ 1 b)) (chartUniformity p F ϖ a b)`
- **What**: **Packages `B^I` as an abstract completion** of the chart localization at the exact chart interval — i.e. `B^I` together with the map `chartToBI` satisfies all four axioms (complete, separated, uniformly inducing, dense range).
- **How**: Assembles the `AbstractCompletion` structure field-by-field from the results already proved: `isComplete_BISub … |>.completeSpace_coe` for completeness, `isUniformInducing_chartToBI` and `denseRange_chartToBI` for the two structural axioms; separation and the uniform structure are inferred.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness `hexact1`, `hexact2`; `include hρ₁0 hρ₁1 hρ₂0 hρ₂1`.
- **Uses from project**: `BISub`, `chartToBI`, `isComplete_BISub`, `isUniformInducing_chartToBI`, `denseRange_chartToBI`, `chartUniformity`, `chartS`
- **Used by**: `chartCompletionUniformEquiv`, `presheafChartToBI_eq_compare`
- **Visibility**: public, `noncomputable`
- **Lines**: 310–330 (structure literal ≈ 12 lines)
- **Notes**: `include hρ₁0 hρ₁1 hρ₂0 hρ₂1 in` — the pivot definition that converts all the analysis above into a universal property.

### `def chartCompletionUniformEquiv`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : presheafValue (chartData p F ϖ 1 b a b) ≃ᵤ ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: **The uniform equivalence `A_inf⟨T/s⟩ ≃ᵤ B^I`** — uniqueness of completions applied to the two abstract completions of the chart localization.
- **How**: `AbstractCompletion.compareEquiv` between mathlib's canonical `UniformSpace.Completion.cPkg` (for the chart uniformity) and `chartBIPkg`.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness `hexact1`, `hexact2`.
- **Uses from project**: `chartBIPkg`, `chartUniformity`, `chartData`, `presheafValue`, `BISub`, `chartS`
- **Used by**: `presheafChartToBI_eq_compare`, `presheafChartRingEquivBISub`
- **Visibility**: public, `noncomputable`
- **Lines**: 332–344 (def, 4 lines)
- **Notes**: `[]`

### `theorem vpi_le_rho2_of_exact`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 : v(ϖ) = ρ₁) (hexact2 : ρ₂ ^ a = v(ϖ) ^ b) : v(ϖ) ≤ ρ₂`
- **What**: At the exact chart interval, the uniformizer's valuation is bounded by the outer radius `ρ₂`.
- **How**: Raise both sides to the power `a * b` and compare: `pow_le_pow_of_le_one` (with `ρ₁ < 1` via `hexact1 ▸ hρ₁1.le`) gives `vπ^(a*b) ≤ vπ^(b*b) = (vπ^b)^b = (ρ₂^a)^b = ρ₂^(a*b)`, then `le_of_pow_le_pow_left₀` strips the exponent.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness; `include hρ₁1` (needs `ρ₁ < 1`).
- **Uses from project**: `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `presheafChartToBI_eq_compare`, `presheafChartRingEquivBISub` (and downstream API)
- **Visibility**: public
- **Lines**: 347–363 (proof ≈ 10 lines)
- **Notes**: this is the extracted standalone form of the `hπ2` block inside `comap_nhds_zero_chartToBI` (lines 191–199) — the same `calc` appears verbatim in both places.

### `theorem rho1_pow_le_of_exact`
- **Type**: `(a b : ℕ) (hab : b ≤ a) (hexact1 : v(ϖ) = ρ₁) : ρ₁ ^ a ≤ v(ϖ) ^ b`
- **What**: At the exact chart interval, `ρ₁^a ≤ |ϖ|^b` — the inner radius-containment inequality, automatic from `b ≤ a` and `ρ₁ < 1`.
- **How**: Rewrite `ρ₁` back to `v(ϖ)` with `hexact1` and apply `pow_le_pow_of_le_one` with `hab`.
- **Hypotheses**: `b ≤ a`, exactness `hexact1`; `include hρ₁1`.
- **Uses from project**: `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `presheafChartToBI_eq_compare`, `presheafChartRingEquivBISub` (and downstream API)
- **Visibility**: public
- **Lines**: 365–371 (proof 2 lines)
- **Notes**: extracted form of the `hr1` block inside `comap_nhds_zero_chartToBI` (lines 200–202).

### `def presheafChartToBI`
- **Type**: `(a b : ℕ) (hb : 0 < b) (hπ1 hπ2 hr1 hr2 : …) : presheafValue (chartData p F ϖ 1 b a b) →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: **The completion-level comparison ring homomorphism** `𝒪_Y(U) = A_inf⟨T/s⟩ → B^I`, corestricted to `B^I`.
- **How**: `RingHom.codRestrict` of `presheafChartToBIProd` along `presheafChartToBIProd_mem_BISub`.
- **Hypotheses**: `0 < b`; the four inequality hypotheses `hπ1`, `hπ2`, `hr1`, `hr2`.
- **Uses from project**: `presheafChartToBIProd`, `presheafChartToBIProd_mem_BISub`, `BISub`, `chartData`, `presheafValue`
- **Used by**: `presheafChartToBI_eq_compare`, `presheafChartRingEquivBISub`
- **Visibility**: public, `noncomputable`
- **Lines**: 373–386 (def, 4 lines)
- **Notes**: mirrors `chartToBI` one level up (completion instead of localization).

### `theorem presheafChartToBI_eq_compare`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : ⇑(presheafChartToBI … ) = ⇑(chartCompletionUniformEquiv …)`
- **What**: The concrete corestricted completion map and the abstract comparison equivalence are the **same function** — which is what makes the ring-hom structure transfer onto the uniform equivalence.
- **How**: Both maps are continuous and the coercion `A_inf[1/(p[ϖ]^b)] → 𝒪_Y(U)` has dense range, so `DenseRange.equalizer` reduces to agreement on the dense image; there `presheafChartToBIProd_coe` computes the left side and `AbstractCompletion.compare_coe` (for `cPkg` vs. `chartBIPkg`) computes the right side, both landing on `chartToBI z` by `chartToBI_coe`.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness (with `hπ`/`hr` arguments supplied by `vpi_le_rho2_of_exact` and `rho1_pow_le_of_exact`).
- **Uses from project**: `presheafChartToBI`, `presheafChartToBIProd`, `presheafChartToBIProd_coe`, `chartCompletionUniformEquiv`, `chartBIPkg`, `chartToBI`, `chartToBI_coe`, `vpi_le_rho2_of_exact`, `rho1_pow_le_of_exact`, `chartData`, `chartUniformity`, `RationalLocData.coeRingHom`
- **Used by**: `presheafChartRingEquivBISub`
- **Visibility**: public
- **Lines**: 388–433 (proof ≈ 32 lines)
- **Notes**: >30-line proof; the `hdense := @UniformSpace.Completion.denseRange_coe _ (chartData p F ϖ 1 b a b).uniformSpace` opener repeats from `presheafChartToBIProd_mem_BISub`.
