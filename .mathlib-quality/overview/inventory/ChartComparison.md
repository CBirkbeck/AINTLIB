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
- **Used by**: `chartBIPkg` (the `dense` field)
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
- **Used by**: `chartBIPkg` (the `isUniformInducing` field)
- **Visibility**: public
- **Lines**: 230–247 (proof ≈ 10 lines)
- **Notes**: `[]`

### `theorem range_chartToBIProd`
- **Type**: `(b : ℕ) (hb : 0 < b) : Set.range (⇑(chartToBIProd … b hb)) = Set.range (⇑(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))`
- **What**: The chart map and the diagonal `Bloc → hatK × hatK` map have the same image in the product.
- **How**: Double inclusion via the ring equivalence `blocEquivAwayChartS`: forward by composing, backward by feeding `(blocEquivAwayChartS …).symm y` and cancelling with `RingEquiv.apply_symm_apply`.
- **Hypotheses**: `0 < b`; radii hypotheses.
- **Uses from project**: `chartToBIProd`, `BIProd`, `blocEquivAwayChartS`
- **Used by**: `presheafChartToBIProd_mem_BISub`
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

### `def presheafChartRingEquivBISub`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 : v(ϖ) = ρ₁) (hexact2 : ρ₂ ^ a = v(ϖ) ^ b) : presheafValue (chartData p F ϖ 1 b a b) ≃+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: **ID2d, the comparison theorem** — `𝒪_Y(U) ≅ B^I` as topological rings at the exact chart interval (Kedlaya Lemma 4.9 case 3 over the `A_inf`-base).
- **How**: Takes `presheafChartToBI` as the forward ring hom and the *inverse of the uniform equivalence* `chartCompletionUniformEquiv⁻¹` as the backward map; the two inverse laws follow from `presheafChartToBI_eq_compare` (which says the two forward maps coincide) plus `UniformEquiv.symm_apply_apply` / `UniformEquiv.apply_symm_apply`, and `map_mul'`/`map_add'` are inherited from the ring hom.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness `hexact1`, `hexact2`; `include hρ₁0 hρ₂0`.
- **Uses from project**: `presheafChartToBI`, `chartCompletionUniformEquiv`, `presheafChartToBI_eq_compare`, `vpi_le_rho2_of_exact`, `rho1_pow_le_of_exact`, `chartData`, `presheafValue`, `BISub`
- **Used by**: `presheafChartRingEquivBISub_continuous`, `presheafChartRingEquivBISub_symm_continuous`, `isSheafy_presheafChart`
- **Visibility**: public, `noncomputable`
- **Lines**: 436–475 (structure literal ≈ 29 lines)
- **Notes**: the file's headline theorem; hand-built `≃+*` rather than `RingEquiv.ofBijective` because the inverse must be the *uniform* inverse (so it is continuous).

### `theorem presheafChartRingEquivBISub_continuous`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : Continuous (presheafChartRingEquivBISub …)`
- **What**: The comparison isomorphism `𝒪_Y(U) → B^I` is continuous.
- **How**: Its underlying map is the corestriction of a `UniformSpace.Completion.extension`, so `Continuous.subtype_mk` applied to `UniformSpace.Completion.continuous_extension` (at the chart datum's uniform space) suffices.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness.
- **Uses from project**: `presheafChartRingEquivBISub`, `chartData`, `RationalLocData.uniformSpace`
- **Used by**: `isSheafy_presheafChart`
- **Visibility**: public
- **Lines**: 477–487 (term-mode, 3 lines)
- **Notes**: `[]`

### `theorem presheafChartRingEquivBISub_symm_continuous`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : Continuous (presheafChartRingEquivBISub …).symm`
- **What**: The inverse comparison isomorphism `B^I → 𝒪_Y(U)` is continuous — so together with the previous lemma the comparison is a topological ring isomorphism.
- **How**: The inverse is by construction the underlying map of `(chartCompletionUniformEquiv …).symm`, so its `UniformEquiv.continuous` field gives the result directly.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness.
- **Uses from project**: `presheafChartRingEquivBISub`, `chartCompletionUniformEquiv`
- **Used by**: `isSheafy_presheafChart`
- **Visibility**: public
- **Lines**: 489–498 (term-mode, 2 lines)
- **Notes**: `[]`

### `theorem isSheafy_presheafChart`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (hexact1 …) (hexact2 …) : letI … ; ValuationSpectrum.IsSheafy (presheafValue (chartData p F ϖ 1 b a b))` (statement carries four `letI` instance packages in its telescope: the transported `PlusSubring`, `IsHuberRing`, right-uniformity `CompleteSpace`, and `IsRingOfIntegralElements`)
- **What**: **ID2e — the chart presheaf value is sheafy**: `𝒪_Y(U)` is a sheafy Huber pair, obtained by transporting sheafiness of `B^I` across the comparison isomorphism.
- **How**: Sets `e := (presheafChartRingEquivBISub …).symm` with continuity both ways from the two continuity lemmas; installs the `B^I`-side instance package (`BIPlusIn` as plus subring, `completeSpace_right_BISub`, `isRingOfIntegralElements_BIPlusIn`), proves `B^I` itself sheafy via `isSheafy_BISub` at `j = n = 1` (needing `ρ₁ ≤ ρ₂` from `vpi_le_rho2_of_exact` and the bound `wI (BIProd (teichPowOverP …)) ≤ 1` from `wI_teichPowOverP_le_one` + `perfectoidValuation_pow_toOF`), upgrades the target to a Tate ring via `isTateRing_congr e he he'`, mirrors the instance package across `e` (`Subring.map`, `IsRingOfIntegralElements.map`, `completeSpace_right_presheafValue`), and concludes with `ValuationSpectrum.isSheafy_mapRingEquiv e he he' rfl`.
- **Hypotheses**: `0 < a`, `0 < b`, `b ≤ a`, exactness `hexact1`, `hexact2`; `include hρ₁0 hρ₂0`.
- **Uses from project**: `presheafChartRingEquivBISub`, `presheafChartRingEquivBISub_continuous`, `presheafChartRingEquivBISub_symm_continuous`, `isTateRing_congr`, `completeSpace_right_presheafValue`, `completeSpace_right_BISub`, `isSheafy_BISub`, `BISub`, `BIPlusIn`, `BIProd`, `BIProd_mem_BISub`, `isRingOfIntegralElements_BIPlusIn`, `wI`, `wI_teichPowOverP_le_one`, `teichPowOverP`, `perfectoidValuation_pow_toOF`, `vpi_le_rho2_of_exact`, `ValuationSpectrum.isSheafy_mapRingEquiv`, `ValuationSpectrum.PlusSubring`, `ValuationSpectrum.ringPlus`, `chartData`, `presheafValue`
- **Used by**: unused in file (terminal result of the module)
- **Visibility**: public
- **Lines**: 500–591 (statement ≈ 42 lines, proof ≈ 50 lines)
- **Notes**: >30-line proof **and** >30-line statement — by far the largest declaration in the file; the `letI` instance package appears twice (once in the statement telescope, once inside the proof) because the statement must expose the instances it is stated relative to.

### `def rhoRight`
- **Type**: `(a b : ℕ) : NNReal`
- **What**: The right endpoint `|ϖ|^{b/a}` of the `U₀`-chart interval, as a real (rpow) power of the perfectoid valuation of the pseudo-uniformizer.
- **How**: `perfectoidValuation p F ϖ ^ ((b : ℝ) / (a : ℝ))` using `NNReal.rpow`.
- **Hypotheses**: none (defined for all `a b : ℕ`; positivity/`< 1` are separate lemmas).
- **Uses from project**: `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `rhoRight_pos`, `rhoRight_lt_one`, `rhoRight_pow_exact`
- **Visibility**: public, `noncomputable`
- **Lines**: 593–597 (def, 2 lines)
- **Notes**: this is what supplies a genuine `ρ₂` satisfying the exactness hypothesis `ρ₂ ^ a = |ϖ| ^ b` for arbitrary `a`, `b`.

### `theorem vpi_pos`
- **Type**: `0 < perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)`
- **What**: The perfectoid valuation of a pseudo-uniformizer is strictly positive.
- **How**: `pos_iff_ne_zero` plus `Valuation.ne_zero_iff`, reducing to `ϖ ≠ 0`, which is `PseudoUniformizer.toOF_ne_zero` after `Subtype.ext`.
- **Hypotheses**: `ϖ` a pseudo-uniformizer (nonzero by definition).
- **Uses from project**: `perfectoidValuation`, `PseudoUniformizer.toOF`, `PseudoUniformizer.toOF_ne_zero`, `OF`
- **Used by**: `rhoRight_pos`
- **Visibility**: public
- **Lines**: 599–602 (proof 2 lines)
- **Notes**: `[]`

### `theorem rhoRight_pos`
- **Type**: `(a b : ℕ) : 0 < rhoRight p F ϖ a b`
- **What**: The chart interval's right endpoint is strictly positive.
- **How**: Unfold `rhoRight` and apply `NNReal.rpow_pos` to `vpi_pos`.
- **Hypotheses**: none beyond the ambient variables.
- **Uses from project**: `rhoRight`, `vpi_pos`
- **Used by**: unused in file (supplies `hρ₂0` for downstream instantiations)
- **Visibility**: public
- **Lines**: 604–606 (proof 2 lines)
- **Notes**: `[]`

### `theorem rhoRight_lt_one`
- **Type**: `(a b : ℕ) (ha : 0 < a) (hb : 0 < b) : rhoRight p F ϖ a b < 1`
- **What**: The chart interval's right endpoint is `< 1`.
- **How**: `NNReal.rpow_lt_one` applied to `perfectoidValuation_toOF_lt_one` (the base is `< 1`) with the exponent `b / a > 0` discharged by `positivity` after casting `ha`, `hb` to `ℝ`.
- **Hypotheses**: `0 < a`, `0 < b` (needed for a strictly positive exponent).
- **Uses from project**: `rhoRight`, `perfectoidValuation_toOF_lt_one`
- **Used by**: unused in file (supplies `hρ₂1` for downstream instantiations)
- **Visibility**: public
- **Lines**: 608–614 (proof 5 lines)
- **Notes**: `[]`

### `theorem rhoRight_pow_exact`
- **Type**: `(a b : ℕ) (ha : 0 < a) : rhoRight p F ϖ a b ^ a = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b`
- **What**: `rhoRight` satisfies exactly the `hexact2` hypothesis `ρ₂ ^ a = |ϖ| ^ b` demanded by every comparison result above.
- **How**: Converts the natural power to an rpow (`NNReal.rpow_natCast`), merges exponents with `NNReal.rpow_mul`, cancels `(b/a) * a = b` by `div_mul_cancel₀` using `a ≠ 0`, and converts back.
- **Hypotheses**: `0 < a` (so `(a : ℝ) ≠ 0` for the cancellation).
- **Uses from project**: `rhoRight`, `perfectoidValuation`, `PseudoUniformizer.toOF`
- **Used by**: unused in file (the key instantiation lemma for `hexact2` downstream)
- **Visibility**: public
- **Lines**: 616–622 (proof 3 lines)
- **Notes**: `[]`

### `theorem two_le_p_add_one`
- **Type**: `2 ≤ p + 1`
- **What**: For a prime `p`, `2 ≤ p + 1`.
- **How**: `Nat.Prime.two_le` from the `Fact (Nat.Prime p)` instance, then `omega`.
- **Hypotheses**: `[Fact (Nat.Prime p)]`.
- **Uses from project**: `[]`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 625–628 (proof 2 lines)
- **Notes**: arithmetic scrap unrelated to the chart comparison — a candidate for deletion or relocation.

---

### File Summary

**Total declarations: 29 top-level** — **6 defs** (`chartToBI`, `chartBIPkg`, `chartCompletionUniformEquiv`, `presheafChartToBI`, `presheafChartRingEquivBISub`, `rhoRight`; all `noncomputable`), **23 theorems**, **0 named instances**, **0 structures/classes/abbrevs**. Plus **1 anonymous local instance** at line 76 (`noncomputable local instance : DecidableEq (Ainf p F) := Classical.decEq _`).

**Key API used by 3+ other declarations (in-file):**
- `chartToBI` (line 88) — 7 in-file consumers (`chartToBI_coe`, `denseRange_chartToBI`, `tendsto_chartToBI`, `comap_nhds_zero_chartToBI_le`, `comap_nhds_zero_chartToBI`, `isInducing_chartToBI`, `isUniformInducing_chartToBI`) plus `chartBIPkg`. The load-bearing definition of the module.
- `presheafChartRingEquivBISub` (line 440) — 3 in-file consumers (`_continuous`, `_symm_continuous`, `isSheafy_presheafChart`); 4 downstream files.
- `vpi_le_rho2_of_exact` / `rho1_pow_le_of_exact` (lines 349 / 367) — 3 in-file consumers each (`presheafChartToBI_eq_compare`, `presheafChartRingEquivBISub`, and — for the former — `isSheafy_presheafChart`); both also used downstream.
- `chartCompletionUniformEquiv` (line 334) — 3 in-file consumers (`presheafChartToBI_eq_compare`, `presheafChartRingEquivBISub`, `presheafChartRingEquivBISub_symm_continuous`).
- `presheafChartToBI` (line 374) — 3 in-file consumers.
- From other project files, the imported workhorses appearing 3+ times: `chartData`, `chartS`, `BISub`, `BIProd`, `chartUniformity`, `blocEquivAwayChartS` (10 occurrences), `perfectoidValuation`/`PseudoUniformizer.toOF`.

**Declarations unused inside this file** (none are instances or `@[simp]`, so in-file-unused = genuinely terminal or export-only; downstream usage checked by grep over `projects/`):
| decl | kind | downstream consumers |
|---|---|---|
| `isTateRing_congr` | theorem (not an instance, not `@[simp]`) | used in `ChartVObj.lean`, `ChartSpa.lean` — **live** |
| `completeSpace_right_presheafValue` | theorem | `ChartVObj.lean`, `CurveVChart.lean`, `YStalks.lean`, `CurveAdicPresentation.lean` — **live** |
| `isSheafy_presheafChart` | theorem (terminal result ID2e) | `ChartVObj.lean`, `BigWindows.lean`, `YStalks.lean` — **live** |
| `rhoRight_pos` | theorem | `ChartBIQ.lean`, `YStalks.lean`, `CurveAdicPresentation.lean`, `ChartSpa.lean` — **live** |
| `rhoRight_lt_one` | theorem | same four files — **live** |
| `rhoRight_pow_exact` | theorem | `ChartBIQ.lean`, `YStalks.lean`, `ChartSpa.lean` — **live** |
| `two_le_p_add_one` | theorem | **NONE anywhere** — genuinely dead; an off-topic `omega` scrap (`2 ≤ p + 1`) that belongs nowhere near a chart-comparison file. Deletion candidate. |

Additionally, several declarations are used *only* in-file and have **no downstream consumers** — the internal scaffolding of the comparison: `chartToBIProd_mem_BISub`, `chartToBI_coe`, `denseRange_chartToBI`, `tendsto_chartToBI`, `comap_nhds_zero_chartToBI_le`, `comap_nhds_zero_chartToBI`, `isInducing_chartToBI`, `isUniformInducing_chartToBI`, `range_chartToBIProd`, `presheafChartToBIProd_mem_BISub`. These are correctly public (they are the documented intermediate API named in the module docstring) but could be `private` if the docstring's promises were relaxed.

**Declarations with `sorry`:** none. The file is sorry-free (`grep -nE "sorry|admit"` → no matches).

**Declarations with `set_option`:** none per-declaration. There is a single **file-level** `set_option linter.overlappingInstances false` at line 33 — a known project-wide issue in this codebase (double `variable` instance binders), not a per-proof workaround. **No `maxHeartbeats` / `maxRecDepth` bumps anywhere** in the file, consistent with the project's no-heartbeat-bump rule.

**Proofs > 30 lines (3 declarations):**
1. `presheafChartToBIProd_mem_BISub` — lines 265–307, **≈ 31-line proof**.
2. `presheafChartToBI_eq_compare` — lines 388–433, **≈ 32-line proof**.
3. `isSheafy_presheafChart` — lines 500–591, **≈ 50-line proof on top of a ≈ 42-line statement** (the statement itself carries four `letI` instance packages). By a wide margin the largest declaration; the prime `/decompose-proof` target in this file.

Also noteworthy though under the bar: `presheafChartRingEquivBISub` is a **29-line structure literal** (lines 436–475), and `denseRange_chartToBI` a 25-line proof (104–133).

**REPEATED PROOF PREAMBLES / duplicated blocks.** This file has the same disease as `ArCompletion.lean`, though at smaller scale. Ranked by extractable value:

1. **The four-instance `letI` package for a "`B^I`-like Huber pair" — 3 verbatim occurrences, ≈ 60 extractable lines.** The block
   `letI : ValuationSpectrum.PlusSubring _ := ⟨…⟩` + `letI : @CompleteSpace _ (IsTopologicalAddGroup.rightUniformSpace _) := …` + `letI : IsRingOfIntegralElements (ValuationSpectrum.ringPlus _) := …` (plus, in two of the three, an `IsHuberRing`/`IsTateRing` instance) appears **three times**: in the *statement* telescope of `isSheafy_presheafChart` (lines 509–540), for the `B^I` side inside its proof (lines 554–563), and for the `presheafValue` side inside its proof (lines 580–590). Counts confirm it: `ValuationSpectrum.PlusSubring` ×3, `IsRingOfIntegralElements` ×3, `IsTopologicalAddGroup.rightUniformSpace` ×4. **This is the ArCompletion-style pattern** — the right fix is one `def`/abbreviation packaging "the Huber-pair instance bundle of a ring `R` with plus-subring `P`", plus a transport lemma along a bicontinuous `≃+*`, which would collapse `isSheafy_presheafChart` from ~92 lines to ~15.
2. **`letI : UniformSpace (Localization.Away (chartS p F ϖ 1 b)) := chartUniformity p F ϖ a b` — 3 occurrences** (lines 218–219 in `isInducing_chartToBI`, 239–240 in `isUniformInducing_chartToBI`, 277–278 in `presheafChartToBIProd_mem_BISub`). Meets the 3+ bar. Cheap fix: a section-level `letI`/`attribute`, or make `chartUniformity` a scoped instance.
3. **The `set vπ … ; hne : a*b ≠ 0 ; le_of_pow_le_pow_left₀ ; calc vπ^(a*b) ≤ … = ρ₂^(a*b)` block — 2 verbatim occurrences** (lines 188–199 inside `comap_nhds_zero_chartToBI`, and lines 354–363 = the whole of `vpi_le_rho2_of_exact`). *Below the 3+ bar but a pure duplicate*: `comap_nhds_zero_chartToBI` should simply call `vpi_le_rho2_of_exact`, which was extracted 150 lines later and then never used to replace the original. Likewise its `hr1` block (lines 200–202) is *character-for-character* `rho1_pow_le_of_exact` (lines 370–371). **≈ 14 lines removable with zero risk.**
4. **The range-identification double-inclusion via `blocEquivAwayChartS` + `RingEquiv.apply_symm_apply` — 2 occurrences** (the `himg` `have` at lines 114–126 inside `denseRange_chartToBI`, and the whole of `range_chartToBIProd` at lines 254–263). Again the standalone lemma exists but the earlier proof does not call it. **≈ 12 lines removable.**
5. **`have hdense := @UniformSpace.Completion.denseRange_coe _ (chartData p F ϖ 1 b a b).uniformSpace` — 2 occurrences** (lines 280–281, 402–403); and **`Continuous.subtype_mk (@UniformSpace.Completion.continuous_extension _ (chartData p F ϖ 1 b a b).uniformSpace _ _ _ _) _` — 2 occurrences** (lines 405–407, 485–487). Two small extractable helpers (`denseRange_chartCoe`, `continuous_presheafChartToBI`); the second is already `presheafChartRingEquivBISub_continuous`, just inlined in the earlier proof.
6. **Named-argument boilerplate `(hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)` — 68 occurrences.** Not a *proof* preamble, but it is the single largest source of line-count in the file. It exists only because `hρ₁0 hρ₁1 hρ₂0 hρ₂1` are declared as **implicit** `variable`s (line 74). Making them instance-implicit or bundling `(ρ₁, ρ₂)` with their constraints into a single `ChartRadii` structure would cut the file's length by roughly a third with no mathematical change. This is the highest-leverage cleanup available here.

**Net extractable estimate:** roughly **90–110 lines** from items 1–5 (with item 1 alone worth ~60), plus a further large reduction from the item-6 signature refactor.
