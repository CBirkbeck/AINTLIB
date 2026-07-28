# Inventory: `projects/AdicSpaces/Adic spaces/FarguesFontaine/Presentation.lean`

File length: 2398 lines. Namespace `FarguesFontaine`, inside `noncomputable section`.
Global variables: `(p : ℕ) [Fact p.Prime]`, `(F : Type u)` a perfectoid field of char `p`
(topological, uniform, nonarchimedean), `(ϖ : PseudoUniformizer F)`.
Imports only `«Adic spaces».FarguesFontaine.IntervalRing`.

---

### `theorem gaussTermF_mono_radius`
- **Type**: `{ρ₁ ρ₂ : NNReal} (h12 : ρ₁ ≤ ρ₂) (x : WittVector p F) (n : ℕ) : gaussTermF p F ρ₁ x n ≤ gaussTermF p F ρ₂ x n`
- **What**: The `n`-th Gauss term `ρⁿ · |x_n|` of a Witt vector is monotone in the radius `ρ`, because the exponent `n` is a nonnegative integer.
- **How**: Unfold `gaussTermF` on both sides and apply `mul_le_mul_of_nonneg_right` to `pow_le_pow_left₀ zero_le h12 n` (monotonicity of `ρ ↦ ρⁿ` on `NNReal`).
- **Hypotheses**: `ρ₁ ≤ ρ₂` in `NNReal`; nothing else (nonnegativity of `NNReal` does the rest).
- **Uses from project**: `gaussTermF`
- **Used by**: `wAloc_mono_radius`
- **Visibility**: public
- **Lines**: 73–77 (proof 2 lines)
- **Notes**: none

### `theorem wAloc_mono_radius`
- **Type**: `{ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) : wAloc p F ϖ hρ₁0 hρ₁1 u ≤ wAloc p F ϖ hρ₂0 hρ₂1 u`
- **What**: The Gauss value on `Aloc = A_inf[1/[ϖ]]` is monotone in the radius. This is the key asymmetry exploited by the whole file: it holds on `Aloc` but fails on `Bloc` (where `p` is inverted).
- **How**: Rewrite `wAloc` as the `gaussValueF` of the underlying Witt series via `gaussValueF_alocToWittF`, then compare the two suprema termwise with `ciSup_mono`, using `bddAbove_gaussTermF_alocToWittF` for the boundedness side condition and `gaussTermF_mono_radius` for the termwise inequality.
- **Hypotheses**: both radii strictly between `0` and `1`; `ρ₁ ≤ ρ₂`; `u` integral-in-`[ϖ]` (i.e. lives in `Aloc`, not `Bloc`).
- **Uses from project**: `gaussValueF_alocToWittF`, `gaussValueF`, `bddAbove_gaussTermF_alocToWittF`, `gaussTermF_mono_radius`, `wAloc`, `Aloc`
- **Used by**: `valued_AlocToHatK_mono`
- **Visibility**: public
- **Lines**: 79–88 (proof 4 lines)
- **Notes**: none

### `theorem valued_AlocToHatK_mono`
- **Type**: `{ρ₁ ρ₂ : NNReal} {hρ₁0 hρ₁1 hρ₂0 hρ₂1} (h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) : Valued.v (AlocToHatK p F ϖ hρ₁0 hρ₁1 u) ≤ Valued.v (AlocToHatK p F ϖ hρ₂0 hρ₂1 u)`
- **What**: The valuations of the two endpoint images of an `Aloc`-element compare in the same direction as the radii: `|u|_{ρ₁} ≤ |u|_{ρ₂}` when `ρ₁ ≤ ρ₂`.
- **How**: Transport `wAloc_mono_radius` across the identification `valued_AlocToHatK` (which says the valuation of the image in `hatK ρ` is exactly `wAloc … ρ`).
- **Hypotheses**: `ρ₁ ≤ ρ₂`, both radii in `(0,1)`; `u ∈ Aloc`.
- **Uses from project**: `valued_AlocToHatK`, `wAloc_mono_radius`, `AlocToHatK`, `Aloc`
- **Used by**: `tendsto_resAr`, `resAr_AlocToHatK`, `valued_resAr_le` (and used implicitly by the contraction estimates)
- **Visibility**: public
- **Lines**: 90–95 (proof 2 lines)
- **Notes**: none

### `theorem eventually_pair_valued_le`
- **Type**: `{ρ} {hρ0 hρ1} (z : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) : ∀ᶠ q in (comap (AlocToHatK …) (𝓝 z)) ×ˢ (comap (AlocToHatK …) (𝓝 z)), Valued.v (AlocToHatK p F ϖ hρ0 hρ1 (q.2 - q.1)) ≤ ε`
- **What**: Any two approximants of a point `z` of `hatK ρ` drawn from the approximant filter are eventually within `ε` of one another — the Cauchy condition for the approximant filter.
- **How**: Take the closed `ε`-ball around `z` (a neighbourhood by `valued_ball_mem_nhds`), pull it back on both factors with `Filter.preimage_mem_comap`, and use the ultrametric triangle inequality `Valuation.map_sub` after `sub_sub_sub_cancel_right` writes `u_y - u_x` as `(u_y - z) - (u_x - z)`.
- **Hypotheses**: `ε > 0`; `ρ ∈ (0,1)`; `z` an arbitrary point of the completion `hatK ρ`.
- **Uses from project**: `valued_ball_mem_nhds`, `AlocToHatK`, `hatK`, `Aloc`
- **Used by**: `tendsto_resAr`
- **Visibility**: public
- **Lines**: 97–113 (proof 11 lines)
- **Notes**: none

### `def resAr`
- **Type**: `{ρ₁ ρ₂ : NNReal} (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (z : hatK p F hρ₂0 hρ₂1) : hatK p F hρ₁0 hρ₁1`
- **What**: The restriction map from the larger radius `ρ₂` to the smaller radius `ρ₁`, defined as the limit (`Filter.limUnder`) of the smaller-radius images `AlocToHatK … ρ₁ u` along the filter of `Aloc`-approximants of `z`.
- **How**: A `limUnder` of the composite `u ↦ AlocToHatK … hρ₁0 hρ₁1 u` along `Filter.comap (AlocToHatK … hρ₂0 hρ₂1) (𝓝 z)`; the limit actually exists only for `z ∈ ArSub` (proved separately in `tendsto_resAr`), so the definition is total but only meaningful there.
- **Hypotheses**: both radii in `(0,1)`; no `ρ₁ ≤ ρ₂` needed for the definition itself.
- **Uses from project**: `AlocToHatK`, `hatK`, `Aloc`
- **Used by**: `tendsto_resAr`, `resAr_AlocToHatK`, `resAr_add`, `resAr_mul`, `resAr_pair_mem`, `ArToBI`, `valued_resAr_le`
- **Visibility**: public
- **Lines**: 115–120 (definition 2 lines)
- **Notes**: uses classical choice through `limUnder`; noncomputable section

### `theorem tendsto_resAr`
- **Type**: `{ρ₁ ρ₂} {hρ₁0 hρ₁1 hρ₂0 hρ₂1} (h12 : ρ₁ ≤ ρ₂) {z} (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) : Tendsto (fun u => AlocToHatK p F ϖ hρ₁0 hρ₁1 u) (comap (AlocToHatK … hρ₂0 hρ₂1) (𝓝 z)) (𝓝 (resAr … z))`
- **What**: For `z` in `A^{ρ₂}` (the closure of the `Aloc`-image), the small-radius approximants genuinely converge, and the limit is `resAr z`. This is the existence statement that makes `resAr` well-defined on `A^r`.
- **How**: The approximant filter is `NeBot` by `neBot_comap_of_mem_ArSub`; its pushforward under `g = AlocToHatK … ρ₁` is shown Cauchy by feeding `eventually_pair_valued_le` through the valued uniformity basis (`Valued.hasBasis_uniformity`) with a real `ε` produced by `exists_nnreal_lt_gamma`, contracting `ρ₂`-distances to `ρ₁`-distances via `valued_AlocToHatK_mono`. Completeness of `hatK ρ₁` (`CompleteSpace.complete`) then yields a limit `w`, and `Tendsto.limUnder_eq` identifies `resAr z = w`.
- **Hypotheses**: `ρ₁ ≤ ρ₂` (essential: the contraction direction), both radii in `(0,1)`, and crucially `z ∈ ArSub` so the approximant filter is nonempty.
- **Uses from project**: `neBot_comap_of_mem_ArSub`, `eventually_pair_valued_le`, `exists_nnreal_lt_gamma`, `valued_AlocToHatK_mono`, `resAr`, `ArSub`, `hatK`, `AlocToHatK`, `Aloc`
- **Used by**: `resAr_AlocToHatK`, `resAr_add`, `resAr_mul`, `resAr_pair_mem`, `valued_resAr_le`
- **Visibility**: public
- **Lines**: 122–158 (proof 31 lines)
- **Notes**: proof >30 lines

### `def AlocToBloc`
- **Type**: `Aloc p F ϖ →+* Bloc p F ϖ`
- **What**: The canonical ring map `A_inf[1/[ϖ]] → A_inf[1/(p[ϖ])]` inverting `p` in addition to `[ϖ]`.
- **How**: `IsLocalization.lift` for the multiplicative set `Submonoid.powers (teichPi p F ϖ)`, along `algebraMap (Ainf p F) (Bloc p F ϖ)`; the required unit condition is discharged by `isUnit_teichPi_image` raised to the `k`-th power.
- **Hypotheses**: `Aloc` is the localization of `Ainf` at powers of `[ϖ]`; `[ϖ]` is a unit in `Bloc`.
- **Uses from project**: `Aloc`, `Bloc`, `Ainf`, `teichPi`, `isUnit_teichPi_image`
- **Used by**: `AlocToBloc_algebraMap`, `BlocToHatK_AlocToBloc`, `resAr_pair_mem`, and the density/`Bloc`-in-image arguments later in the file
- **Visibility**: public
- **Lines**: 161–168 (definition 7 lines)
- **Notes**: none

### `theorem AlocToBloc_algebraMap`
- **Type**: `(x : Ainf p F) : AlocToBloc p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) x) = algebraMap (Ainf p F) (Bloc p F ϖ) x`
- **What**: `AlocToBloc` restricted to the image of `Ainf` is the structure map `Ainf → Bloc`.
- **How**: Immediate from the defining property `IsLocalization.lift_eq`.
- **Hypotheses**: `Aloc` a localization of `Ainf`.
- **Uses from project**: `AlocToBloc`, `Ainf`, `Aloc`, `Bloc`
- **Used by**: `BlocToHatK_AlocToBloc`
- **Visibility**: public, `@[simp]`
- **Lines**: 170–174 (proof 1 line)
- **Notes**: `@[simp]`

### `theorem BlocToHatK_AlocToBloc`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) : BlocToHatK p F ϖ hρ0 hρ1 (AlocToBloc p F ϖ u) = AlocToHatK p F ϖ hρ0 hρ1 u`
- **What**: The two routes `Aloc → Bloc → hatK ρ` and `Aloc → hatK ρ` agree — the endpoint maps are compatible with `AlocToBloc`.
- **How**: Prove the composite ring homs are equal by `IsLocalization.ringHom_ext` on `Submonoid.powers (teichPi …)`, checking on the image of `Ainf`, where both sides are `toHatK` by `IsLocalization.lift_eq` (and `AlocToBloc_algebraMap`); then apply the resulting equality of homs pointwise via `congrFun`/`congrArg`.
- **Hypotheses**: `ρ ∈ (0,1)`; the localization presentations of `Aloc` and `Bloc`.
- **Uses from project**: `BlocToHatK`, `AlocToBloc`, `AlocToHatK`, `AlocToBloc_algebraMap`, `toHatK`, `teichPi`, `Ainf`, `Aloc`, `Bloc`, `hatK`
- **Used by**: `resAr_pair_mem`, and the later `Bloc`-in-image / density arguments
- **Visibility**: public
- **Lines**: 176–189 (proof 12 lines)
- **Notes**: none

### `theorem map_add_comap_le_Ar`
- **Type**: `{ρ} {hρ0 hρ1} (z z' : hatK p F hρ0 hρ1) : Filter.map (fun q => q.1 + q.2) (comap (AlocToHatK …) (𝓝 z) ×ˢ comap (AlocToHatK …) (𝓝 z')) ≤ comap (AlocToHatK …) (𝓝 (z + z'))`
- **What**: Summing two approximant filters lands inside the approximant filter of the sum — the filter-level form of "approximants of a sum are sums of approximants".
- **How**: Convert `map ≤ comap` to a `Tendsto` statement, combine the two coordinate limits `Filter.tendsto_comap.comp Filter.tendsto_fst/snd` with `Tendsto.add`, and rewrite the composite using additivity `map_add` of the ring hom `AlocToHatK`.
- **Hypotheses**: `ρ ∈ (0,1)`; continuity of addition on `hatK ρ` (topological ring).
- **Uses from project**: `AlocToHatK`, `Aloc`, `hatK`
- **Used by**: `resAr_add`
- **Visibility**: public
- **Lines**: 192–218 (proof 20 lines)
- **Notes**: none

### `theorem map_mul_comap_le_Ar`
- **Type**: `{ρ} {hρ0 hρ1} (z z' : hatK p F hρ0 hρ1) : Filter.map (fun q => q.1 * q.2) (comap … ×ˢ comap …) ≤ comap (AlocToHatK …) (𝓝 (z * z'))`
- **What**: The multiplicative analogue of `map_add_comap_le_Ar`: products of approximants approximate the product.
- **How**: Same pattern — `Filter.map_le_iff_le_comap`, coordinate limits `Filter.tendsto_comap.comp Filter.tendsto_fst/snd`, `Tendsto.mul`, and `map_mul` of `AlocToHatK` to identify the composite.
- **Hypotheses**: `ρ ∈ (0,1)`; continuity of multiplication on `hatK ρ`.
- **Uses from project**: `AlocToHatK`, `Aloc`, `hatK`
- **Used by**: `resAr_mul`
- **Visibility**: public
- **Lines**: 220–246 (proof 20 lines)
- **Notes**: none

### `theorem AlocToHatK_mem_ArSub`
- **Type**: `{ρ} {hρ0 hρ1} (u : Aloc p F ϖ) : AlocToHatK p F ϖ hρ0 hρ1 u ∈ ArSub p F ϖ hρ0 hρ1`
- **What**: Every image of an `Aloc`-element lies in `A^ρ` (which is the topological closure of that image).
- **How**: `Subring.le_topologicalClosure` applied to the witness `⟨u, rfl⟩` exhibiting the point in the range subring.
- **Hypotheses**: `ρ ∈ (0,1)`; `ArSub` defined as a topological closure of the `Aloc`-range subring.
- **Uses from project**: `ArSub`, `AlocToHatK`, `Aloc`
- **Used by**: `resAr_AlocToHatK`, and later constant/`Aloc`-layer arguments
- **Visibility**: public
- **Lines**: 248–251 (proof 1 line)
- **Notes**: none

### `theorem resAr_AlocToHatK`
- **Type**: `{ρ₁ ρ₂} {hρ₁0 hρ₁1 hρ₂0 hρ₂1} (h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) : resAr … (AlocToHatK p F ϖ hρ₂0 hρ₂1 u) = AlocToHatK p F ϖ hρ₁0 hρ₁1 u`
- **What**: On the dense layer `Aloc`, the abstract restriction map is the honest smaller-radius map: `resAr` really extends `u ↦ u|_{ρ₁}`.
- **How**: Two `Tendsto` statements to the same filter and uniqueness of limits (`tendsto_nhds_unique`): one is `tendsto_resAr` at `z = AlocToHatK u` (legal by `AlocToHatK_mem_ArSub` + `neBot_comap_of_mem_ArSub`), the other is a direct ε-argument showing the small-radius images converge to `AlocToHatK … ρ₁ u`, built from `Valued.mem_nhds`, `exists_nnreal_lt_gamma`, `valued_ball_mem_nhds` and the contraction `valued_AlocToHatK_mono`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`, both radii in `(0,1)`; `hatK ρ₁` Hausdorff for limit uniqueness.
- **Uses from project**: `AlocToHatK_mem_ArSub`, `neBot_comap_of_mem_ArSub`, `tendsto_resAr`, `exists_nnreal_lt_gamma`, `valued_ball_mem_nhds`, `valued_AlocToHatK_mono`, `resAr`, `AlocToHatK`, `hatK`, `Aloc`
- **Used by**: `ArToBI` (`map_one'`, `map_zero'`), and the later constants-in-image lemmas
- **Visibility**: public
- **Lines**: 253–279 (proof 22 lines)
- **Notes**: none

### `theorem resAr_add`
- **Type**: `{ρ₁ ρ₂} {…} (h12 : ρ₁ ≤ ρ₂) {z z'} (hz : z ∈ ArSub …) (hz' : z' ∈ ArSub …) : resAr … (z + z') = resAr … z + resAr … z'`
- **What**: The restriction map is additive on `A^{ρ₂}`.
- **How**: Two limits of the same filter: `tendsto_resAr` applied to `z`, `z'` and to `z + z'` (using `add_mem` for membership), the latter pre-composed with `map_add_comap_le_Ar`; `map_add` of `AlocToHatK` rewrites the composite, and `tendsto_nhds_unique` concludes.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; both `z, z'` in `ArSub` (so both approximant filters are `NeBot` via `neBot_comap_of_mem_ArSub`).
- **Uses from project**: `neBot_comap_of_mem_ArSub`, `tendsto_resAr`, `map_add_comap_le_Ar`, `resAr`, `ArSub`, `AlocToHatK`, `hatK`, `Aloc`
- **Used by**: `ArToBI` (`map_add'`)
- **Visibility**: public
- **Lines**: 281–301 (proof 15 lines)
- **Notes**: none

### `theorem resAr_mul`
- **Type**: `{ρ₁ ρ₂} {…} (h12 : ρ₁ ≤ ρ₂) {z z'} (hz : z ∈ ArSub …) (hz' : z' ∈ ArSub …) : resAr … (z * z') = resAr … z * resAr … z'`
- **What**: The restriction map is multiplicative on `A^{ρ₂}`.
- **How**: Identical scheme to `resAr_add` with `mul_mem` and `map_mul_comap_le_Ar` in place of the additive versions, closing with `tendsto_nhds_unique` against `(h1.comp tendsto_fst).mul (h2.comp tendsto_snd)`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `z, z' ∈ ArSub`.
- **Uses from project**: `neBot_comap_of_mem_ArSub`, `tendsto_resAr`, `map_mul_comap_le_Ar`, `resAr`, `ArSub`, `AlocToHatK`, `hatK`, `Aloc`
- **Used by**: `ArToBI` (`map_mul'`)
- **Visibility**: public
- **Lines**: 303–323 (proof 15 lines)
- **Notes**: none

### `theorem resAr_pair_mem`
- **Type**: `{ρ₁ ρ₂} {…} (h12 : ρ₁ ≤ ρ₂) {z} (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) : (resAr … z, z) ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: The graph pair `(resAr z, z)` of an element of `A^{ρ₂}` lies in the interval ring `B^{[ρ₁,ρ₂]}` (defined as the closure of the range of the diagonal `Bloc`-map).
- **How**: Form the joint limit `Tendsto.prodMk_nhds` of `tendsto_resAr` (first coordinate) and `Filter.tendsto_comap` (second coordinate), observe that every approximant pair `(u|_{ρ₁}, u|_{ρ₂})` is in `Set.range (BIProd …)` — witnessed by `AlocToBloc u` via `BlocToHatK_AlocToBloc` on each leg — and conclude by `mem_closure_of_tendsto`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`, both radii in `(0,1)`, `z ∈ ArSub`.
- **Uses from project**: `neBot_comap_of_mem_ArSub`, `tendsto_resAr`, `BIProd`, `AlocToBloc`, `BlocToHatK_AlocToBloc`, `BISub`, `resAr`, `ArSub`, `AlocToHatK`, `hatK`
- **Used by**: `ArToBI`
- **Visibility**: public
- **Lines**: 325–348 (proof 18 lines)
- **Notes**: none

### `def ArToBI`
- **Type**: `{ρ₁ ρ₂} {hρ₁0 hρ₁1 hρ₂0 hρ₂1} (h12 : ρ₁ ≤ ρ₂) : ↥(ArSub p F ϖ hρ₂0 hρ₂1) →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: **The `A^r`-algebra structure on `B^I`**: the ring homomorphism `z ↦ (resAr z, z)` embedding `A^{ρ₂}` into the interval ring `B^{[ρ₁,ρ₂]}` as the graph of restriction. This is the structure Kedlaya's "Robba localizations" presentation needs.
- **How**: The underlying function is the graph pair, well-defined by `resAr_pair_mem`; the four ring-hom fields reduce (after `Subtype.ext`/`Prod.ext`, second coordinate being `rfl`) to `resAr_mul`, `resAr_add`, and — for `0`/`1` — to writing the constant as `AlocToHatK` of a constant and applying `resAr_AlocToHatK`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`, both radii in `(0,1)`.
- **Uses from project**: `resAr`, `resAr_pair_mem`, `resAr_mul`, `resAr_add`, `resAr_AlocToHatK`, `AlocToHatK`, `ArSub`, `BISub`, `hatK`
- **Used by**: `ArToBI_snd`, `ArToBI_injective`, `wI_ArToBI`, and every evaluation/presentation construction downstream
- **Visibility**: public
- **Lines**: 351–374 (definition 21 lines)
- **Notes**: none

### `theorem ArToBI_snd`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (z : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : ((ArToBI … h12 z : ↥(BISub …)) : hatK ρ₁ × hatK ρ₂).2 = (z : hatK p F hρ₂0 hρ₂1)`
- **What**: The second (large-radius) coordinate of `ArToBI z` is `z` itself.
- **How**: `rfl` — true by construction of the graph map.
- **Hypotheses**: `ρ₁ ≤ ρ₂`.
- **Uses from project**: `ArToBI`, `ArSub`, `BISub`, `hatK`
- **Used by**: used as a `simp` lemma throughout the norm computations (e.g. `wI_ArToBI`)
- **Visibility**: public, `@[simp]`
- **Lines**: 376–382 (proof: `rfl`)
- **Notes**: `@[simp]`

### `theorem ArToBI_injective`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) : Function.Injective (ArToBI p F ϖ … h12)`
- **What**: `A^{ρ₂}` embeds in `B^{[ρ₁,ρ₂]}` — the graph map is injective.
- **How**: A graph map is injective because the second coordinate recovers the input: apply `congrArg` with the projection `w ↦ (w : hatK ρ₁ × hatK ρ₂).2` to the hypothesis and finish with `Subtype.ext`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`.
- **Uses from project**: `ArToBI`, `BISub`, `ArSub`, `hatK`
- **Used by**: unused in file (headline result quoted in the module docstring)
- **Visibility**: public
- **Lines**: 384–393 (proof 5 lines)
- **Notes**: none

### `theorem valued_resAr_le`
- **Type**: `{ρ₁ ρ₂} {…} (h12 : ρ₁ ≤ ρ₂) {z} (hz : z ∈ ArSub p F ϖ hρ₂0 hρ₂1) : Valued.v (resAr … z) ≤ Valued.v z`
- **What**: The restriction map is contracting: the `ρ₁`-value of an element of `A^{ρ₂}` is at most its `ρ₂`-value. This is what makes the interval norm of an `A^r`-element equal to its right-endpoint value.
- **How**: Prove the weaker `∀ ε > 0, v(resAr z) ≤ max (v z) ε` by pushing the estimate through the limit: on the `ε`-ball around `z` every approximant `u` has `v_{ρ₂}(u) ≤ max (v z) ε` (ultrametric `Valuation.map_add` after `u = z + (u - z)`), hence `v_{ρ₁}(u) ≤ max (v z) ε` by `valued_AlocToHatK_mono`; the target set is closed (`isClosed_valued_ball`), so `IsClosed.mem_of_tendsto` with `tendsto_resAr` transfers it to `resAr z`. Then a `by_contra` + `exists_between` picks an `ε` strictly between `v z` and `v (resAr z)` for the contradiction.
- **Hypotheses**: `ρ₁ ≤ ρ₂`, both radii in `(0,1)`, `z ∈ ArSub` (needed for `tendsto_resAr` and `NeBot`).
- **Uses from project**: `neBot_comap_of_mem_ArSub`, `tendsto_resAr`, `valued_ball_mem_nhds`, `valued_AlocToHatK_mono`, `isClosed_valued_ball`, `resAr`, `ArSub`, `AlocToHatK`, `hatK`
- **Used by**: `wI_ArToBI`
- **Visibility**: public
- **Lines**: 395–426 (proof 26 lines)
- **Notes**: uses `push Not` (custom/renamed `push_neg`-style tactic)

### `theorem wI_ArToBI`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (z : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : wI p F … ((ArToBI … h12 z : ↥(BISub …)) : hatK ρ₁ × hatK ρ₂) = Valued.v (z : hatK p F hρ₂0 hρ₂1)`
- **What**: **The interval norm of an element of `A^r` is exactly its right-endpoint (`ρ₂`) value** — the two-endpoint max collapses because the left endpoint is smaller.
- **How**: `wI` is the max of the two coordinate valuations; `max_eq_right` applies because `valued_resAr_le` bounds the `ρ₁`-coordinate by the `ρ₂`-coordinate.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `z ∈ A^{ρ₂}`.
- **Uses from project**: `wI`, `ArToBI`, `valued_resAr_le`, `resAr`, `ArSub`, `BISub`, `hatK`
- **Used by**: `exists_eval_series`, `wI_evalTerm_le`, `evalArHom` norm bounds, `evalAr_le` and the `k`-variable restrictedness proofs
- **Visibility**: public
- **Lines**: 428–437 (proof 3 lines)
- **Notes**: none

### `def teichPowOverP`
- **Type**: `(zb : OF F) (n : ℕ) : Bloc p F ϖ`
- **What**: **Kedlaya's Tate variable image** `[z̄ⁿ]/p ∈ Bloc` — the element that the presentation `A^r{T}/(pT - [z̄ⁿ]) ≅ B^I` sends `T` to.
- **How**: The Teichmüller lift `WittVector.teichmuller p zb` raised to `n`, pushed into `Bloc` via `algebraMap`, times the inverse of the unit `p` (available because `isUnit_p_image` makes `p` invertible in `Bloc`).
- **Hypotheses**: `zb` in the ring of integers `OF F`; `p` invertible in `Bloc` (`isUnit_p_image`).
- **Uses from project**: `Bloc`, `Ainf`, `OF`, `isUnit_p_image`
- **Used by**: `wLoc_teichPowOverP`, `wI_teichPowOverP`, `wI_teichPowOverP_le_one`, `teichPowOverPElt`
- **Visibility**: public
- **Lines**: 440–444 (definition 3 lines)
- **Notes**: none

### `theorem wLoc_teichPowOverP`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (zb : OF F) (n : ℕ) : wLoc p F ϖ hρ0 hρ1 (teichPowOverP p F ϖ zb n) = (perfectoidValuation p F (zb : F)) ^ n / ρ`
- **What**: The Gauss value of `[z̄ⁿ]/p` at radius `ρ` is `|z̄|ⁿ/ρ` — the Teichmüller part contributes `|z̄|ⁿ` and the `1/p` contributes `1/ρ`.
- **How**: Multiplicativity of the valuation (`Valuation.map_mul`) splits the two factors; `wLoc_algebraMap` and `gaussValue_teichmuller` compute the Teichmüller factor, `wLoc_p_inv` computes `|1/p| = 1/ρ`, and a `push_cast` handles `((zb^n : OF F) : F) = (zb : F)^n`.
- **Hypotheses**: `ρ ∈ (0,1)`; `zb` integral.
- **Uses from project**: `teichPowOverP`, `wLoc`, `wLoc_algebraMap`, `wLoc_p_inv`, `gaussValue_teichmuller`, `perfectoidValuation`, `OF`
- **Used by**: `wI_teichPowOverP`
- **Visibility**: public
- **Lines**: 446–453 (proof 4 lines)
- **Notes**: none

### `theorem wI_teichPowOverP`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (zb : OF F) (n : ℕ) : wI p F … (BIProd p F ϖ … (teichPowOverP p F ϖ zb n)) = (perfectoidValuation p F (zb : F)) ^ n / ρ₁`
- **What**: The interval norm of the Tate variable is `|z̄|ⁿ/ρ₁` — the *smaller* radius dominates because the element has a pole at `p`.
- **How**: `wI_BIProd` reduces to the max of the two endpoint valuations, `valued_BlocToHatK` turns each into a `wLoc`, `wLoc_teichPowOverP` evaluates both, and `max_eq_left` picks the `ρ₁` one since `x/ρ` is antitone in `ρ` (`div_le_div_of_nonneg_left`).
- **Hypotheses**: `ρ₁ ≤ ρ₂`, both in `(0,1)`, `ρ₁ > 0` for the division.
- **Uses from project**: `wI_BIProd`, `valued_BlocToHatK`, `wLoc_teichPowOverP`, `teichPowOverP`, `BIProd`, `wI`, `perfectoidValuation`, `OF`
- **Used by**: `wI_teichPowOverP_le_one`
- **Visibility**: public
- **Lines**: 455–463 (proof 3 lines)
- **Notes**: none

### `theorem wI_teichPowOverP_le_one`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) {zb : OF F} {n : ℕ} (hzb : (perfectoidValuation p F (zb : F)) ^ n ≤ ρ₁) : wI p F … (BIProd p F ϖ … (teichPowOverP p F ϖ zb n)) ≤ 1`
- **What**: **Power-boundedness of the Tate variable**: `|[z̄ⁿ]/p|_I ≤ 1` exactly under Kedlaya's left-endpoint condition `|z̄|ⁿ ≤ ρ₁` (his `s ≥ -n⁻¹ log_c p`).
- **How**: Rewrite with `wI_teichPowOverP` and apply `div_le_one_of_le₀` to the hypothesis.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; the left-endpoint condition `|z̄|ⁿ ≤ ρ₁`.
- **Uses from project**: `wI_teichPowOverP`, `teichPowOverP`, `BIProd`, `wI`, `perfectoidValuation`, `OF`
- **Used by**: unused in file directly (headline hypothesis-check quoted in the docstring; the power-bound hypothesis `hb` of the evaluation API is what consumes it)
- **Visibility**: public
- **Lines**: 465–473 (proof 2 lines)
- **Notes**: none

### `def teichPowOverPElt`
- **Type**: `(hρ₁0 hρ₁1 hρ₂0 hρ₂1) (zb : OF F) (n : ℕ) : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: The Tate variable `[z̄ⁿ]/p` packaged as an element of the interval ring `B^I` (subtype form).
- **How**: The pair `BIProd … (teichPowOverP … zb n)` together with the membership proof `BIProd_mem_BISub`.
- **Hypotheses**: both radii in `(0,1)`.
- **Uses from project**: `BIProd`, `teichPowOverP`, `BIProd_mem_BISub`, `BISub`, `OF`
- **Used by**: unused in file (exported for downstream presentation construction)
- **Visibility**: public
- **Lines**: 475–479 (definition 3 lines)
- **Notes**: none

### `theorem wI_sum_le`
- **Type**: `{ι : Type*} (s : Finset ι) (f : ι → hatK ρ₁ × hatK ρ₂) {c : NNReal} (hf : ∀ i ∈ s, wI … (f i) ≤ c) : wI … (∑ i ∈ s, f i) ≤ c`
- **What**: The ultrametric bound for finite sums: the interval norm of a finite sum is at most the largest term norm.
- **How**: `Finset.induction`; the empty case is `wI_zero` plus `zero_le`, and the insert case uses `Finset.sum_insert` followed by the ultrametric `wI_add_le` and `max_le`.
- **Hypotheses**: `wI` is a nonarchimedean seminorm (`wI_add_le`, `wI_zero`); `s` finite.
- **Uses from project**: `wI`, `wI_zero`, `wI_add_le`, `hatK`
- **Used by**: `wI_partial_cauchy_diff`, `wI_evalTerm_sum_le`-style estimates, `evalAr_le`, and the `k`-variable slice bounds
- **Visibility**: public
- **Lines**: 481–496 (proof 10 lines)
- **Notes**: `classical`

### `theorem exists_eval_series`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (a : ℕ → ↥(ArSub …)) (ha : Tendsto (fun l => Valued.v (a l)) atTop (𝓝 0)) {b} (hbmem : b ∈ BISub …) (hb : wI … b ≤ 1) : ∃ S ∈ BISub …, Tendsto (fun n => ∑ l ∈ range n, (ArToBI … (a l)) * b ^ l) atTop (𝓝 S)`
- **What**: **A restricted series over `A^r` evaluated at a power-bounded element of `B^I` converges** (inside `B^I`). This is the convergence half of the presentation map.
- **How**: Feed the general summability criterion `exists_BI_series_limit` with the term family `ArToBI (a l) · bˡ`, whose membership is `mul_mem` of `(ArToBI (a l)).2` and `pow_mem hbmem l`, and whose norm bound is `v_{ρ₂}(a l)`: submultiplicativity `wI_mul_le`, then `wI_ArToBI` for the coefficient and `wI_pow` + `pow_le_one₀ … hb` for `bˡ`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; the coefficient values tend to `0` (restrictedness); `b ∈ B^I` and `b` power-bounded (`wI b ≤ 1`).
- **Uses from project**: `exists_BI_series_limit`, `ArToBI`, `wI_mul_le`, `wI_ArToBI`, `wI_pow`, `wI`, `BISub`, `ArSub`, `hatK`
- **Used by**: `evalAr` (via the choice of `S`), `evalArHom`
- **Visibility**: public
- **Lines**: 498–531 (proof 16 lines)
- **Notes**: none

### `theorem biUnion_antidiagonal_eq`
- **Type**: `(N : ℕ) : (Finset.range N).biUnion (fun l => Finset.antidiagonal l) = (Finset.range N ×ˢ Finset.range N).filter (fun q => q.1 + q.2 < N)`
- **What**: A combinatorial identity: the union of the antidiagonals of level `< N` is exactly the sub-`N` triangle of the `N × N` square.
- **How**: `Finset.ext` and unfolding of the membership lemmas (`Finset.mem_biUnion`, `Finset.mem_antidiagonal`, `Finset.mem_filter`, `Finset.mem_product`); forwards take `l = q.1 + q.2` and bound each coordinate by `Nat.le_add_right/left`, backwards take the level to be `q.1 + q.2`.
- **Hypotheses**: none beyond `N : ℕ`.
- **Uses from project**: []
- **Used by**: `wI_partial_cauchy_diff`
- **Visibility**: public
- **Lines**: 534–546 (proof 9 lines)
- **Notes**: none

### `theorem wI_partial_cauchy_diff`
- **Type**: `{b} (hb : wI … b ≤ 1) (A A' : ℕ → hatK ρ₁ × hatK ρ₂) {N₀ N} (hN : 2 * N₀ ≤ N) {ε M} (hA hA' : … ≤ M) (hAε hA'ε : ∀ i ≥ N₀, … ≤ ε) : wI ((∑_{i<N} A i bⁱ)(∑_{j<N} A' j bʲ) - ∑_{l<N} (∑_{i+j=l} A i A' j) bˡ) ≤ ε * M`
- **What**: **The Cauchy-product estimate.** The product of two truncated series differs from the truncated Cauchy product by a term of interval norm `≤ ε·M`, once the truncation `N` is at least `2N₀`.
- **How**: Both sides are rewritten as sums of `g q = A q.1 · A' q.2 · b^{q.1+q.2}` over the square (`Finset.sum_product`, `Finset.sum_mul_sum`) and over the triangle (`biUnion_antidiagonal_eq` + `Finset.sum_biUnion` with pairwise-disjointness of antidiagonals); `Finset.sum_sdiff_eq_sub` turns the difference into a sum over the complement, bounded termwise by `wI_sum_le`. On the complement `q.1 + q.2 ≥ N ≥ 2N₀` forces `max q.1 q.2 ≥ N₀` (`omega`), so `wI_mul_le` + `wI_pow`/`pow_le_one₀` give `wI (g q) ≤ wI(A q.1)·wI(A' q.2) ≤ ε·M` in either case.
- **Hypotheses**: `b` power-bounded; uniform bound `M` on both families; both families `≤ ε` past `N₀`; `N ≥ 2N₀` (the pigeonhole that makes one index large).
- **Uses from project**: `biUnion_antidiagonal_eq`, `wI_sum_le`, `wI_mul_le`, `wI_pow`, `wI`, `hatK`
- **Used by**: `tendsto_cauchy_product`
- **Visibility**: public
- **Lines**: 548–630 (proof 64 lines)
- **Notes**: proof >30 lines; `classical`; uses `push Not`

### `theorem tendsto_zero_of_wI_tendsto_zero`
- **Type**: `{x : ℕ → hatK ρ₁ × hatK ρ₂} (h : Tendsto (fun n => wI … (x n)) atTop (𝓝 0)) : Tendsto x atTop (𝓝 0)`
- **What**: Convergence to `0` in interval norm implies topological convergence to `0` in `hatK ρ₁ × hatK ρ₂`.
- **How**: Unfold `Filter.tendsto_def`; every neighbourhood `U` of `0` contains a `wI`-ball by `exists_wI_ball_subset`, and `h.eventually_le_const` puts the sequence eventually inside that ball.
- **Hypotheses**: `wI`-balls form a neighbourhood basis at `0` (`exists_wI_ball_subset`).
- **Uses from project**: `exists_wI_ball_subset`, `wI`, `hatK`
- **Used by**: `tendsto_cauchy_product`
- **Visibility**: public
- **Lines**: 633–646 (proof 7 lines)
- **Notes**: none

### `theorem exists_bound_of_wI_tendsto_zero`
- **Type**: `{A : ℕ → hatK ρ₁ × hatK ρ₂} (h : Tendsto (fun i => wI … (A i)) atTop (𝓝 0)) : ∃ M : NNReal, ∀ i, wI … (A i) ≤ M`
- **What**: A null family in interval norm is uniformly bounded.
- **How**: Past some `N₁` the norms are `≤ 1` (`h.eventually_le_const zero_lt_one` + `Filter.eventually_atTop`); take `M = max 1 (sup over Finset.range N₁)` and split on `N₁ ≤ i` using `Finset.le_sup` on the finite initial segment.
- **Hypotheses**: only the null hypothesis; `NNReal` is a lattice with finite sups.
- **Uses from project**: `wI`, `hatK`
- **Used by**: `tendsto_cauchy_product`
- **Visibility**: public
- **Lines**: 648–661 (proof 8 lines)
- **Notes**: none

### `theorem tendsto_cauchy_product`
- **Type**: `{b} (hb : wI … b ≤ 1) (A A' : ℕ → hatK ρ₁ × hatK ρ₂) (hA0 hA'0 : null) {S S'} (hS : partial sums of A → S) (hS' : partial sums of A' → S') : Tendsto (fun n => ∑ l ∈ range n, (∑ q ∈ antidiagonal l, A q.1 * A' q.2) * b ^ l) atTop (𝓝 (S * S'))`
- **What**: **The Cauchy product converges to the product of the limits** — the multiplicativity engine behind the presentation map `A^r{T} → B^I`.
- **How**: Bound both families by a common `MM = max M M'` (`exists_bound_of_wI_tendsto_zero` twice), then show the difference "product of partial sums minus partial Cauchy product" is null: for every `δ > 0` choose `N₁, N₂` with the families `≤ δ/2/MM` and apply `wI_partial_cauchy_diff` at `N₀ = max N₁ N₂`, `N ≥ 2N₀`, giving `≤ (δ/2/MM)·MM = δ/2 < δ` (with a separate degenerate branch when `MM = 0`); `tendsto_zero_of_wI_tendsto_zero` upgrades this to topological nullity, and `hS.mul hS'` minus the null difference plus `sub_sub_cancel` gives the claim.
- **Hypotheses**: `b` power-bounded; both coefficient families null in interval norm; both partial-sum sequences convergent.
- **Uses from project**: `exists_bound_of_wI_tendsto_zero`, `tendsto_zero_of_wI_tendsto_zero`, `wI_partial_cauchy_diff`, `wI`, `hatK`
- **Used by**: `evalAr_mul` / `evalArHom` multiplicativity
- **Visibility**: public
- **Lines**: 663–733 (proof 52 lines)
- **Notes**: proof >30 lines

### `def coeffSeq`
- **Type**: `{A : Type*} [CommRing A] (f : MvPowerSeries (Fin 1) A) (n : ℕ) : A`
- **What**: The coefficient sequence of a one-variable (`Fin 1`-indexed) multivariate power series: the `n`-th coefficient is the coefficient at the multi-index `Finsupp.single 0 n`.
- **How**: `MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) n) f`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: []
- **Used by**: `coeffSeq_zero`, `coeffSeq_add`, `coeffSeq_one`, `coeffSeq_mul`, `tendsto_valued_coeffSeq`, `evalTerm`, `evalAr`, `mvPowerSeries_ext_coeffSeq`, `sliceSeries`, and the whole evaluation API
- **Visibility**: public
- **Lines**: 735–737 (definition 2 lines)
- **Notes**: none

### `theorem coeffSeq_zero`
- **Type**: `{A} [CommRing A] (n : ℕ) : coeffSeq (0 : MvPowerSeries (Fin 1) A) n = 0`
- **What**: The coefficient sequence of the zero series is zero.
- **How**: Unfold `coeffSeq` and apply `map_zero` for the linear map `MvPowerSeries.coeff`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq`
- **Used by**: `evalAr_zero`, `sliceSeries_zero`
- **Visibility**: public, `@[simp]`
- **Lines**: 739–742 (proof 1 line)
- **Notes**: `@[simp]`

### `theorem coeffSeq_add`
- **Type**: `{A} [CommRing A] (f g : MvPowerSeries (Fin 1) A) (n : ℕ) : coeffSeq (f + g) n = coeffSeq f n + coeffSeq g n`
- **What**: The coefficient sequence is additive.
- **How**: Unfold and apply `map_add`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq`
- **Used by**: `evalAr_add`, `sliceSeries_add`
- **Visibility**: public
- **Lines**: 744–746 (proof 1 line)
- **Notes**: none

### `theorem coeffSeq_one`
- **Type**: `{A} [CommRing A] (n : ℕ) : coeffSeq (1 : MvPowerSeries (Fin 1) A) n = if n = 0 then 1 else 0`
- **What**: The coefficient sequence of `1` is the Kronecker delta at `0`.
- **How**: `MvPowerSeries.coeff_one` reduces to an `if` on multi-indices; the `n ≠ 0` branch uses `Finsupp.single_eq_zero` to transfer `Finsupp.single 0 n = 0 ↔ n = 0`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq`
- **Used by**: `evalAr_one`, `sliceSeries_one`
- **Visibility**: public
- **Lines**: 748–756 (proof 6 lines)
- **Notes**: none

### `theorem coeffSeq_mul`
- **Type**: `{A} [CommRing A] (f g : MvPowerSeries (Fin 1) A) (n : ℕ) : coeffSeq (f * g) n = ∑ q ∈ Finset.antidiagonal n, coeffSeq f q.1 * coeffSeq g q.2`
- **What**: The coefficient sequence of a product is the Cauchy product of the coefficient sequences — the bridge from `MvPowerSeries` multiplication to the one-variable convolution used in `tendsto_cauchy_product`.
- **How**: `MvPowerSeries.coeff_mul` gives a sum over the `Finsupp`-antidiagonal; `Finsupp.antidiagonal_single` identifies it with the image of the `ℕ`-antidiagonal under `Finsupp.single 0`, and `Finset.sum_map` + `rfl` finish.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq`
- **Used by**: `evalAr_mul`, `sliceSeries_mul`
- **Visibility**: public
- **Lines**: 758–763 (proof 3 lines)
- **Notes**: `classical`

### `theorem tendsto_valued_coeffSeq`
- **Type**: `{ρ} {hρ0 hρ1} {f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ0 hρ1)} (hf : MvPowerSeries.IsRestricted f) : Tendsto (fun n => Valued.v ((coeffSeq f n : ↥(ArSub …)) : hatK p F hρ0 hρ1)) atTop (𝓝 0)`
- **What**: A restricted one-variable series over `A^r` has coefficient values tending to `0` — restrictedness (a finiteness condition on multi-indices) becomes an honest sequential null condition.
- **What/How bridge**: this is what lets `exists_eval_series` be applied to a `MvPowerSeries`.
- **How**: For `δ > 0`, `isRestricted_iff_valued` gives that only finitely many multi-indices have value `> δ/2`; pull that finite set back along the injection `n ↦ Finsupp.single 0 n` (`Finsupp.single_injective`, `Set.Finite.preimage`), take an upper bound `N` from `Set.Finite.bddAbove`, and past `N + 1` the value is `≤ δ/2 < δ` by `NNReal.half_lt_self`.
- **Hypotheses**: `f` restricted; `ρ ∈ (0,1)`.
- **Uses from project**: `isRestricted_iff_valued`, `coeffSeq`, `ArSub`, `hatK`
- **Used by**: `evalAr` (via `exists_eval_series`), `evalArHom`, `wI_evalTerm_tendsto_zero`
- **Visibility**: public
- **Lines**: 765–786 (proof 16 lines)
- **Notes**: none

### `def evalTerm`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (b : hatK ρ₁ × hatK ρ₂) (f : MvPowerSeries (Fin 1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) (l : ℕ) : hatK ρ₁ × hatK ρ₂`
- **What**: The `l`-th term `a_l · bˡ` of the evaluation series of `f` at `b`, with the coefficient pushed into `B^I` by `ArToBI`.
- **How**: `(ArToBI … h12 (coeffSeq f l) : …) * b ^ l`, i.e. the coefficient image times the `l`-th power of the point.
- **Hypotheses**: `ρ₁ ≤ ρ₂` (so `ArToBI` exists); radii in `(0,1)`.
- **Uses from project**: `ArToBI`, `coeffSeq`, `ArSub`, `BISub`, `hatK`
- **Used by**: `evalAr`, `wI_evalTerm_le`-style bounds, `evalArHom`
- **Visibility**: public (in the `variable`-scoped section from line 789)
- **Lines**: 791–797 (definition 3 lines)
- **Notes**: from line 789 the radius hypotheses `ρ₁ ρ₂ hρ₁0 hρ₁1 hρ₂0 hρ₂1` become implicit `variable`s

### `def evalAr`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) {b} (hbmem : b ∈ BISub …) (hb : wI … b ≤ 1) (f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1))) : hatK ρ₁ × hatK ρ₂`
- **What**: **The value of a restricted one-variable series over `A^r` at a power-bounded point `b` of `B^I`** — the sum of `∑ a_l bˡ`.
- **How**: `.choose` of the existential produced by `exists_eval_series`, applied to the coefficient sequence `coeffSeq f` whose nullity comes from `tendsto_valued_coeffSeq f.2`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `f` in the restricted-series subring; `b ∈ B^I` power-bounded.
- **Uses from project**: `exists_eval_series`, `coeffSeq`, `tendsto_valued_coeffSeq`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `wI`, `hatK`
- **Used by**: `evalAr_mem`, `tendsto_evalAr`, `evalAr_add`, `evalAr_mul`, `evalAr_one`, `evalAr_zero`, `evalArHom`, `wI_evalAr_le`
- **Visibility**: public
- **Lines**: 799–806 (definition 2 lines)
- **Notes**: `Exists.choose` — noncomputable, opaque; all its properties come from the two `choose_spec` lemmas below

### `theorem evalAr_mem`
- **Type**: `(h12) {b} (hbmem) (hb) (f) : evalAr p F ϖ h12 hbmem hb f ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1`
- **What**: The value of the evaluation actually lies in the interval ring `B^I`.
- **How**: The first component of `Exists.choose_spec` for `exists_eval_series`.
- **Hypotheses**: as `evalAr`.
- **Uses from project**: `exists_eval_series`, `evalAr`, `coeffSeq`, `tendsto_valued_coeffSeq`, `BISub`, `ArSub`
- **Used by**: `evalArHom`
- **Visibility**: public
- **Lines**: 808–814 (proof 2 lines)
- **Notes**: none

### `theorem tendsto_evalAr`
- **Type**: `(h12) {b} (hbmem) (hb) (f) : Tendsto (fun n => ∑ l ∈ Finset.range n, evalTerm p F ϖ h12 b (f : …) l) atTop (𝓝 (evalAr p F ϖ h12 hbmem hb f))`
- **What**: The partial sums of the evaluation series converge to `evalAr f` — the defining property of the evaluation.
- **How**: The second component of `Exists.choose_spec` for `exists_eval_series` (the term family there is definitionally `evalTerm`).
- **Hypotheses**: as `evalAr`.
- **Uses from project**: `exists_eval_series`, `evalAr`, `evalTerm`, `coeffSeq`, `tendsto_valued_coeffSeq`, `BISub`, `ArSub`
- **Used by**: `evalAr_add`, `evalAr_mul`, `evalAr_one`, `evalAr_zero`, `wI_evalAr_le`, `evalArMv` restrictedness proofs
- **Visibility**: public
- **Lines**: 816–825 (proof 2 lines)
- **Notes**: none

### `theorem tendsto_wI_evalTerm`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) {f : MvPowerSeries (Fin 1) ↥(ArSub …)} (hf : MvPowerSeries.IsRestricted f) : Tendsto (fun l => wI … (ArToBI … (coeffSeq f l))) atTop (𝓝 0)`
- **What**: For a restricted series the interval norms of the coefficient images tend to `0`.
- **How**: `Filter.Tendsto.congr` against `tendsto_valued_coeffSeq`, using `wI_ArToBI` to identify each interval norm with the corresponding `ρ₂`-valuation.
- **Hypotheses**: `f` restricted; `ρ₁ ≤ ρ₂`.
- **Uses from project**: `tendsto_valued_coeffSeq`, `wI_ArToBI`, `ArToBI`, `coeffSeq`, `wI`, `ArSub`, `BISub`, `hatK`
- **Used by**: `evalAr_mul`
- **Visibility**: public
- **Lines**: 827–837 (proof 2 lines)
- **Notes**: none

### `theorem ArToBI_add`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (a a' : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : ArToBI … (a + a') = ArToBI … a + ArToBI … a'`
- **What**: Additivity of the inclusion `A^r ↪ B^I`, restated as a plain equation.
- **How**: `RingHom.map_add` of `ArToBI`; the point of the restatement is to avoid `AddMonoidHomClass` instance search on nested subring types.
- **Hypotheses**: `ρ₁ ≤ ρ₂`.
- **Uses from project**: `ArToBI`, `ArSub`
- **Used by**: `ArToBI_sum`, `evalAr_add`
- **Visibility**: public
- **Lines**: 840–847 (proof 1 line)
- **Notes**: exists purely as an elaboration-performance workaround (documented in its docstring)

### `theorem ArToBI_mul`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (a a' : ↥(ArSub p F ϖ hρ₂0 hρ₂1)) : ArToBI … (a * a') = ArToBI … a * ArToBI … a'`
- **What**: Multiplicativity of the inclusion `A^r ↪ B^I`, as a plain equation.
- **How**: `RingHom.map_mul` of `ArToBI`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`.
- **Uses from project**: `ArToBI`, `ArSub`
- **Used by**: `evalAr_mul`
- **Visibility**: public
- **Lines**: 849–855 (proof 1 line)
- **Notes**: elaboration-performance restatement

### `theorem ArToBI_sum`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) {ι : Type*} (s : Finset ι) (a : ι → ↥(ArSub …)) : ArToBI … (∑ i ∈ s, a i) = ∑ i ∈ s, ArToBI … (a i)`
- **What**: The inclusion `A^r ↪ B^I` commutes with finite sums.
- **How**: `Finset.induction` with `ArToBI_add` in the insert step and `RingHom.map_zero` in the empty step — done by hand so no `AddMonoidHomClass` search is needed on the nested subring types.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `s` finite.
- **Uses from project**: `ArToBI`, `ArToBI_add`, `ArSub`
- **Used by**: `evalAr_mul`
- **Visibility**: public
- **Lines**: 857–875 (proof 11 lines)
- **Notes**: `classical`; elaboration-performance restatement

### `theorem evalAr_add`
- **Type**: `(h12) {b} (hbmem) (hb) (f g : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub …))) : evalAr … (f + g) = evalAr … f + evalAr … g`
- **What**: Evaluation is additive in the series.
- **How**: `tendsto_nhds_unique` between `tendsto_evalAr (f+g)` and the sum of the two partial-sum limits; termwise the identification is `coeffSeq_add` followed by `ArToBI_add` and factoring out `bˡ` (`add_mul`), with `Finset.sum_add_distrib` matching the two partial sums.
- **Hypotheses**: as `evalAr`; Hausdorffness of `hatK ρ₁ × hatK ρ₂` for limit uniqueness.
- **Uses from project**: `tendsto_evalAr`, `evalTerm`, `coeffSeq_add`, `ArToBI_add`, `coeffSeq`, `evalAr`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`
- **Used by**: `evalArHom`, `evalArHom_add`
- **Visibility**: public
- **Lines**: 877–897 (proof 14 lines)
- **Notes**: none

### `theorem evalAr_mul`
- **Type**: `(h12) {b} (hbmem) (hb) (f g) : evalAr … (f * g) = evalAr … f * evalAr … g`
- **What**: **Evaluation is multiplicative** — the analytic heart of the presentation map.
- **How**: `tendsto_nhds_unique` against `tendsto_cauchy_product` applied to the two coefficient-image families (nullity from `tendsto_wI_evalTerm`, convergence from `tendsto_evalAr`); the two partial-sum sequences are matched termwise by `coeffSeq_mul` (coefficients of a product are the Cauchy convolution) followed by `ArToBI_sum` and `ArToBI_mul` to move the finite sum and products through the inclusion.
- **Hypotheses**: as `evalAr`; `b` power-bounded (needed by `tendsto_cauchy_product`); both `f, g` restricted.
- **Uses from project**: `tendsto_evalAr`, `tendsto_cauchy_product`, `tendsto_wI_evalTerm`, `coeffSeq_mul`, `ArToBI_sum`, `ArToBI_mul`, `ArToBI`, `coeffSeq`, `evalTerm`, `evalAr`, `ArSub`, `BISub`
- **Used by**: `evalArHom`, `evalArHom_mul`
- **Visibility**: public
- **Lines**: 899–932 (proof 27 lines)
- **Notes**: none

### `theorem evalAr_one`
- **Type**: `(h12) {b} (hbmem) (hb) : evalAr p F ϖ h12 hbmem hb 1 = 1`
- **What**: Evaluation sends the constant series `1` to `1`.
- **How**: The partial sums are eventually constantly `1`: by `coeffSeq_one` the `l`-th term is `1` for `l = 0` and `0` otherwise, so `Finset.sum_ite_eq'` collapses the sum over `range n` (`n ≥ 1`) to `1`; `tendsto_const_nhds.congr'` plus `tendsto_nhds_unique` with `tendsto_evalAr` concludes.
- **Hypotheses**: as `evalAr`.
- **Uses from project**: `tendsto_evalAr`, `evalTerm`, `coeffSeq_one`, `evalAr`, `ArSub`, `BISub`, `hatK`
- **Used by**: `evalArHom`
- **Visibility**: public
- **Lines**: 934–960 (proof 22 lines)
- **Notes**: none

### `theorem evalAr_zero`
- **Type**: `(h12) {b} (hbmem) (hb) : evalAr p F ϖ h12 hbmem hb 0 = 0`
- **What**: Evaluation sends the zero series to `0`.
- **How**: Every term vanishes — `coeffSeq_zero` then `map_zero` of `ArToBI` and `zero_mul` — so `Finset.sum_eq_zero` makes the partial sums constantly `0`; conclude with `tendsto_const_nhds.congr` and `tendsto_nhds_unique` against `tendsto_evalAr`.
- **Hypotheses**: as `evalAr`.
- **Uses from project**: `tendsto_evalAr`, `evalTerm`, `coeffSeq_zero`, `coeffSeq`, `evalAr`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `hatK`
- **Used by**: `evalArHom`
- **Visibility**: public
- **Lines**: 962–975 (proof 9 lines)
- **Notes**: none

### `def evalArHom`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) {b} (hbmem : b ∈ BISub …) (hb : wI … b ≤ 1) : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ₂0 hρ₂1)) →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: **Evaluation as a ring homomorphism `A^r⟨T⟩ →+* B^I`** at any power-bounded point `b` — Kedlaya's case-3 presentation map.
- **How**: The bundle of `evalAr` (well-defined into `B^I` by `evalAr_mem`) with the four algebraic laws `evalAr_one`, `evalAr_mul`, `evalAr_zero`, `evalAr_add`, each wrapped by `Subtype.ext`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `b ∈ B^I` with `wI b ≤ 1`.
- **Uses from project**: `evalAr`, `evalAr_mem`, `evalAr_one`, `evalAr_mul`, `evalAr_zero`, `evalAr_add`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `wI`, `hatK`
- **Used by**: `evalArHom_add`, `evalArHom_mul`, `evalArHom_one`, `evalArHom_zero`, `evalArHom_sum`, `evalArMv`, `evalArMvHom`, and the image/density results
- **Visibility**: public
- **Lines**: 977–988 (definition 10 lines)
- **Notes**: none

### `theorem cons_add`
- **Type**: `{k : ℕ} (a₁ a₂ : ℕ) (b₁ b₂ : Fin k →₀ ℕ) : Finsupp.cons (a₁ + a₂) (b₁ + b₂) = Finsupp.cons a₁ b₁ + Finsupp.cons a₂ b₂`
- **What**: `Finsupp.cons` (prepending a head to a `Fin k`-indexed finsupp) is additive.
- **How**: `Finsupp.ext` and `Fin.cases` on the index: `Finsupp.cons_zero` handles the head, `Finsupp.cons_succ` the tail, and `Finsupp.add_apply` distributes.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `antidiagonal_cons`
- **Visibility**: public
- **Lines**: 990–998 (proof 6 lines)
- **Notes**: none

### `theorem tail_add`
- **Type**: `{k : ℕ} (x y : Fin (k + 1) →₀ ℕ) : Finsupp.tail (x + y) = Finsupp.tail x + Finsupp.tail y`
- **What**: `Finsupp.tail` is additive.
- **How**: `Finsupp.ext` plus `Finsupp.tail_apply` and `Finsupp.add_apply`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `antidiagonal_cons`
- **Visibility**: public
- **Lines**: 1000–1004 (proof 2 lines)
- **Notes**: none

### `theorem antidiagonal_cons`
- **Type**: `{k : ℕ} (n : ℕ) (I : Fin k →₀ ℕ) : Finset.antidiagonal (Finsupp.cons n I) = ((Finset.antidiagonal n) ×ˢ (Finset.antidiagonal I)).map ⟨fun q => (Finsupp.cons q.1.1 q.2.1, Finsupp.cons q.1.2 q.2.2), _⟩`
- **What**: **The antidiagonal of a `cons` splits as a product of antidiagonals**: multi-index pairs summing to `cons n I` are exactly the consings of a pair summing to `n` onto a pair summing to `I`. This is the combinatorial identity that makes slicing compatible with multiplication.
- **How**: The embedding's injectivity is `Finsupp.cons_injective2` applied to both components. For the set equality, forwards decompose `q` as `(head, tail)` using `Finsupp.cons_tail`, with the head equation read off at index `0` (`Finsupp.cons_zero`) and the tail equation via `tail_add` + `Finsupp.tail_cons`; backwards is `cons_add` applied to the two given equations.
- **Hypotheses**: none.
- **Uses from project**: `tail_add`, `cons_add`
- **Used by**: `sliceSeries_mul`
- **Visibility**: public
- **Lines**: 1006–1034 (proof 17 lines, plus a 7-line inline injectivity proof)
- **Notes**: none

### `theorem coeffSeq_ext`
- **Type**: `{A : Type*} [CommRing A] {f g : MvPowerSeries (Fin 1) A} (h : ∀ n, coeffSeq f n = coeffSeq g n) : f = g`
- **What**: A one-variable multivariate power series is determined by its coefficient sequence.
- **How**: `MvPowerSeries.ext` on multi-indices, then observe every `m : Fin 1 →₀ ℕ` equals `Finsupp.single 0 (m 0)` — proved by `Finsupp.ext` and `Subsingleton.elim` on `Fin 1` — and apply `h (m 0)`.
- **Hypotheses**: `A` a commutative ring; `Fin 1` a subsingleton index type.
- **Uses from project**: `coeffSeq`
- **Used by**: `sliceSeries_add`, `sliceSeries_one`, `sliceSeries_zero`, `sliceSeries_mul`, and the `k`-variable identifications
- **Visibility**: public
- **Lines**: 1037–1045 (proof 6 lines)
- **Notes**: none

### `def sliceSeries`
- **Type**: `{k : ℕ} {A : Type*} [CommRing A] (f : MvPowerSeries (Fin (k + 1)) A) (I : Fin k →₀ ℕ) : MvPowerSeries (Fin 1) A`
- **What**: **The `I`-slice of a `(k+1)`-variable series**: the one-variable series in the first variable `T` obtained by fixing the exponent multi-index `I` in the remaining variables `T₁,…,T_k`.
- **How**: Directly as a coefficient function `m ↦ MvPowerSeries.coeff (Finsupp.cons (m 0) I) f`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: []
- **Used by**: `coeffSeq_sliceSeries`, `sliceSeries_add`, `sliceSeries_one`, `sliceSeries_zero`, `sliceSeries_mul`, `isRestricted_sliceSeries`, `sliceElt`, `evalArMv`
- **Visibility**: public
- **Lines**: 1047–1051 (definition 2 lines)
- **Notes**: route (a) of design decision AD-10 (per module docstring)

### `theorem coeffSeq_sliceSeries`
- **Type**: `{k} {A} [CommRing A] (f : MvPowerSeries (Fin (k+1)) A) (I : Fin k →₀ ℕ) (n : ℕ) : coeffSeq (sliceSeries f I) n = MvPowerSeries.coeff (Finsupp.cons n I) f`
- **What**: The `n`-th coefficient of the `I`-slice is the `(n, I)`-coefficient of `f`.
- **How**: Unfold both sides and simplify `(Finsupp.single (0 : Fin 1) n) 0 = n` with `Finsupp.single_eq_same`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq`, `sliceSeries`
- **Used by**: `sliceSeries_add`, `sliceSeries_one`, `sliceSeries_zero`, `sliceSeries_mul`, `isRestricted_sliceSeries`, `evalArMv` coefficient computations
- **Visibility**: public, `@[simp]`
- **Lines**: 1053–1059 (proof 3 lines)
- **Notes**: `@[simp]`

### `theorem sliceSeries_add`
- **Type**: `{k} {A} [CommRing A] (f g : MvPowerSeries (Fin (k+1)) A) (I : Fin k →₀ ℕ) : sliceSeries (f + g) I = sliceSeries f I + sliceSeries g I`
- **What**: Slicing is additive.
- **How**: `coeffSeq_ext`, then `coeffSeq_sliceSeries` on both sides and `map_add` for the coefficient functional.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq_ext`, `coeffSeq_sliceSeries`, `coeffSeq_add`, `sliceSeries`
- **Used by**: `sliceElt_add`, `evalArMv_add`
- **Visibility**: public
- **Lines**: 1061–1066 (proof 3 lines)
- **Notes**: none

### `theorem sliceSeries_one`
- **Type**: `{k} {A} [CommRing A] (I : Fin k →₀ ℕ) : sliceSeries (1 : MvPowerSeries (Fin (k+1)) A) I = if I = 0 then 1 else 0`
- **What**: The slices of the constant series `1` are `1` at `I = 0` and `0` otherwise.
- **How**: `coeffSeq_ext` and `MvPowerSeries.coeff_one`, splitting on `I = 0`; the `Finsupp.cons`-level nonvanishing conditions are supplied by `Finsupp.cons_zero_zero`, `Finsupp.cons_ne_zero_of_left` and `Finsupp.cons_ne_zero_of_right`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq_ext`, `coeffSeq_sliceSeries`, `coeffSeq_one`, `coeffSeq_zero`, `sliceSeries`
- **Used by**: `sliceElt_one`, `evalArMv_one`
- **Visibility**: public
- **Lines**: 1068–1082 (proof 11 lines)
- **Notes**: none

### `theorem sliceSeries_zero`
- **Type**: `{k} {A} [CommRing A] (I : Fin k →₀ ℕ) : sliceSeries (0 : MvPowerSeries (Fin (k+1)) A) I = 0`
- **What**: All slices of the zero series are zero.
- **How**: `coeffSeq_ext` plus `coeffSeq_sliceSeries`, `map_zero` and `coeffSeq_zero`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq_ext`, `coeffSeq_sliceSeries`, `coeffSeq_zero`, `sliceSeries`
- **Used by**: `sliceElt_zero`, `evalArMv_zero`
- **Visibility**: public
- **Lines**: 1084–1087 (proof 2 lines)
- **Notes**: none

### `theorem sliceSeries_mul`
- **Type**: `{k} {A} [CommRing A] (f g : MvPowerSeries (Fin (k+1)) A) (I : Fin k →₀ ℕ) : sliceSeries (f * g) I = ∑ q ∈ Finset.antidiagonal I, sliceSeries f q.1 * sliceSeries g q.2`
- **What**: **Slicing turns a product into the finite Cauchy product of slices** — the identity that reduces the `k`-variable evaluation to the one-variable one.
- **How**: Compare coefficients via `coeffSeq_ext`: the left side is `MvPowerSeries.coeff_mul` over the `(k+1)`-antidiagonal, which `antidiagonal_cons` + `Finset.sum_map` + `Finset.sum_product_right` refactor as a double sum over the `I`-antidiagonal and the `n`-antidiagonal; the right side unwinds by `map_sum` and `coeffSeq_mul`, and the two inner sums match termwise by `coeffSeq_sliceSeries`.
- **Hypotheses**: `A` a commutative ring.
- **Uses from project**: `coeffSeq_ext`, `coeffSeq_sliceSeries`, `antidiagonal_cons`, `coeffSeq_mul`, `sliceSeries`, `coeffSeq`
- **Used by**: `sliceElt_mul`, `evalArMv_mul`
- **Visibility**: public
- **Lines**: 1089–1114 (proof 19 lines)
- **Notes**: `classical`

### `theorem wI_evalAr_le`
- **Type**: `(h12) {b} (hbmem) (hb) (f) {ε : NNReal} (hε : 0 < ε) (hf : ∀ l, Valued.v (coeffSeq f l) ≤ ε) : wI p F … (evalAr p F ϖ h12 hbmem hb f) ≤ ε`
- **What**: **Evaluation is norm-decreasing**: if every coefficient has `ρ₂`-value at most `ε`, then so does the value of the series.
- **How**: The `ε`-ball for `wI` is closed (`isClosed_wI_ball`), so `IsClosed.mem_of_tendsto` transfers the bound from the partial sums (`tendsto_evalAr`) to the limit; each partial sum obeys the bound by the ultrametric `wI_sum_le`, and each term by `wI_mul_le` + `wI_ArToBI` + `wI_pow`/`pow_le_one₀ … hb`.
- **Hypotheses**: `ε > 0`; uniform coefficient bound `hf`; `b` power-bounded.
- **Uses from project**: `isClosed_wI_ball`, `tendsto_evalAr`, `wI_sum_le`, `evalTerm`, `wI_mul_le`, `wI_ArToBI`, `wI_pow`, `coeffSeq`, `evalAr`, `wI`, `ArSub`, `BISub`
- **Used by**: the restrictedness proof for the `k`-variable map (`evalArMv` lands in restricted series)
- **Visibility**: public
- **Lines**: 1116–1141 (proof 14 lines)
- **Notes**: none

### `theorem isRestricted_sliceSeries`
- **Type**: `{k : ℕ} {f : MvPowerSeries (Fin (k+1)) ↥(ArSub p F ϖ hρ₂0 hρ₂1)} (hf : MvPowerSeries.IsRestricted f) (I : Fin k →₀ ℕ) : MvPowerSeries.IsRestricted (sliceSeries f I)`
- **What**: Each slice of a restricted `(k+1)`-variable series is a restricted one-variable series.
- **How**: Via the valuation criterion `isRestricted_iff_valued`: the set of one-variable indices with coefficient value `> ε` embeds into the preimage of the corresponding finite set for `f` under `s ↦ Finsupp.cons (s 0) I`, injective on that set by `Finsupp.cons_injective2`; `Set.Finite.preimage` and `Set.Finite.subset` conclude.
- **Hypotheses**: `f` restricted.
- **Uses from project**: `isRestricted_iff_valued`, `sliceSeries`, `ArSub`, `hatK`
- **Used by**: `sliceElt`, `evalArMv`
- **Visibility**: public
- **Lines**: 1143–1163 (proof 16 lines)
- **Notes**: none

### `theorem isRestricted_of_wI`
- **Type**: `{k : ℕ} {c : MvPowerSeries (Fin k) ↥(BISub …)} (h : ∀ ε > 0, {I | ε < wI … (coeff I c)}.Finite) : MvPowerSeries.IsRestricted c`
- **What**: **The interval-norm criterion for restrictedness over `B^I`**: if for every `ε > 0` only finitely many coefficients exceed `ε` in interval norm, the series is restricted.
- **How**: Unfold `IsRestricted` (cofinite pushforward into every neighbourhood of `0`); a neighbourhood of `0` in the subtype comes from an ambient one (`mem_nhds_subtype`), which contains a `wI`-ball by `exists_wI_ball_subset`; then `Filter.mem_cofinite` + `Set.Finite.subset (h ε hε)` gives the finiteness.
- **Hypotheses**: `wI`-balls are a neighbourhood basis at `0` in `B^I` (`exists_wI_ball_subset`).
- **Uses from project**: `exists_wI_ball_subset`, `wI`, `BISub`, `hatK`
- **Used by**: the `k`-variable restrictedness proof `evalArMv_isRestricted` / `evalArMvHom`
- **Visibility**: public
- **Lines**: 1166–1186 (proof 13 lines)
- **Notes**: none

### `theorem evalArHom_add`
- **Type**: `(h12) {b} (hbmem) (hb) (f g) : evalArHom p F ϖ h12 hbmem hb (f + g) = evalArHom … f + evalArHom … g`
- **What**: Additivity of the bundled evaluation ring hom, restated at the subtype level.
- **How**: `Subtype.ext` applied to `evalAr_add` — again to avoid class search on nested subring types.
- **Hypotheses**: as `evalArHom`.
- **Uses from project**: `evalArHom`, `evalAr_add`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`
- **Used by**: `evalArHom_sum`, `evalArMv_add`
- **Visibility**: public
- **Lines**: 1188–1197 (proof 1 line)
- **Notes**: elaboration-performance restatement

### `theorem evalArHom_mul`
- **Type**: `(h12) {b} (hbmem) (hb) (f g) : evalArHom … (f * g) = evalArHom … f * evalArHom … g`
- **What**: Multiplicativity of the bundled evaluation ring hom at the subtype level.
- **How**: `Subtype.ext` applied to `evalAr_mul`.
- **Hypotheses**: as `evalArHom`.
- **Uses from project**: `evalArHom`, `evalAr_mul`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`
- **Used by**: `evalArMvFun_mul`
- **Visibility**: public
- **Lines**: 1199–1207 (proof 1 line)
- **Notes**: elaboration-performance restatement

### `theorem evalArHom_one`
- **Type**: `(h12) {b} (hbmem) (hb) : evalArHom p F ϖ h12 hbmem hb 1 = 1`
- **What**: The bundled evaluation map sends `1` to `1`.
- **How**: `Subtype.ext` applied to `evalAr_one`.
- **Hypotheses**: as `evalArHom`.
- **Uses from project**: `evalArHom`, `evalAr_one`
- **Used by**: `evalArMvFun_one`
- **Visibility**: public
- **Lines**: 1209–1215 (proof 1 line)
- **Notes**: none

### `theorem evalArHom_zero`
- **Type**: `(h12) {b} (hbmem) (hb) : evalArHom p F ϖ h12 hbmem hb 0 = 0`
- **What**: The bundled evaluation map sends `0` to `0`.
- **How**: `Subtype.ext` applied to `evalAr_zero`.
- **Hypotheses**: as `evalArHom`.
- **Uses from project**: `evalArHom`, `evalAr_zero`
- **Used by**: `evalArMvFun_zero`, `evalArMvFun_one`
- **Visibility**: public
- **Lines**: 1217–1223 (proof 1 line)
- **Notes**: none

### `def sliceElt`
- **Type**: `{ρ} {hρ0 hρ1} {k : ℕ} (f : ↥(restrictedMvPowerSeriesSubring (k+1) ↥(ArSub p F ϖ hρ0 hρ1))) (I : Fin k →₀ ℕ) : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub p F ϖ hρ0 hρ1))`
- **What**: The `T`-slice of a restricted `(k+1)`-variable series, packaged as an element of the one-variable restricted-series ring.
- **How**: `sliceSeries (f : …) I` together with the restrictedness proof `isRestricted_sliceSeries p F ϖ f.2 I`; bundling keeps the object opaque in later goals (a deliberate elaboration-cost choice, per its docstring).
- **Hypotheses**: `f` restricted; `ρ ∈ (0,1)`.
- **Uses from project**: `sliceSeries`, `isRestricted_sliceSeries`, `restrictedMvPowerSeriesSubring`, `ArSub`
- **Used by**: `coeffSeq_sliceElt`, `sliceElt_add`, `sliceElt_zero`, `sliceElt_one`, `sliceElt_mul`, `evalArMvFun`, `isRestricted_evalArMvFun`
- **Visibility**: public
- **Lines**: 1225–1233 (definition 3 lines)
- **Notes**: none

### `theorem coeffSeq_sliceElt`
- **Type**: `{ρ} {hρ0 hρ1} {k} (f) (I : Fin k →₀ ℕ) (n : ℕ) : coeffSeq (sliceElt p F ϖ f I : …) n = MvPowerSeries.coeff (Finsupp.cons n I) (f : …)`
- **What**: The `n`-th coefficient of the bundled slice is the `(n, I)`-coefficient of `f`.
- **How**: Directly `coeffSeq_sliceSeries` (the bundling is definitionally transparent on the underlying series).
- **Hypotheses**: `f` restricted.
- **Uses from project**: `coeffSeq`, `sliceElt`, `coeffSeq_sliceSeries`, `restrictedMvPowerSeriesSubring`, `ArSub`
- **Used by**: `isRestricted_evalArMvFun`
- **Visibility**: public, `@[simp]`
- **Lines**: 1235–1243 (proof 1 line)
- **Notes**: `@[simp]`

### `theorem sliceElt_add`
- **Type**: `{ρ} {hρ0 hρ1} {k} (f g) (I) : sliceElt p F ϖ (f + g) I = sliceElt p F ϖ f I + sliceElt p F ϖ g I`
- **What**: The slice of a sum is the sum of slices (bundled form).
- **How**: `Subtype.ext` applied to `sliceSeries_add`.
- **Hypotheses**: `f, g` restricted.
- **Uses from project**: `sliceElt`, `sliceSeries_add`
- **Used by**: `evalArMvFun_add`
- **Visibility**: public
- **Lines**: 1245–1250 (proof 1 line)
- **Notes**: none

### `theorem sliceElt_zero`
- **Type**: `{ρ} {hρ0 hρ1} {k} (I : Fin k →₀ ℕ) : sliceElt p F ϖ (0 : …) I = 0`
- **What**: The slices of the bundled zero series are zero.
- **How**: `Subtype.ext` with an explicit `show` reducing to `sliceSeries_zero`, sandwiched between two `ZeroMemClass.coe_zero` rewrites to pass through the subring coercions.
- **Hypotheses**: none beyond the ambient radii.
- **Uses from project**: `sliceElt`, `sliceSeries_zero`, `restrictedMvPowerSeriesSubring`, `ArSub`
- **Used by**: `evalArMvFun_zero`
- **Visibility**: public
- **Lines**: 1252–1263 (proof 6 lines)
- **Notes**: none

### `theorem sliceElt_one`
- **Type**: `{ρ} {hρ0 hρ1} {k} (I : Fin k →₀ ℕ) : sliceElt p F ϖ (1 : …) I = if I = 0 then 1 else 0`
- **What**: The slices of the bundled series `1` are `1` at `I = 0` and `0` elsewhere.
- **How**: `Subtype.ext` reducing to `sliceSeries_one` via `OneMemClass.coe_one`, then a `by_cases hI : I = 0` split pushing the `if` through the coercion with `OneMemClass.coe_one` / `ZeroMemClass.coe_zero`.
- **Hypotheses**: none beyond the ambient radii.
- **Uses from project**: `sliceElt`, `sliceSeries_one`, `restrictedMvPowerSeriesSubring`, `ArSub`
- **Used by**: `evalArMvFun_one`
- **Visibility**: public
- **Lines**: 1265–1279 (proof 8 lines)
- **Notes**: none

### `theorem sliceElt_mul`
- **Type**: `{ρ} {hρ0 hρ1} {k} (f g) (I) : sliceElt p F ϖ (f * g) I = ∑ q ∈ Finset.antidiagonal I, sliceElt p F ϖ f q.1 * sliceElt p F ϖ g q.2`
- **What**: The bundled slice of a product is the finite Cauchy product of the bundled slices.
- **How**: `Subtype.ext`; `AddSubmonoidClass.coe_finsetSum` moves the finite sum through the subring coercion, and the residual claim is exactly `sliceSeries_mul`.
- **Hypotheses**: `f, g` restricted.
- **Uses from project**: `sliceElt`, `sliceSeries_mul`, `restrictedMvPowerSeriesSubring`, `ArSub`
- **Used by**: `evalArMvFun_mul`
- **Visibility**: public
- **Lines**: 1281–1295 (proof 8 lines)
- **Notes**: none

### `def evalArMvFun`
- **Type**: `(h12) {b} (hbmem) (hb) {k : ℕ} (f : ↥(restrictedMvPowerSeriesSubring (k+1) ↥(ArSub …))) : MvPowerSeries (Fin k) ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)`
- **What**: **The `k`-variable presentation map, coefficientwise**: the `I`-coefficient of the image is the one-variable evaluation of the `I`-slice.
- **How**: `fun I => evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ f I)` — slice, then evaluate.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `b ∈ B^I` power-bounded; `f` restricted.
- **Uses from project**: `evalArHom`, `sliceElt`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `wI`, `hatK`
- **Used by**: `evalArMvFun_apply`, `isRestricted_evalArMvFun`, `evalArMvFun_add`, `evalArMvFun_zero`, `evalArMvFun_one`, `evalArMvFun_mul`, `evalArMvHom`
- **Visibility**: public
- **Lines**: 1297–1304 (definition 1 line)
- **Notes**: none

### `theorem evalArMvFun_apply`
- **Type**: `(h12) {b} (hbmem) (hb) {k} (f) (I) : evalArMvFun p F ϖ h12 hbmem hb f I = evalArHom p F ϖ h12 hbmem hb (sliceElt p F ϖ f I)`
- **What**: The defining coefficient formula for the `k`-variable map.
- **How**: `rfl`.
- **Hypotheses**: as `evalArMvFun`.
- **Uses from project**: `evalArMvFun`, `evalArHom`, `sliceElt`
- **Used by**: available as a `simp` lemma; not invoked explicitly elsewhere in the file (the proofs use `show` instead)
- **Visibility**: public, `@[simp]`
- **Lines**: 1306–1314 (proof: `rfl`)
- **Notes**: `@[simp]`

### `theorem evalAr_sum`
- **Type**: `(h12) {b} (hbmem) (hb) {ι : Type*} (s : Finset ι) (f : ι → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub …))) : evalAr … (∑ i ∈ s, f i) = ∑ i ∈ s, evalAr … (f i)`
- **What**: Evaluation commutes with finite sums, stated at the ambient-product level where the ring operations are cheap.
- **How**: `Finset.cons_induction`: the empty case is `evalAr_zero`, the cons case is `Finset.sum_cons` plus `evalAr_add` and the induction hypothesis.
- **Hypotheses**: as `evalAr`; `s` finite.
- **Uses from project**: `evalAr`, `evalAr_zero`, `evalAr_add`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`
- **Used by**: `evalArHom_sum`
- **Visibility**: public
- **Lines**: 1316–1330 (proof 6 lines)
- **Notes**: none

### `theorem evalArHom_sum`
- **Type**: `(h12) {b} (hbmem) (hb) {ι} (s : Finset ι) (f : ι → …) : evalArHom … (∑ i ∈ s, f i) = ∑ i ∈ s, evalArHom … (f i)`
- **What**: The bundled evaluation map commutes with finite sums.
- **How**: `Subtype.ext` down to the ambient product, where `AddSubmonoidClass.coe_finsetSum` moves the sum through the coercion and `evalAr_sum` finishes.
- **Hypotheses**: as `evalArHom`; `s` finite.
- **Uses from project**: `evalArHom`, `evalAr`, `evalAr_sum`, `BISub`, `ArSub`, `hatK`
- **Used by**: `evalArMvFun_mul`
- **Visibility**: public
- **Lines**: 1332–1346 (proof 7 lines)
- **Notes**: none

### `theorem isRestricted_evalArMvFun`
- **Type**: `(h12) {b} (hbmem) (hb) {k : ℕ} (f) : MvPowerSeries.IsRestricted (evalArMvFun p F ϖ h12 hbmem hb f)`
- **What**: **The `k`-variable presentation map lands in the restricted series over `B^I`** — the image really is an element of `B^I⟨T₁,…,T_k⟩`.
- **How**: Use the interval-norm criterion `isRestricted_of_wI`; the "bad" multi-indices `I` (those with `wI(coefficient) > ε`) are shown to lie in the image under `Finsupp.tail` of the finite bad-index set of `f` supplied by `isRestricted_iff_valued`. If no `(l, I)` were bad for `f`, then `wI_evalAr_le` would bound the `I`-coefficient by `ε` (via `coeffSeq_sliceElt` to identify slice coefficients with coefficients of `f` at `Finsupp.cons l I`), contradicting badness; `Finsupp.tail_cons` supplies the preimage witness.
- **Hypotheses**: `f` restricted; `b` power-bounded (needed by `wI_evalAr_le`).
- **Uses from project**: `isRestricted_of_wI`, `isRestricted_iff_valued`, `wI_evalAr_le`, `coeffSeq_sliceElt`, `sliceElt`, `evalArMvFun`, `wI`, `ArSub`, `BISub`, `hatK`
- **Used by**: `evalArMvHom`
- **Visibility**: public
- **Lines**: 1348–1372 (proof 18 lines)
- **Notes**: none

### `theorem evalArMvFun_add`
- **Type**: `(h12) {b} (hbmem) (hb) {k} (f g) : evalArMvFun … (f + g) = evalArMvFun … f + evalArMvFun … g`
- **What**: The `k`-variable map is additive.
- **How**: `funext I` and then coefficientwise: `sliceElt_add` splits the slice, `evalArHom_add` splits the evaluation.
- **Hypotheses**: as `evalArMvFun`.
- **Uses from project**: `evalArMvFun`, `evalArHom`, `sliceElt`, `sliceElt_add`, `evalArHom_add`
- **Used by**: `evalArMvHom`
- **Visibility**: public
- **Lines**: 1375–1388 (proof 6 lines)
- **Notes**: none

### `theorem evalArMvFun_zero`
- **Type**: `(h12) {b} (hbmem) (hb) {k} : evalArMvFun p F ϖ h12 hbmem hb (0 : …) = 0`
- **What**: The `k`-variable map sends `0` to `0`.
- **How**: `funext I` and coefficientwise `sliceElt_zero` followed by `evalArHom_zero`.
- **Hypotheses**: as `evalArMvFun`.
- **Uses from project**: `evalArMvFun`, `evalArHom`, `sliceElt`, `sliceElt_zero`, `evalArHom_zero`
- **Used by**: `evalArMvHom`
- **Visibility**: public
- **Lines**: 1390–1403 (proof 6 lines)
- **Notes**: none

### `theorem evalArMvFun_one`
- **Type**: `(h12) {b} (hbmem) (hb) {k} : evalArMvFun p F ϖ h12 hbmem hb (1 : …) = 1`
- **What**: The `k`-variable map sends `1` to `1`.
- **How**: `funext I`, then `MvPowerSeries.coeff_one` on the target and a `by_cases hI : I = 0`; in each branch `sliceElt_one` computes the slice (`1` or `0`) and `evalArHom_one` / `evalArHom_zero` evaluates it, transported by `congrArg`.
- **Hypotheses**: as `evalArMvFun`.
- **Uses from project**: `evalArMvFun`, `evalArHom`, `sliceElt`, `sliceElt_one`, `evalArHom_one`, `evalArHom_zero`
- **Used by**: `evalArMvHom`
- **Visibility**: public
- **Lines**: 1405–1431 (proof 19 lines)
- **Notes**: none

### `theorem evalArMvFun_mul`
- **Type**: `(h12) {b} (hbmem) (hb) {k} (f g) : evalArMvFun … (f * g) = evalArMvFun … f * evalArMvFun … g`
- **What**: The `k`-variable map is multiplicative — the culmination of the slicing strategy.
- **How**: `funext I`, then `sliceElt_mul` turns the slice of the product into a finite Cauchy sum of slice products, `evalArHom_sum` distributes the evaluation over that sum, `MvPowerSeries.coeff_mul` expands the target coefficient over the same antidiagonal, and `evalArHom_mul` matches the two sums termwise.
- **Hypotheses**: as `evalArMvFun`.
- **Uses from project**: `evalArMvFun`, `evalArHom`, `sliceElt`, `sliceElt_mul`, `evalArHom_sum`, `evalArHom_mul`
- **Used by**: `evalArMvHom`
- **Visibility**: public
- **Lines**: 1433–1448 (proof 7 lines)
- **Notes**: `classical`

### `def evalArMvHom`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) {b} (hbmem) (hb) {k : ℕ} : ↥(restrictedMvPowerSeriesSubring (k+1) ↥(ArSub p F ϖ hρ₂0 hρ₂1)) →+* ↥(restrictedMvPowerSeriesSubring k ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))`
- **What**: **The `k`-variable presentation map** `A^r⟨T, T₁,…,T_k⟩ →+* B^I⟨T₁,…,T_k⟩` — slice in the `T`-direction and evaluate each slice at `b`. Its surjectivity is what will make `B^I` strongly noetherian.
- **How**: Bundles `evalArMvFun` (lands in restricted series by `isRestricted_evalArMvFun`) with the four ring-hom laws `evalArMvFun_add`, `evalArMvFun_zero`, `evalArMvFun_one`, `evalArMvFun_mul`, each via `Subtype.ext`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `b ∈ B^I` with `wI b ≤ 1`.
- **Uses from project**: `evalArMvFun`, `isRestricted_evalArMvFun`, `evalArMvFun_add`, `evalArMvFun_zero`, `evalArMvFun_one`, `evalArMvFun_mul`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`
- **Used by**: unused in file (headline export for the Robba-localization presentation)
- **Visibility**: public
- **Lines**: 1450–1465 (definition 12 lines)
- **Notes**: none

### `theorem evalAr_monomial`
- **Type**: `(h12) {b} (hbmem) (hb) (l : ℕ) (a : ↥(ArSub …)) (hres : IsRestricted (MvPowerSeries.monomial (Finsupp.single 0 l) a)) : evalAr p F ϖ h12 hbmem hb ⟨_, hres⟩ = (ArToBI … a) * b ^ l`
- **What**: **Evaluation of a monomial**: `a·Tˡ ↦ a·bˡ`.
- **How**: All partial sums past `l + 1` are constantly `a·bˡ`: `MvPowerSeries.coeff_monomial` (plus `Finsupp.single_injective` to compare multi-indices) shows the `m`-th coefficient is `a` at `m = l` and `0` otherwise, so `Finset.sum_ite_eq'` collapses the sum; `tendsto_const_nhds.congr'` and `tendsto_nhds_unique` against `tendsto_evalAr` conclude.
- **Hypotheses**: as `evalAr`; the monomial is restricted (`hres`).
- **Uses from project**: `tendsto_evalAr`, `evalTerm`, `coeffSeq`, `ArToBI`, `evalAr`, `ArSub`, `BISub`, `hatK`
- **Used by**: `exists_evalAr_eq_pInv`
- **Visibility**: public
- **Lines**: 1467–1513 (proof 34 lines)
- **Notes**: proof >30 lines; `classical`

### `theorem ArToBI_AlocToHatK`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (u : Aloc p F ϖ) : (ArToBI … ⟨AlocToHatK p F ϖ hρ₂0 hρ₂1 u, _⟩ : …) = BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (AlocToBloc p F ϖ u)`
- **What**: **On the dense layer the inclusion `A^r ↪ B^I` is the diagonal map**: for `u ∈ Aloc`, the graph pair `(resAr, id)` of its `A^r`-image is exactly the `Bloc`-diagonal image of `u`.
- **How**: `Prod.ext`; the first coordinate is `resAr_AlocToHatK` composed with `BlocToHatK_AlocToBloc`, the second is `BlocToHatK_AlocToBloc` alone.
- **Hypotheses**: `ρ₁ ≤ ρ₂`.
- **Uses from project**: `ArToBI`, `AlocToHatK`, `AlocToHatK_mem_ArSub`, `BIProd`, `AlocToBloc`, `resAr`, `resAr_AlocToHatK`, `BlocToHatK`, `BlocToHatK_AlocToBloc`, `BISub`, `hatK`, `Aloc`
- **Used by**: `exists_evalAr_eq_pInv`, and the `Bloc`-in-image / density arguments
- **Visibility**: public
- **Lines**: 1515–1530 (proof 8 lines)
- **Notes**: none

### `def teichPiInvAloc`
- **Type**: `Aloc p F ϖ`
- **What**: The inverse of `[ϖ]` inside `Aloc = A_inf[1/[ϖ]]`.
- **How**: The inverse of the unit provided by `IsLocalization.map_units` for the element `teichPi p F ϖ` of `Submonoid.powers (teichPi p F ϖ)`.
- **Hypotheses**: `Aloc` a localization of `Ainf` at powers of `[ϖ]`.
- **Uses from project**: `Aloc`, `teichPi`
- **Used by**: `teichPiInvAloc_mul`, `AlocToBloc_teichPiInv_mul`, `exists_evalAr_eq_pInv`
- **Visibility**: public
- **Lines**: 1532–1535 (definition 3 lines)
- **Notes**: none

### `theorem teichPiInvAloc_mul`
- **Type**: `algebraMap (Ainf p F) (Aloc p F ϖ) (teichPi p F ϖ) * teichPiInvAloc p F ϖ = 1`
- **What**: `teichPiInvAloc` really is a two-sided inverse of the image of `[ϖ]` in `Aloc`.
- **How**: `Units.mul_inv` for the localization unit, transported along `IsUnit.unit_spec` to replace the abstract unit by the actual algebra-map image.
- **Hypotheses**: `Aloc` a localization at powers of `[ϖ]`.
- **Uses from project**: `teichPiInvAloc`, `teichPi`, `Ainf`, `Aloc`
- **Used by**: `AlocToBloc_teichPiInv_mul`
- **Visibility**: public
- **Lines**: 1537–1542 (proof 4 lines)
- **Notes**: none

### `theorem AlocToBloc_teichPiInv_mul`
- **Type**: `(k : ℕ) : AlocToBloc p F ϖ (teichPiInvAloc p F ϖ ^ k) * algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ ^ k) = 1`
- **What**: In `Bloc`, the image of `[ϖ]^{-k}` cancels `[ϖ]^k` — the `k`-th power version of the inverse relation.
- **How**: The `k = 1` case follows from applying `AlocToBloc` to `teichPiInvAloc_mul` and rewriting with `AlocToBloc_algebraMap`; the general case is `map_pow` twice, `← mul_pow`, then `one_pow`.
- **Hypotheses**: none beyond the standing localization structure.
- **Uses from project**: `AlocToBloc`, `teichPiInvAloc`, `teichPiInvAloc_mul`, `AlocToBloc_algebraMap`, `teichPi`, `Ainf`, `Bloc`
- **Used by**: `exists_evalAr_eq_pInv`
- **Visibility**: public
- **Lines**: 1545–1554 (proof 7 lines)
- **Notes**: none

### `theorem exists_evalAr_eq_pInv`
- **Type**: `(h12 : ρ₁ ≤ ρ₂) (j n : ℕ) (hbmem : BIProd … (teichPowOverP p F ϖ ((PseudoUniformizer.toOF F ϖ)^j) n) ∈ BISub …) (hb : wI … ≤ 1) : ∃ f, evalAr p F ϖ h12 hbmem hb f = BIProd … ↑(isUnit_p_image p F ϖ).unit⁻¹`
- **What**: **The presentation map hits `1/p`.** With Kedlaya's Tate variable at `z̄ = ϖʲ` (the case AD-9 selects), the monomial `[ϖ]^{-jn}·T` evaluates to the image of `p⁻¹`. Together with the constants (the `Aloc`-image, which already inverts `[ϖ]`), this puts the whole dense subring `Bloc` in the image.
- **How**: Take `f` to be the monomial with coefficient the `A^r`-image of `teichPiInvAloc^{jn}` (restricted by `isRestricted_monomial`, in `A^r` by `AlocToHatK_mem_ArSub`); `evalAr_monomial` evaluates it to `ArToBI(coefficient)·b`, `ArToBI_AlocToHatK` turns that into a `Bloc`-image, and then `[ϖ]^{-jn}·([ϖ]^{jn}/p) = 1/p` by `teichPi`-power bookkeeping (`map_pow`, `pow_mul`) plus `AlocToBloc_teichPiInv_mul`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; the Tate variable at `ϖʲ` must be in `B^I` and power-bounded (the left-endpoint condition, supplied as `hbmem`, `hb`).
- **Uses from project**: `evalAr_monomial`, `ArToBI_AlocToHatK`, `AlocToHatK`, `AlocToHatK_mem_ArSub`, `teichPiInvAloc`, `AlocToBloc_teichPiInv_mul`, `isRestricted_monomial`, `teichPowOverP`, `teichPi`, `BIProd`, `isUnit_p_image`, `PseudoUniformizer.toOF`, `evalAr`, `ArSub`, `BISub`
- **Used by**: the `Bloc`-in-image lemma and hence `BISub_le_topologicalClosure_evalRange`
- **Visibility**: public
- **Lines**: 1556–1579 (proof 11 lines)
- **Notes**: none

### `def evalRange`
- **Type**: `(h12) {b} (hbmem) (hb) : Subring ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))`
- **What**: The image of the one-variable presentation map, as a subring of the ambient product `hatK ρ₁ × hatK ρ₂`.
- **How**: `RingHom.range` of `(BISub …).subtype.comp (evalArHom …)` — the evaluation hom followed by the inclusion of `B^I` into the ambient product.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `b ∈ B^I` power-bounded.
- **Uses from project**: `evalArHom`, `BISub`, `wI`, `hatK`
- **Used by**: `mem_evalRange_iff`, the constants/`Bloc`-in-image lemmas, `BISub_le_topologicalClosure_evalRange`
- **Visibility**: public
- **Lines**: 1581–1588 (definition 3 lines)
- **Notes**: none

### `theorem mem_evalRange_iff`
- **Type**: `(h12) {b} (hbmem) (hb) {z} : z ∈ evalRange p F ϖ h12 hbmem hb ↔ ∃ f, evalAr p F ϖ h12 hbmem hb f = z`
- **What**: Membership in the image subring is exactly being an evaluated series.
- **How**: `Iff.rfl` — the two sides are definitionally the same existential.
- **Hypotheses**: as `evalRange`.
- **Uses from project**: `evalRange`, `evalAr`, `hatK`
- **Used by**: the constants/`Bloc`-in-image lemmas
- **Visibility**: public
- **Lines**: 1590–1596 (proof: `Iff.rfl`)
- **Notes**: none

### `theorem BIProd_AlocToBloc_mem_evalRange`
- **Type**: `(h12) {b} (hbmem) (hb) (u : Aloc p F ϖ) : BIProd p F ϖ … (AlocToBloc p F ϖ u) ∈ evalRange p F ϖ h12 hbmem hb`
- **What**: **Constants are in the image**: every `Aloc`-element, viewed diagonally in `B^I`, is an evaluated series.
- **How**: Take the degree-`0` monomial with coefficient the `A^r`-image of `u` (restricted by `isRestricted_monomial`, in `A^r` by `AlocToHatK_mem_ArSub`); `evalAr_monomial` at `l = 0` plus `ArToBI_AlocToHatK` and `pow_zero`/`mul_one` identify its value with the diagonal image.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; `b` power-bounded and in `B^I`.
- **Uses from project**: `mem_evalRange_iff`, `evalAr_monomial`, `ArToBI_AlocToHatK`, `AlocToHatK`, `AlocToHatK_mem_ArSub`, `isRestricted_monomial`, `evalRange`, `BIProd`, `AlocToBloc`, `ArSub`, `Aloc`
- **Used by**: `BIProd_mem_evalRange`
- **Visibility**: public
- **Lines**: 1598–1610 (proof 5 lines)
- **Notes**: none

### `theorem BIProd_mem_evalRange`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (x : Bloc p F ϖ) : BIProd p F ϖ … x ∈ evalRange p F ϖ h12 hbmem hb`
- **What**: **The whole dense subring `Bloc` lies in the image of the presentation map.**
- **How**: Write `x` via `IsLocalization.surj` at `Submonoid.powers (p·[ϖ])` as `a · (p[ϖ])^{-k}`, then split the inverse as `vp · vt` where `vp = p⁻¹` (from `isUnit_p_image`) and `vt = [ϖ]⁻¹` (from `teichPiInvAloc_mul` pushed by `AlocToBloc_algebraMap`); each factor is in the image — the constant `a` and `[ϖ]⁻¹` by `BIProd_AlocToBloc_mem_evalRange`, and `p⁻¹` by `exists_evalAr_eq_pInv` — and `evalRange` is a subring, so `mul_mem`/`pow_mem` finish.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; the Tate variable at `ϖʲ` must be in `B^I` and power-bounded.
- **Uses from project**: `BIProd_AlocToBloc_mem_evalRange`, `exists_evalAr_eq_pInv`, `mem_evalRange_iff`, `teichPiInvAloc`, `teichPiInvAloc_mul`, `AlocToBloc`, `AlocToBloc_algebraMap`, `isUnit_p_image`, `teichPi`, `teichPowOverP`, `BIProd`, `evalRange`, `Ainf`, `Aloc`, `Bloc`, `BISub`
- **Used by**: `BISub_le_topologicalClosure_evalRange`
- **Visibility**: public
- **Lines**: 1612–1662 (proof 42 lines)
- **Notes**: proof >30 lines; the `vp`/`vt` splitting block is duplicated verbatim in `exists_evalAr_lift_bloc` (lines 1959–1991) — a dedup candidate

### `theorem BISub_le_topologicalClosure_evalRange`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) : BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 ≤ (evalRange p F ϖ h12 hbmem hb).topologicalClosure`
- **What**: **The image of the presentation map is dense in `B^I`** — its closure contains the whole interval ring. (Kedlaya's surjectivity is this plus the strictness estimate, which gives closedness of the image.)
- **How**: `BISub` is by definition the closure of the range of `BIProd`; `closure_mono` reduces the claim to the inclusion of that range in `evalRange`, which is exactly `BIProd_mem_evalRange`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; the Tate variable at `ϖʲ` in `B^I` and power-bounded.
- **Uses from project**: `BIProd_mem_evalRange`, `BIProd`, `BISub`, `evalRange`, `teichPowOverP`, `hatK`
- **Used by**: unused in file (headline export)
- **Visibility**: public
- **Lines**: 1665–1681 (proof 6 lines)
- **Notes**: none

### `theorem wAloc_teichPiInvAloc`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : wAloc p F ϖ hρ0 hρ1 (teichPiInvAloc p F ϖ) = (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹`
- **What**: The Gauss value of `[ϖ]⁻¹` is `|ϖ|⁻¹`, at every radius (in particular radius-independent).
- **How**: Apply `wAloc` to the unit relation `teichPiInvAloc_mul`; multiplicativity (`Valuation.map_mul`) plus `wAloc_algebraMap` and `gaussValue_teichmuller` turn it into `|ϖ| · wAloc([ϖ]⁻¹) = 1`, and `field_simp` (after ruling out `|ϖ| = 0`) solves for the inverse.
- **Hypotheses**: `ρ ∈ (0,1)`; `|ϖ| ≠ 0` (derived inside the proof from the unit relation).
- **Uses from project**: `wAloc`, `teichPiInvAloc`, `teichPiInvAloc_mul`, `wAloc_algebraMap`, `gaussValue`, `gaussValue_teichmuller`, `teichPi`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `valued_teichPiInv_pow`, `exists_aloc_head_split`, `gaussNormRPS_teichMonomial`
- **Visibility**: public
- **Lines**: 1683–1697 (proof 11 lines)
- **Notes**: none

### `theorem valued_teichPiInv_pow`
- **Type**: `{ρ} {hρ0 hρ1} (k : ℕ) : Valued.v (AlocToHatK p F ϖ hρ0 hρ1 (teichPiInvAloc p F ϖ ^ k)) = ((perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F))⁻¹) ^ k`
- **What**: The value of `[ϖ]^{-k}` in `A^r` is `|ϖ|^{-k}`.
- **How**: `valued_AlocToHatK` reduces to `wAloc`, `map_pow` pulls out the power, and `wAloc_teichPiInvAloc` computes the base.
- **Hypotheses**: `ρ ∈ (0,1)`.
- **Uses from project**: `valued_AlocToHatK`, `wAloc_teichPiInvAloc`, `teichPiInvAloc`, `AlocToHatK`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `exists_evalAr_eq_pInv_pow`
- **Visibility**: public
- **Lines**: 1699–1703 (proof 1 line)
- **Notes**: none

### `theorem exists_evalAr_eq_pInv_pow`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (i : ℕ) : ∃ f, evalAr … f = BIProd … (↑(isUnit_p_image p F ϖ).unit⁻¹ ^ i) ∧ gaussNormRPS p F ϖ hρ₂0 hρ₂1 (f : …) = ((perfectoidValuation p F (ϖ : F))⁻¹) ^ (j * n * i)`
- **What**: **The norm-exact lift of `p^{-i}`** (the heart of Kedlaya's strictness estimate in the AD-9 case): the monomial `[ϖ]^{-jni}·Tⁱ` evaluates to the image of `p^{-i}` and has Gauss norm `|ϖ|^{-jni}`, which equals `ρ₁^{-i}` exactly when the left endpoint is on the nose.
- **How**: Two goals for the explicit monomial. The evaluation is `evalAr_monomial` at `l = i` + `ArToBI_AlocToHatK`, then `[ϖ]^{-jni}·([ϖ]^{jn}/p)^i = p^{-i}` by `mul_pow`, `pow_mul` and `AlocToBloc_teichPiInv_mul`. The norm is `gaussNormRPS_monomial` followed by `valued_teichPiInv_pow`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; the Tate variable at `ϖʲ` in `B^I` and power-bounded.
- **Uses from project**: `evalAr_monomial`, `ArToBI_AlocToHatK`, `AlocToHatK`, `AlocToHatK_mem_ArSub`, `teichPiInvAloc`, `AlocToBloc_teichPiInv_mul`, `isRestricted_monomial`, `gaussNormRPS`, `gaussNormRPS_monomial`, `valued_teichPiInv_pow`, `teichPowOverP`, `teichPi`, `BIProd`, `isUnit_p_image`, `evalAr`, `ArSub`, `BISub`
- **Used by**: unused in file (the `exists_evalAr_lift_*` chain supersedes it with the `Aloc`-coefficient version)
- **Visibility**: public
- **Lines**: 1706–1735 (proof 14 lines)
- **Notes**: none

### `theorem teichPiInvAloc_pow_mul`
- **Type**: `(m : ℕ) : algebraMap (Ainf p F) (Aloc p F ϖ) (teichPi p F ϖ ^ m) * teichPiInvAloc p F ϖ ^ m = 1`
- **What**: In `Aloc`, `[ϖ]^m · [ϖ]^{-m} = 1`.
- **How**: `map_pow`, `← mul_pow`, then `teichPiInvAloc_mul` and `one_pow`.
- **Hypotheses**: none beyond the standing localization structure.
- **Uses from project**: `teichPiInvAloc`, `teichPiInvAloc_mul`, `teichPi`, `Ainf`, `Aloc`
- **Used by**: `exists_aloc_head_split`
- **Visibility**: public
- **Lines**: 1737–1741 (proof 1 line)
- **Notes**: none

### `theorem exists_aloc_head_split`
- **Type**: `(u : Aloc p F ϖ) : ∃ t w : Aloc p F ϖ, u = t + (p : Aloc p F ϖ) * w ∧ ∀ ρ σ (hρ0 hρ1 hσ0 hσ1), wAloc p F ϖ hρ0 hρ1 t ≤ wAloc p F ϖ hσ0 hσ1 u`
- **What**: **The `Aloc` head split**: every `u ∈ Aloc` decomposes as a Teichmüller "head" `t` plus `p` times another `Aloc`-element, where the head's Gauss value is *radius-independent* and bounded by `u`'s value at *every* radius. This is the inductive step of the strictness estimate.
- **How**: Write `u = D · [ϖ]^{-m}` via `IsLocalization.surj` and `teichPiInvAloc_pow_mul`; apply the `Ainf`-level head split `exists_head_split` to `D` (giving `D = [D₀] + p·D'`) and multiply both pieces by `[ϖ]^{-m}`. The value estimate computes both sides with `wAloc_algebraMap`, `gaussValue_teichmuller` and `wAloc_teichPiInvAloc` — the `[ϖ]^{-m}` factor is radius-independent and cancels — reducing to `gaussTerm_le_gaussValue` at `n = 0`, i.e. the `0`-th Gauss term is at most the Gauss value.
- **Hypotheses**: none beyond the standing setup; the key input is the `Ainf`-level `exists_head_split`.
- **Uses from project**: `exists_head_split`, `teichPiInvAloc`, `teichPiInvAloc_pow_mul`, `teichCoeff`, `wAloc`, `wAloc_algebraMap`, `wAloc_teichPiInvAloc`, `gaussValue`, `gaussValue_teichmuller`, `gaussTerm`, `gaussTerm_le_gaussValue`, `teichPi`, `perfectoidValuation`, `Ainf`, `Aloc`, `OF`, `PseudoUniformizer.toOF`
- **Used by**: `exists_evalAr_lift_aloc`
- **Visibility**: public
- **Lines**: 1743–1787 (proof 38 lines)
- **Notes**: proof >30 lines

### `theorem wLoc_AlocToBloc`
- **Type**: `{ρ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) : wLoc p F ϖ hρ0 hρ1 (AlocToBloc p F ϖ u) = wAloc p F ϖ hρ0 hρ1 u`
- **What**: The `Bloc`-side Gauss value restricts to the `Aloc`-side Gauss value on `Aloc`-images.
- **How**: Both are valuations of endpoint images; `valued_BlocToHatK` and `valued_AlocToHatK` convert, and `BlocToHatK_AlocToBloc` identifies the two images.
- **Hypotheses**: `ρ ∈ (0,1)`.
- **Uses from project**: `wLoc`, `wAloc`, `AlocToBloc`, `valued_BlocToHatK`, `BlocToHatK_AlocToBloc`, `valued_AlocToHatK`, `Aloc`
- **Used by**: `wI_BIProd_aloc_pInv_pow`
- **Visibility**: public
- **Lines**: 1790–1793 (proof 1 line)
- **Notes**: none

### `theorem wI_BIProd_aloc_pInv_pow`
- **Type**: `(k : ℕ) (u : Aloc p F ϖ) : wI p F … (BIProd … (AlocToBloc p F ϖ u * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ k)) = max (wAloc p F ϖ hρ₁0 hρ₁1 u * (ρ₁⁻¹) ^ k) (wAloc p F ϖ hρ₂0 hρ₂1 u * (ρ₂⁻¹) ^ k)`
- **What**: The interval norm of `u·p^{-k}` for `u ∈ Aloc`: the max of the two endpoint values rescaled by `ρ^{-k}`.
- **How**: `wI_BIProd` reduces to a max of endpoint valuations, `valued_BlocToHatK` converts each to `wLoc`, then multiplicativity (`Valuation.map_mul`/`map_pow`) splits off the `p^{-k}` factor, evaluated by `wLoc_p_inv`, and `wLoc_AlocToBloc` computes the `Aloc` factor.
- **Hypotheses**: both radii in `(0,1)`; `p` invertible in `Bloc`.
- **Uses from project**: `wI_BIProd`, `valued_BlocToHatK`, `wLoc_p_inv`, `wLoc_AlocToBloc`, `wAloc`, `BIProd`, `AlocToBloc`, `isUnit_p_image`, `wI`, `Aloc`
- **Used by**: `exists_evalAr_lift_aloc`, `exists_evalAr_lift_bloc`
- **Visibility**: public
- **Lines**: 1795–1804 (proof 4 lines)
- **Notes**: none

### `theorem evalAr_teichMonomial`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (t : Aloc p F ϖ) (i : ℕ) : evalAr … ⟨monomial (single 0 i) ⟨AlocToHatK … (t * teichPiInvAloc^{jni}), _⟩, _⟩ = BIProd … (AlocToBloc p F ϖ t * ↑(isUnit_p_image p F ϖ).unit⁻¹ ^ i)`
- **What**: **Evaluation of the exact monomial lift**: `t·[ϖ]^{-jni}·Tⁱ` evaluates to `t·p^{-i}` — the AD-9 cancellation `[ϖ]^{jn}/p = ` Tate variable.
- **How**: `evalAr_monomial` gives `ArToBI(coefficient)·bⁱ`; `ArToBI_AlocToHatK` turns the coefficient into a `Bloc`-image, the Tate variable is expanded by `teichPowOverP` with `[ϖ]^{jn}` identified via `map_pow`/`pow_mul`, and a `calc` reassociation plus `AlocToBloc_teichPiInv_mul` cancels `[ϖ]^{-jni}·[ϖ]^{jni}` leaving `t·p^{-i}`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; the Tate variable at `ϖʲ` in `B^I` and power-bounded.
- **Uses from project**: `evalAr_monomial`, `ArToBI_AlocToHatK`, `AlocToHatK`, `AlocToHatK_mem_ArSub`, `teichPiInvAloc`, `AlocToBloc`, `AlocToBloc_teichPiInv_mul`, `isRestricted_monomial`, `teichPowOverP`, `teichPi`, `BIProd`, `isUnit_p_image`, `evalAr`, `Ainf`, `Aloc`, `Bloc`, `ArSub`, `BISub`
- **Used by**: `exists_evalAr_lift_aloc`
- **Visibility**: public
- **Lines**: 1806–1838 (proof 17 lines)
- **Notes**: none

### `theorem gaussNormRPS_teichMonomial`
- **Type**: `(t : Aloc p F ϖ) (i l : ℕ) : gaussNormRPS p F ϖ hρ₂0 hρ₂1 (monomial (single 0 i) ⟨AlocToHatK … (t * teichPiInvAloc^l), _⟩) = wAloc p F ϖ hρ₂0 hρ₂1 t * ((perfectoidValuation p F (ϖ : F))⁻¹) ^ l`
- **What**: **The Gauss norm of the exact monomial lift** is the value of its coefficient: `|t|_{ρ₂}·|ϖ|^{-l}` (independent of the degree `i`, since the Tate algebra has radius one).
- **How**: `gaussNormRPS_monomial` reduces to the coefficient's valuation, `valued_AlocToHatK` converts it to `wAloc`, multiplicativity splits `t` from the `[ϖ]^{-l}` factor, and `wAloc_teichPiInvAloc` evaluates the latter.
- **Hypotheses**: `ρ₂ ∈ (0,1)`.
- **Uses from project**: `gaussNormRPS`, `gaussNormRPS_monomial`, `valued_AlocToHatK`, `wAloc`, `wAloc_teichPiInvAloc`, `teichPiInvAloc`, `AlocToHatK`, `AlocToHatK_mem_ArSub`, `perfectoidValuation`, `ArSub`, `Aloc`, `OF`, `PseudoUniformizer.toOF`
- **Used by**: `exists_evalAr_lift_aloc`
- **Visibility**: public
- **Lines**: 1840–1850 (proof 2 lines)
- **Notes**: none

### `theorem exists_evalAr_lift_aloc`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (hexact : perfectoidValuation p F (ϖ : F) ^ (j * n) = ρ₁) (k : ℕ) (u : Aloc p F ϖ) : ∃ f, evalAr … f = BIProd … (AlocToBloc p F ϖ u * p⁻¹ ^ k) ∧ gaussNormRPS … f ≤ wI … (BIProd … (AlocToBloc p F ϖ u * p⁻¹ ^ k))`
- **What**: **The norm-controlled lift on the dense layer** — Kedlaya's strictness estimate in the AD-9 exact form: every `u·p^{-k}` with `u ∈ Aloc` has an `evalAr`-preimage whose Gauss norm is at most its interval norm (constant `1`).
- **How**: Induction on `k` generalizing `u`. The base case is the degree-`0` monomial via `evalAr_teichMonomial` and `gaussNormRPS_teichMonomial`, compared with `wI_BIProd_aloc_pInv_pow` and `le_max_right`. The step splits `u = t + p·w` by `exists_aloc_head_split`, lifts `w` at level `k` by induction and `t` by the degree-`(k+1)` monomial; the evaluation identity is `evalAr_add` + `evalAr_teichMonomial` closed by a `linear_combination` against `p·p⁻¹ = 1`, and the norm bound is `gaussNormRPS_add_le` with two branches: the head branch uses `hexact` to turn `|ϖ|^{-jn(k+1)}` into `ρ₁^{-(k+1)}` together with the radius-independence from `exists_aloc_head_split`, and the tail branch uses the induction bound plus the elementary inequality `|w|·ρ^{-k} ≤ |u|·ρ^{-(k+1)}` derived from `wAloc_p_pow_mul` and the ultrametric `Valuation.map_sub`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; Tate variable in `B^I` and power-bounded; **`hexact`**: `|ϖ|^{jn} = ρ₁` exactly (the left endpoint is on the nose).
- **Uses from project**: `exists_aloc_head_split`, `evalAr_teichMonomial`, `gaussNormRPS_teichMonomial`, `wI_BIProd_aloc_pInv_pow`, `evalAr_add`, `gaussNormRPS_add_le`, `wAloc_p_pow_mul`, `isRestricted_monomial`, `AlocToHatK`, `AlocToHatK_mem_ArSub`, `teichPiInvAloc`, `AlocToBloc`, `isUnit_p_image`, `teichPowOverP`, `gaussNormRPS`, `wAloc`, `wI`, `BIProd`, `evalAr`, `perfectoidValuation`, `ArSub`, `BISub`, `Aloc`, `Bloc`
- **Used by**: `exists_evalAr_lift_bloc`
- **Visibility**: public
- **Lines**: 1852–1940 (proof 69 lines)
- **Notes**: proof >30 lines; the only place `hexact` (exact left endpoint) is genuinely used

### `theorem exists_evalAr_lift_bloc`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (hexact : perfectoidValuation p F (ϖ : F) ^ (j * n) = ρ₁) (x : Bloc p F ϖ) : ∃ f, evalAr … f = BIProd … x ∧ gaussNormRPS … f ≤ wI … (BIProd … x)`
- **What**: **The norm-controlled lift of every `Bloc` element** — Kedlaya's estimate (4.9.1) with constant `1` in the AD-9 exact case.
- **How**: Rewrite an arbitrary `x ∈ Bloc` as `u · p^{-k}` with `u ∈ Aloc`: `IsLocalization.surj` at `Submonoid.powers (p·[ϖ])` gives `x = a·(p[ϖ])^{-k}`, and the inverse splits as `vp·vt` (`isUnit_p_image` for `p⁻¹`, `teichPiInvAloc_mul` + `AlocToBloc_algebraMap` for `[ϖ]⁻¹`), so the `[ϖ]^{-k}` part can be absorbed into the `Aloc`-factor. Then apply `exists_evalAr_lift_aloc` at that `u` and `k`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; Tate variable in `B^I` and power-bounded; `hexact` (exact left endpoint).
- **Uses from project**: `exists_evalAr_lift_aloc`, `teichPiInvAloc`, `teichPiInvAloc_mul`, `AlocToBloc`, `AlocToBloc_algebraMap`, `isUnit_p_image`, `teichPi`, `teichPowOverP`, `BIProd`, `gaussNormRPS`, `evalAr`, `wI`, `Ainf`, `Aloc`, `Bloc`, `ArSub`, `BISub`
- **Used by**: `exists_correction_sequence`
- **Visibility**: public
- **Lines**: 1942–2001 (proof 43 lines)
- **Notes**: proof >30 lines; the `vp`/`vt` splitting block (lines 1959–1991) duplicates lines 1622–1654 of `BIProd_mem_evalRange` almost verbatim — a dedup candidate

### `theorem exists_BIProd_approx`
- **Type**: `{z} (hz : z ∈ BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) {ε : NNReal} (hε : 0 < ε) : ∃ x : Bloc p F ϖ, wI p F … (z - BIProd p F ϖ … x) ≤ ε`
- **What**: **Density extraction**: every element of `B^I` is within `ε` (in interval norm) of a `Bloc`-image.
- **How**: `B^I` is by definition the closure of the range of `BIProd`; `mem_closure_iff_nhds` applied to the `wI`-ball neighbourhood `wI_ball_mem_nhds` produces a range element inside the ball, and `wI_neg` flips the sign of the difference.
- **Hypotheses**: `ε > 0`; `z ∈ B^I`.
- **Uses from project**: `wI_ball_mem_nhds`, `wI_neg`, `BIProd`, `BISub`, `wI`, `hatK`, `Bloc`
- **Used by**: `exists_correction_sequence`
- **Visibility**: public
- **Lines**: 2003–2016 (proof 9 lines)
- **Notes**: none

### `theorem exists_chain`
- **Type**: `{α β : Type*} (S : α → Prop) (ν : α → NNReal) (μ : β → NNReal) (sub : α → β → α) (c : ℕ → NNReal) (z : α) (hz : S z) (hzc : ν z ≤ c 0) (hstep : ∀ m r, S r → ν r ≤ c m → ∃ f, μ f ≤ c m ∧ S (sub r f) ∧ ν (sub r f) ≤ c (m+1)) : ∃ u r, r 0 = z ∧ (∀ m, r (m+1) = sub (r m) (u m)) ∧ (∀ m, μ (u m) ≤ c m) ∧ (∀ m, S (r m)) ∧ (∀ m, ν (r m) ≤ c m)`
- **What**: **Abstract successive-approximation chain**: from a one-step improvement engine, extract a full correction sequence together with its residual sequence. Stated over *opaque* types `α, β` so the recursion never unfolds against the heavy concrete types (design note PERF-1).
- **How**: `choose` extracts a Skolem function `F` from `hstep`, and a `Nat.rec` builds a dependent sequence of subtypes `{r // S r ∧ ν r ≤ c m}`, carrying the invariant along; the six conclusions are read off from the components, with the recursion equation being `rfl`.
- **Hypotheses**: an initial point satisfying the invariant, and a step producing a bounded correction that improves the residual by one index of `c`.
- **Uses from project**: []
- **Used by**: `exists_correction_sequence`
- **Visibility**: public
- **Lines**: 2018–2036 (proof 9 lines)
- **Notes**: fully generic (no `p`, `F`, `ϖ`); deliberately abstracted for elaboration performance (PERF-1)

### `theorem wI_z_sub_evalAr_add_le`
- **Type**: `(h12) {b} (hbmem) (hb) (z) (SS V : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub …))) {ε} (hε : 0 < ε) (h1 : wI (z - evalAr SS) ≤ ε) (h2 : gaussNormRPS V ≤ ε) : wI (z - evalAr (SS + V)) ≤ ε`
- **What**: One step of the residual estimate: if the residual after the partial sum `SS` is `≤ ε` and the new correction `V` has Gauss norm `≤ ε`, the residual after `SS + V` is still `≤ ε`.
- **How**: `wI_evalAr_le` bounds `wI (evalAr V)` by `ε`, using `valued_coeff_le_gaussNormRPS` to pass from the Gauss norm of `V` to its individual coefficient values; then `evalAr_add` splits the evaluation and the ultrametric `wI_add_le` (with `wI_neg`) bounds the sum of the two `ε`-small pieces.
- **Hypotheses**: `ε > 0`; both `ε`-bounds; `b` power-bounded.
- **Uses from project**: `wI_evalAr_le`, `valued_coeff_le_gaussNormRPS`, `evalAr_add`, `wI_add_le`, `wI_neg`, `gaussNormRPS`, `evalAr`, `wI`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `hatK`
- **Used by**: `exists_evalAr_eq_of_correction`
- **Visibility**: public
- **Lines**: 2038–2069 (proof 19 lines)
- **Notes**: none

### `theorem exists_evalAr_eq_of_correction`
- **Type**: `(h12) {b} (hbmem) (hb) (z) {W} (hW : 0 < W) (u : ℕ → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub …))) (hCbnd : ∀ l, gaussNormRPS (u l) ≤ W·2⁻ˡ) (hres : ∀ m, wI (z - evalAr (∑_{l<m} u l)) ≤ W·2⁻ᵐ) : ∃ U, evalAr … U = z ∧ gaussNormRPS … U ≤ W`
- **What**: From a geometrically-decaying correction sequence, the limit series is an *exact* `evalAr`-preimage of `z` with Gauss norm at most `W`.
- **How**: `exists_rps_series_limit` (with nullity of `W·2⁻ˡ` from `tendsto_pow_atTop_nhds_zero_of_lt_one`) produces the limit series `U` with tail control; the `m = 0` instance of that control gives `gaussNormRPS U ≤ W`, while for each `m` the tail `U - ∑_{l<m} u l` has Gauss norm `≤ W·2⁻ᵐ`, so `wI_z_sub_evalAr_add_le` yields `wI (z - evalAr U) ≤ W·2⁻ᵐ` for all `m`; `ge_of_tendsto` forces it to be `0`, and `wI_eq_zero_iff` + `sub_eq_zero` give `evalAr U = z`.
- **Hypotheses**: `W > 0`; geometric Gauss-norm bounds on the corrections; geometric residual bounds.
- **Uses from project**: `exists_rps_series_limit`, `wI_z_sub_evalAr_add_le`, `wI_eq_zero_iff`, `gaussNormRPS`, `evalAr`, `wI`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `hatK`
- **Used by**: `exists_evalAr_eq_of_mem_BISub`
- **Visibility**: public
- **Lines**: 2071–2126 (proof 38 lines)
- **Notes**: proof >30 lines

### `theorem exists_correction_sequence`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (hexact) {z} (hz : z ∈ BISub …) {W} (hW : 0 < W) (hzW : wI … z ≤ W) : ∃ u : ℕ → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub …)), (∀ l, gaussNormRPS (u l) ≤ W·2⁻ˡ) ∧ ∀ m, wI (z - evalAr (∑_{l<m} u l)) ≤ W·2⁻ᵐ`
- **What**: **The correction sequence**: successive approximation of an element of `B^I` by values of the presentation map, each round halving the residual with Gauss-norm control — the engine behind closedness of the image.
- **How**: The one-step engine takes a residual `r ∈ B^I` with `wI r ≤ W·2⁻ᵐ`, uses `exists_BIProd_approx` to find `x ∈ Bloc` within `W·2^{-(m+1)}`, and lifts `x` by `exists_evalAr_lift_bloc` to a series of Gauss norm `≤ wI (BIProd x) ≤ W·2⁻ᵐ` (the last step by the ultrametric `wI_add_le`/`wI_neg`); the new residual `r - evalAr f = r - BIProd x` is in `B^I` (`sub_mem`, `BIProd_mem_BISub`) and `≤ W·2^{-(m+1)}`. Feeding this into the abstract `exists_chain` produces the sequence, and an induction using `evalAr_zero`/`evalAr_add` identifies the chain's residuals `r m` with `z - evalAr (∑_{l<m} u l)`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; Tate variable in `B^I` and power-bounded; `hexact`; `z ∈ B^I` with `wI z ≤ W`, `W > 0`.
- **Uses from project**: `exists_BIProd_approx`, `exists_evalAr_lift_bloc`, `exists_chain`, `wI_add_le`, `wI_neg`, `BIProd_mem_BISub`, `evalAr_zero`, `evalAr_add`, `gaussNormRPS`, `evalAr`, `wI`, `BIProd`, `teichPowOverP`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `hatK`
- **Used by**: `exists_evalAr_eq_of_mem_BISub`
- **Visibility**: public
- **Lines**: 2128–2210 (proof 61 lines)
- **Notes**: proof >30 lines

### `theorem exists_evalAr_eq_of_mem_BISub`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (hexact) {z} (hz : z ∈ BISub …) : ∃ f : ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub …)), evalAr … f = z ∧ gaussNormRPS … f ≤ wI … z`
- **What**: **Strict surjectivity onto `B^I`** (Kedlaya, Lemma "Robba localizations", case 3): every element of the interval ring is the value of a restricted series over `A^r` whose Gauss norm is at most its interval norm.
- **How**: Split on `wI z = 0`: then `wI_eq_zero_iff` gives `z = 0` and `f = 0` works (its Gauss norm is `0` by a direct `ciSup_le` computation on `gaussNormRPS`). Otherwise `W := wI z > 0`, and `exists_correction_sequence` at `W` (with `le_rfl`) feeds `exists_evalAr_eq_of_correction`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; Tate variable in `B^I` and power-bounded; `hexact` (exact left endpoint); `z ∈ B^I`.
- **Uses from project**: `exists_correction_sequence`, `exists_evalAr_eq_of_correction`, `evalAr_zero`, `wI_eq_zero_iff`, `gaussNormRPS`, `evalAr`, `wI`, `BIProd`, `teichPowOverP`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`
- **Used by**: `surjective_evalArHom`, `surjective_evalArMvHom`
- **Visibility**: public
- **Lines**: 2212–2246 (proof 17 lines)
- **Notes**: none

### `theorem surjective_evalArHom`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (hexact) : Function.Surjective (evalArHom p F ϖ h12 hbmem hb)`
- **What**: **The univariate presentation map `A^r⟨T⟩ → B^I` is surjective** (project ticket T911, one-variable case).
- **How**: Destructure a target `⟨z, hz⟩` of `B^I`, apply `exists_evalAr_eq_of_mem_BISub` to get a preimage series (discarding the norm bound), and repackage with `Subtype.ext`.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; Tate variable in `B^I` and power-bounded; `hexact` (exact left endpoint).
- **Uses from project**: `exists_evalAr_eq_of_mem_BISub`, `evalArHom`, `BIProd`, `teichPowOverP`, `wI`, `BISub`, `hatK`
- **Used by**: unused in file (headline export)
- **Visibility**: public
- **Lines**: 2248–2261 (proof 4 lines)
- **Notes**: none

### `theorem wI_finite_of_isRestricted`
- **Type**: `{k : ℕ} {c : MvPowerSeries (Fin k) ↥(BISub …)} (hc : MvPowerSeries.IsRestricted c) {ε : NNReal} (hε : 0 < ε) : {I : Fin k →₀ ℕ | ε < wI … (coeff I c)}.Finite`
- **What**: Restrictedness over `B^I` forces the coefficients' interval norms to be cofinitely small — the converse of `isRestricted_of_wI`.
- **How**: The `wI`-ball is a neighbourhood of `0` in the ambient product (`wI_ball_mem_nhds`), so its preimage under `Subtype.val` is a neighbourhood of `0` in `B^I` (`continuous_subtype_val.continuousAt.preimage_mem_nhds`); `IsRestricted.eventually` then makes the bound hold cofinitely, and `Filter.eventually_cofinite` converts this to finiteness of the complement.
- **Hypotheses**: `c` restricted; `ε > 0`.
- **Uses from project**: `wI_ball_mem_nhds`, `wI`, `BISub`, `hatK`
- **Used by**: `isRestricted_liftAssembly`
- **Visibility**: public
- **Lines**: 2263–2287 (proof 17 lines)
- **Notes**: none

### `theorem isRestricted_liftAssembly`
- **Type**: `{k : ℕ} (fI : (Fin k →₀ ℕ) → ↥(restrictedMvPowerSeriesSubring 1 ↥(ArSub …))) (g : ↥(restrictedMvPowerSeriesSubring k ↥(BISub …))) (hfInorm : ∀ I, gaussNormRPS (fI I) ≤ wI (coeff I g)) : MvPowerSeries.IsRestricted (fun s => coeffSeq (fI (Finsupp.tail s)) (s 0))`
- **What**: **The coefficientwise-lifted series is restricted** — the assembly step of the `k`-variable surjectivity: gluing per-multi-index one-variable lifts `fI` into a single `(k+1)`-variable series preserves restrictedness, provided each lift is Gauss-norm-controlled by the corresponding coefficient of `g`.
- **How**: Via `isRestricted_iff_valued`. For `ε > 0`, the bad multi-indices of the glued series inject into a *biUnion*: finitely many bad tails `I` (from `wI_finite_of_isRestricted` applied to `g`) times, for each, finitely many bad heads `l` (from `isRestricted_iff_valued` applied to `fI I`, pulled back along the injection `Finsupp.single 0`). Badness of `s` forces badness of `Finsupp.tail s` because `valued_coeff_le_gaussNormRPS` plus `hfInorm` bound the `s`-coefficient by `wI (coeff (tail s) g)`; `Finsupp.cons_tail` supplies the reconstruction `s = cons (s 0) (tail s)`.
- **Hypotheses**: `g` restricted; each `fI I` restricted; the Gauss-norm control `hfInorm` (this is exactly what the *strict* surjectivity supplies).
- **Uses from project**: `wI_finite_of_isRestricted`, `isRestricted_iff_valued`, `valued_coeff_le_gaussNormRPS`, `coeffSeq`, `gaussNormRPS`, `wI`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `hatK`
- **Used by**: `surjective_evalArMvHom`
- **Visibility**: public
- **Lines**: 2289–2356 (proof 46 lines)
- **Notes**: proof >30 lines; hoisted to its own lemma per the PERF-1 design note

### `theorem surjective_evalArMvHom`
- **Type**: `(h12) (j n : ℕ) (hbmem) (hb) (hexact) {k : ℕ} : Function.Surjective (evalArMvHom p F ϖ h12 hbmem hb (k := k))`
- **What**: **The `k`-variable presentation map `A^r⟨T, T₁,…,T_k⟩ → B^I⟨T₁,…,T_k⟩` is surjective** — the restricted-series functor applied to the strict surjection (project ticket T911b). This is the statement that makes `B^I` a quotient of a radius-one Tate algebra over `A^r`, hence strongly noetherian.
- **How**: `choose` a per-multi-index lift `fI I` of each coefficient of `g` via `exists_evalAr_eq_of_mem_BISub` (which supplies both the evaluation identity and the Gauss-norm control), assemble them into one `(k+1)`-variable series, restricted by `isRestricted_liftAssembly`. Then check the assembled series maps to `g`: `coeffSeq_ext` plus `coeffSeq_sliceElt`, `Finsupp.tail_cons` and `Finsupp.cons_zero` show its `I`-slice is exactly `fI I`, so `evalArMvFun_apply` and the chosen evaluation identity finish coefficientwise.
- **Hypotheses**: `ρ₁ ≤ ρ₂`; Tate variable in `B^I` and power-bounded; `hexact` (exact left endpoint).
- **Uses from project**: `exists_evalAr_eq_of_mem_BISub`, `isRestricted_liftAssembly`, `sliceElt`, `coeffSeq_sliceElt`, `coeffSeq_ext`, `coeffSeq`, `evalArMvFun`, `evalArMvFun_apply`, `evalArMvHom`, `BIProd`, `teichPowOverP`, `restrictedMvPowerSeriesSubring`, `ArSub`, `BISub`, `wI`
- **Used by**: unused in file (the headline export of the file)
- **Visibility**: public
- **Lines**: 2358–2394 (proof 25 lines)
- **Notes**: none

---

### File Summary
- **Total declarations: 117** (15 defs, 102 lemmas/theorems, 0 instances). No structures, classes, or abbrevs.
- **Key API (used by 3+ other declarations in this file)**, with in-file consumer counts:
  `evalAr` (23), `coeffSeq` (21), `teichPowOverP` (15), `teichPiInvAloc` (13), `sliceElt` (13),
  `evalArHom` (13), `ArToBI` (12), `AlocToBloc` (12), `sliceSeries` (10), `resAr` (10),
  `evalArMvFun` (8), `AlocToHatK_mem_ArSub` (8), `evalTerm` (7), `tendsto_evalAr` (6),
  `evalAr_add` (6), `tendsto_resAr` (5), `teichPiInvAloc_mul` (5), `evalAr_zero` (5),
  `coeffSeq_sliceSeries` (5), `coeffSeq_ext` (5), `tendsto_valued_coeffSeq` (4), `evalRange` (4),
  `evalAr_monomial` (4), `ArToBI_AlocToHatK` (4), `AlocToBloc_algebraMap` (4), `wI_ArToBI` (3),
  `wAloc_teichPiInvAloc` (3), `valued_AlocToHatK_mono` (3), `exists_eval_series` (3),
  `coeffSeq_zero` (3), `BlocToHatK_AlocToBloc` (3), `AlocToBloc_teichPiInv_mul` (3).
- **Unused declarations (no in-file consumer)** — all are intended exports / headline results:
  `ArToBI_snd` (a `@[simp]` lemma, used by simp not by name), `ArToBI_injective`,
  `wI_teichPowOverP_le_one`, `teichPowOverPElt`, `exists_evalAr_eq_pInv_pow`,
  `BISub_le_topologicalClosure_evalRange`, `surjective_evalArHom`, `surjective_evalArMvHom`.
  (`evalArMvHom` and `evalArMvFun_apply` are likewise terminal/`simp`-only.)
  Genuinely superseded: `exists_evalAr_eq_pInv_pow` — the later `exists_evalAr_lift_*` chain
  proves a strictly stronger statement; and `BISub_le_topologicalClosure_evalRange` (density)
  is subsumed by `surjective_evalArHom` (exact surjectivity).
- **Declarations with `sorry`: none.** The file is sorry-free.
- **Declarations with `set_option`: none.** (Consistent with the project's no-heartbeat-bump rule;
  the elaboration cost is instead managed by the `ArToBI_add/mul/sum`, `evalArHom_*`, `sliceElt`
  restatements and the type-opaque `exists_chain` — see the PERF-1 notes in the docstrings.)
- **Proofs >30 lines** (declaration span, docstring excluded):
  `exists_evalAr_lift_aloc` (89), `exists_correction_sequence` (84), `wI_partial_cauchy_diff` (79),
  `isRestricted_liftAssembly` (70), `tendsto_cauchy_product` (69),
  `exists_evalAr_lift_bloc` (58), `exists_evalAr_eq_of_correction` (58),
  `BIProd_mem_evalRange` (55), `evalAr_monomial` (49), `exists_aloc_head_split` (42),
  `surjective_evalArMvHom` (38), `tendsto_resAr` (36), `evalAr_mul` (33),
  `wI_z_sub_evalAr_add_le` (32), `exists_evalAr_eq_of_mem_BISub` (32),
  `exists_eval_series` (31), `evalAr_teichMonomial` (31).
- **Other notes**: `wI_partial_cauchy_diff` and `valued_resAr_le` use the tactic `push Not`
  (a `push_neg` variant); several proofs open with `classical`. There is one substantive
  duplication: the `vp`/`vt` inverse-splitting block appears verbatim in both
  `BIProd_mem_evalRange` (1622–1654) and `exists_evalAr_lift_bloc` (1959–1991) — extracting it
  as a shared `Bloc = Aloc · p^{-k}` lemma would remove ~30 duplicated lines.
