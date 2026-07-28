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
