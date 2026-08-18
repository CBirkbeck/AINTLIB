# Inventory — `projects/Chebotarev/CebotarevDensity/Density.lean`

Namespace `Chebotarev`. Section variables: `{K : Type*} [Field K] [NumberField K]`,
`{S : Set (Ideal (𝓞 K))}`, `{δ : ℝ}`. File-wide `@[expose] public section`, `noncomputable section`.
The block from line 281 onward is under `variable (K)` (K explicit).

---

### `def primeIdealZetaSum`
- **Type**: `(S : Set (Ideal (𝓞 K))) (s : ℝ) : ℝ`, defined as `∑' 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)`.
- **What**: The partial Dirichlet series `Σ_{𝔭 ∈ S} N𝔭^{-s}` summed over nonzero prime ideals of `𝓞 K` that lie in `S`.
- **How**: Definition only — a `tsum` over the 3-part subtype (in `S`, prime, nonzero).
- **Hypotheses**: None (total function; sum may be junk/0 when not summable).
- **Uses from project**: []
- **Used by**: `primeIdealZetaSum_def`, `HasDirichletDensity`, `HasUpperDirichletDensity`, `HasLowerDirichletDensity`, and essentially every theorem in the file.
- **Visibility**: public
- **Lines**: 48–52 (def, no proof)
- **Notes**: none

### `theorem primeIdealZetaSum_def`
- **Type**: `(S : Set (Ideal (𝓞 K))) (s : ℝ) : primeIdealZetaSum S s = ∑' 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)`
- **What**: Equation lemma unfolding `primeIdealZetaSum` to its defining `tsum`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum`
- **Used by**: `hasDirichletDensity_empty`, `primeIdealZetaSum_le_univ`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, `primeIdealZetaSum_empty`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, `primeIdealZetaSum_univ_eq_tsum_prime2`, `primeIdealZetaSum_le_card_of_finite`.
- **Visibility**: public
- **Lines**: 54–58 (proof 1 line)
- **Notes**: none

### `def HasDirichletDensity`
- **Type**: `(S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop`, `Tendsto (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 δ)`.
- **What**: `S` has Dirichlet density `δ` when the ratio of partial sums tends to `δ` as `s ↓ 1` (Sharifi 7.1.13).
- **How**: Definition via `Tendsto` of the density ratio at the right-neighbourhood filter `𝓝[>] 1`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum`
- **Used by**: `hasDirichletDensity_empty`, `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasUpper`, `HasDirichletDensity.hasLower`, `HasDirichletDensity.union_of_disjoint`, `hasDirichletDensity_of_finite`, `hasDirichletDensity_univ`.
- **Visibility**: public
- **Lines**: 60–67 (def, no proof)
- **Notes**: none

### `def HasUpperDirichletDensity`
- **Type**: `(S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop`, `limsup (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) = δ`.
- **What**: Upper Dirichlet density (`limsup` of the ratio); standard convention (upper = limsup), which is Sharifi's inverted "lower"/`δ_sup`.
- **How**: Definition via `limsup` of the density ratio.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum`
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasUpper`.
- **Visibility**: public
- **Lines**: 69–85 (def, no proof; long convention-note docstring)
- **Notes**: none

### `def HasLowerDirichletDensity`
- **Type**: `(S : Set (Ideal (𝓞 K))) (δ : ℝ) : Prop`, `liminf (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s) (𝓝[>] 1) = δ`.
- **What**: Lower Dirichlet density (`liminf` of the ratio); matches Sharifi's `δ_inf` despite his label inversion.
- **How**: Definition via `liminf` of the density ratio.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum`
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasLower`, `HasLowerDirichletDensity.mono`.
- **Visibility**: public
- **Lines**: 87–92 (def, no proof)
- **Notes**: none

### `theorem hasDirichletDensity_empty`
- **Type**: `HasDirichletDensity (∅ : Set (Ideal (𝓞 K))) 0`
- **What**: The Dirichlet density of the empty set is `0`.
- **How**: The defining subtype is `IsEmpty` (membership in `∅` is false), so `tsum_empty` makes the numerator `0`; `zero_div` makes the ratio constantly `0`, and `tendsto_const_nhds` gives the limit.
- **Hypotheses**: None.
- **Uses from project**: `HasDirichletDensity`, `primeIdealZetaSum_def`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 94–100 (proof ~4 lines)
- **Notes**: none

### `private theorem summable_nonzeroIdeal_absNorm_rpow`
- **Type**: `{s : ℝ} (hs : 1 < s) : Summable (fun I : NonzeroIdeal K ↦ (Ideal.absNorm I.1 : ℝ) ^ (-s))`
- **What**: Over the nonzero ideals of `𝓞 K`, the series `Σ_I N(I)^{-s}` is summable for `1 < s`.
- **How**: Transfers summability from the complex Dedekind-zeta Euler product. Hinges on `hasSum_nonzeroIdeal_absNorm_cpow` (project, from `NumberFieldEulerProduct`): takes its `.summable.norm`, then rewrites the norm of `N(I)^{-(s:ℂ)}` to the real `rpow` via `Complex.norm_natCast_cpow_of_pos` (norms nonzero since `Ideal.absNorm_eq_zero_iff`).
- **Hypotheses**: `1 < s`.
- **Uses from project**: `hasSum_nonzeroIdeal_absNorm_cpow` (imported)
- **Used by**: `summable_prime_absNorm_rpow`
- **Visibility**: private
- **Lines**: 102–108 (proof ~5 lines)
- **Notes**: none

### `theorem summable_prime_absNorm_rpow`
- **Type**: `(S : Set (Ideal (𝓞 K))) {s : ℝ} (hs : 1 < s) : Summable (fun 𝔭 : {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))`
- **What**: Over the nonzero prime ideals lying in any set `S`, the series `Σ_𝔭 N𝔭^{-s}` is summable for `1 < s`.
- **How**: The map sending a qualifying prime to its underlying `NonzeroIdeal` is injective (`Subtype.ext`); precompose the all-nonzero-ideals summability `summable_nonzeroIdeal_absNorm_rpow` with this injection via `comp_injective`.
- **Hypotheses**: `1 < s`.
- **Uses from project**: `summable_nonzeroIdeal_absNorm_rpow`
- **Used by**: `primeIdealZetaSum_le_univ`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_union_of_disjoint`, `summable_prime2_absNorm_rpow`.
- **Visibility**: public
- **Lines**: 110–119 (proof ~5 lines)
- **Notes**: none

### `private theorem primeIdealZetaSum_nonneg`
- **Type**: `(S : Set (Ideal (𝓞 K))) (s : ℝ) : 0 ≤ primeIdealZetaSum S s`
- **What**: The partial Dirichlet series is nonnegative.
- **How**: `tsum_nonneg`, each term `N𝔭^{-s} ≥ 0` by `positivity`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum` (via unfolding)
- **Used by**: `primeIdealZetaSum_le_univ` (indirectly), `isBoundedUnder_ge_primeIdealZetaSum_ratio`, `eventually_primeIdealZetaSum_ratio_le_one`, `HasLowerDirichletDensity.mono`, `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`.
- **Visibility**: private
- **Lines**: 121–124 (proof 1 line)
- **Notes**: none

### `private theorem primeIdealZetaSum_le_univ`
- **Type**: `{s : ℝ} (hs : 1 < s) : primeIdealZetaSum S s ≤ primeIdealZetaSum (univ) s`
- **What**: For `1 < s`, the partial sum over `S` is bounded above by the sum over all primes.
- **How**: `tsum_le_tsum_of_inj` along the inclusion of the `S`-subtype into the `univ`-subtype; terms agree (`le_of_eq rfl`), nonnegativity from `Real.rpow_nonneg`, both sides summable via `summable_prime_absNorm_rpow`.
- **Hypotheses**: `1 < s`.
- **Uses from project**: `primeIdealZetaSum_def`, `summable_prime_absNorm_rpow`
- **Used by**: `eventually_primeIdealZetaSum_ratio_le_one`
- **Visibility**: private
- **Lines**: 126–135 (proof ~5 lines)
- **Notes**: none

### `theorem primeIdealZetaSum_le_of_subset`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {s : ℝ} (hs : 1 < s) : primeIdealZetaSum S s ≤ primeIdealZetaSum T s`
- **What**: For `S ⊆ T` and `1 < s`, the partial sum over `S` is bounded above by the one over `T`.
- **How**: `tsum_le_tsum_of_inj` along the subtype inclusion induced by `hST` (terms equal, nonneg via `Real.rpow_nonneg`, summability from `summable_prime_absNorm_rpow`).
- **Hypotheses**: `S ⊆ T`; `1 < s`.
- **Uses from project**: `primeIdealZetaSum_def`, `summable_prime_absNorm_rpow`
- **Used by**: `HasLowerDirichletDensity.mono`
- **Visibility**: public
- **Lines**: 137–146 (proof ~5 lines)
- **Notes**: none

### `theorem primeIdealZetaSum_union_of_disjoint`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {s : ℝ} (hs : 1 < s) : primeIdealZetaSum (S ∪ T) s = primeIdealZetaSum S s + primeIdealZetaSum T s`
- **What**: For disjoint `S`, `T` and `1 < s`, the partial sum over `S ∪ T` splits as the sum over `S` plus the sum over `T`.
- **How**: Builds two explicit `Equiv`s (`eS`, `eT`) identifying the `S`- and `T`-subtypes with the `S`-membership subset of the `S∪T`-subtype and its complement (disjointness via `hDisj.le_bot`); then `tsum_subtype_add_tsum_subtype_compl` (needing `summable_prime_absNorm_rpow (S∪T)`) splits the union sum and the two `Equiv.tsum_eq` rewrites match the pieces, closing by `rfl`.
- **Hypotheses**: `Disjoint S T`; `1 < s`.
- **Uses from project**: `primeIdealZetaSum_def`, `summable_prime_absNorm_rpow`
- **Used by**: `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `HasDirichletDensity.union_of_disjoint`.
- **Visibility**: public
- **Lines**: 148–171 (proof ~18 lines incl. two Equiv definitions)
- **Notes**: none (18 lines, under 30)

### `theorem primeIdealZetaSum_empty`
- **Type**: `(s : ℝ) : primeIdealZetaSum (∅ : Set (Ideal (𝓞 K))) s = 0`
- **What**: The partial Dirichlet series over the empty set is `0`.
- **How**: The defining subtype is `IsEmpty`, so the `tsum` is `0` by `tsum_empty`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum_def`
- **Used by**: `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`
- **Visibility**: public
- **Lines**: 173–177 (proof ~3 lines)
- **Notes**: none

### `theorem primeIdealZetaSum_biUnion_of_pairwiseDisjoint`
- **Type**: `{ι : Type*} (t : Finset ι) (g : ι → Set (Ideal (𝓞 K))) (hg : (t : Set ι).PairwiseDisjoint g) {s : ℝ} (hs : 1 < s) : primeIdealZetaSum (⋃ i ∈ t, g i) s = ∑ i ∈ t, primeIdealZetaSum (g i) s`
- **What**: For a `Finset`-indexed pairwise-disjoint family, the partial sum over the union equals the finite sum of the partial sums.
- **How**: `Finset.induction` on `t`; the insert step uses `disjoint_iUnion₂_right` to get `g a` disjoint from the rest, then `primeIdealZetaSum_union_of_disjoint` plus `Finset.sum_insert` and the induction hypothesis (restricting pairwise-disjointness via `hg.subset`).
- **Hypotheses**: `t` a finite index set; `g` pairwise-disjoint on `t`; `1 < s`.
- **Uses from project**: `primeIdealZetaSum_empty`, `primeIdealZetaSum_union_of_disjoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 179–193 (proof ~9 lines)
- **Notes**: none; uses `classical`

### `theorem primeIdealZetaSum_eq_univ_of_forall_prime_mem`
- **Type**: `(hS : ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭 ∈ S) (s : ℝ) : primeIdealZetaSum S s = primeIdealZetaSum (univ) s`
- **What**: If `S` contains every nonzero prime ideal, its partial Dirichlet series equals the one over `univ`.
- **How**: `Equiv.subtypeEquivRight` matching the `S`-subtype with the `univ`-subtype (membership conditions equivalent given `hS`), then `Equiv.tsum_eq` and `rfl`.
- **Hypotheses**: `S` contains all nonzero primes.
- **Uses from project**: `primeIdealZetaSum_def`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 195–206 (proof ~6 lines)
- **Notes**: none

### `private theorem isBoundedUnder_ge_primeIdealZetaSum_ratio`
- **Type**: `(S : Set (Ideal (𝓞 K))) : IsBoundedUnder (· ≥ ·) (𝓝[>] (1 : ℝ)) (fun s ↦ primeIdealZetaSum S s / primeIdealZetaSum univ s)`
- **What**: The density ratio `Σ_S / Σ_univ` is bounded below (always nonnegative).
- **How**: `isBoundedUnder_of` with lower bound `0`, nonnegativity from `div_nonneg` of two `primeIdealZetaSum_nonneg`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum_nonneg`
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasLowerDirichletDensity.mono`.
- **Visibility**: private
- **Lines**: 208–213 (proof ~2 lines)
- **Notes**: none

### `private theorem eventually_primeIdealZetaSum_ratio_le_one`
- **Type**: `(S : Set (Ideal (𝓞 K))) : ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum S s / primeIdealZetaSum univ s ≤ 1`
- **What**: The density ratio `Σ_S / Σ_univ` is eventually `≤ 1` as `s ↓ 1`.
- **How**: `filter_upwards [self_mem_nhdsWithin]`; for `s > 1`, `div_le_one_of_le₀` using `primeIdealZetaSum_le_univ` and `primeIdealZetaSum_nonneg`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum_le_univ`, `primeIdealZetaSum_nonneg`
- **Used by**: `HasDirichletDensity.of_upper_eq_lower`, `HasLowerDirichletDensity.mono`.
- **Visibility**: private
- **Lines**: 215–223 (proof ~4 lines)
- **Notes**: none

### `theorem HasDirichletDensity.of_upper_eq_lower`
- **Type**: `(hUp : HasUpperDirichletDensity S δ) (hLow : HasLowerDirichletDensity S δ) : HasDirichletDensity S δ`
- **What**: Sandwich criterion — if upper density = lower density = `δ`, then `S` has Dirichlet density `δ` (Sharifi 7.2.2 Step 2).
- **How**: `tendsto_of_liminf_eq_limsup` from the matching liminf/limsup, with eventual upper bound `1` (from `eventually_primeIdealZetaSum_ratio_le_one`) and the lower bound (from `isBoundedUnder_ge_primeIdealZetaSum_ratio`).
- **Hypotheses**: upper and lower densities both equal `δ`.
- **Uses from project**: `HasUpperDirichletDensity`, `HasLowerDirichletDensity`, `HasDirichletDensity`, `eventually_primeIdealZetaSum_ratio_le_one`, `isBoundedUnder_ge_primeIdealZetaSum_ratio`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 225–233 (proof ~4 lines)
- **Notes**: none

### `theorem HasDirichletDensity.hasUpper`
- **Type**: `(h : HasDirichletDensity S δ) : HasUpperDirichletDensity S δ`
- **What**: A Dirichlet density yields the equal upper Dirichlet density.
- **How**: `h.limsup_eq` (limit ⇒ limsup equals the limit).
- **Hypotheses**: `S` has Dirichlet density `δ`.
- **Uses from project**: `HasDirichletDensity`, `HasUpperDirichletDensity`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 235–238 (proof 1 line)
- **Notes**: none

### `theorem HasDirichletDensity.hasLower`
- **Type**: `(h : HasDirichletDensity S δ) : HasLowerDirichletDensity S δ`
- **What**: A Dirichlet density yields the equal lower Dirichlet density.
- **How**: `h.liminf_eq` (limit ⇒ liminf equals the limit).
- **Hypotheses**: `S` has Dirichlet density `δ`.
- **Uses from project**: `HasDirichletDensity`, `HasLowerDirichletDensity`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 240–243 (proof 1 line)
- **Notes**: none

### `theorem HasDirichletDensity.union_of_disjoint`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hDisj : Disjoint S T) {ε : ℝ} (hS : HasDirichletDensity S δ) (hT : HasDirichletDensity T ε) : HasDirichletDensity (S ∪ T) (δ + ε)`
- **What**: The Dirichlet density of a disjoint union is the sum of the densities.
- **How**: Adds the two limits (`hS.add hT`) and shows the union ratio eventually agrees: `filter_upwards`, then `primeIdealZetaSum_union_of_disjoint` + `add_div` for `s > 1`.
- **Hypotheses**: `S`, `T` disjoint; `S` has density `δ`, `T` has density `ε`.
- **Uses from project**: `HasDirichletDensity`, `primeIdealZetaSum_union_of_disjoint`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 245–253 (proof ~5 lines)
- **Notes**: none

### `theorem HasLowerDirichletDensity.mono`
- **Type**: `{T : Set (Ideal (𝓞 K))} (hST : S ⊆ T) {ε : ℝ} (hS : HasLowerDirichletDensity S δ) (hT : HasLowerDirichletDensity T ε) : δ ≤ ε`
- **What**: Monotonicity of the lower Dirichlet density under inclusion `S ⊆ T`.
- **How**: Rewrites both densities as liminfs and applies `liminf_le_liminf`; the eventual pointwise ratio inequality comes from `primeIdealZetaSum_le_of_subset` and `div_le_div_of_nonneg_right`; co/boundedness from `isBoundedUnder_ge_primeIdealZetaSum_ratio` and `isCoboundedUnder_ge_of_eventually_le` (using `eventually_primeIdealZetaSum_ratio_le_one T`).
- **Hypotheses**: `S ⊆ T`; both have lower densities (`δ`, `ε`).
- **Uses from project**: `HasLowerDirichletDensity`, `isBoundedUnder_ge_primeIdealZetaSum_ratio`, `eventually_primeIdealZetaSum_ratio_le_one`, `primeIdealZetaSum_le_of_subset`, `primeIdealZetaSum_nonneg`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 255–267 (proof ~9 lines)
- **Notes**: none

### `private theorem summable_prime2_absNorm_rpow`
- **Type**: `{s : ℝ} (hs : 1 < s) : Summable (fun 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))` (K explicit)
- **What**: Over the bare 2-part nonzero-prime subtype (no ambient set), `Σ_𝔭 N𝔭^{-s}` is summable for `1 < s`.
- **How**: Re-indexes `summable_prime_absNorm_rpow univ` along `Equiv.subtypeEquivRight` (dropping the trivial `∈ univ` condition) via `comp_injective`.
- **Hypotheses**: `1 < s`.
- **Uses from project**: `summable_prime_absNorm_rpow`
- **Used by**: `primeIdealZetaHigherTail_bounded`, `summable_neg_log_one_sub_absNorm_rpow`, `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private
- **Lines**: 283–290 (proof ~3 lines)
- **Notes**: none

### `private theorem two_le_absNorm_of_prime`
- **Type**: `{𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ)` (K explicit)
- **What**: A nonzero prime ideal of `𝓞 K` has absolute norm at least `2`.
- **How**: `Nat.two_le_iff`: norm `≠ 0` (`Ideal.absNorm_eq_zero_iff`, since `𝔭 ≠ ⊥`) and `≠ 1` (`Ideal.absNorm_eq_one_iff`, since prime ⇒ not top); cast to `ℝ`.
- **Hypotheses**: `𝔭` prime and nonzero.
- **Uses from project**: []
- **Used by**: `absNorm_rpow_neg_lt_one`, `primeIdealHigherTail_term_le`.
- **Visibility**: private
- **Lines**: 292–297 (proof ~3 lines)
- **Notes**: none

### `private theorem absNorm_rpow_neg_lt_one`
- **Type**: `{𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ} (hs : 1 < s) : (Ideal.absNorm 𝔭 : ℝ) ^ (-s) < 1` (K explicit)
- **What**: For a nonzero prime `𝔭` and `1 < s`, the Euler factor `N𝔭^{-s} < 1`.
- **How**: `Real.rpow_lt_one_of_one_lt_of_neg` with base `> 1` (from `two_le_absNorm_of_prime`) and negative exponent.
- **Hypotheses**: `𝔭` prime and nonzero; `1 < s`.
- **Uses from project**: `two_le_absNorm_of_prime`
- **Used by**: `primeIdealZetaHigherTail_bounded`, `one_sub_absNorm_rpow_pos`, `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private
- **Lines**: 299–303 (proof ~2 lines)
- **Notes**: none

### `private theorem primeIdealHigherTail_term_le`
- **Type**: `{𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ} (hs : 1 < s) : (Ideal.absNorm 𝔭 : ℝ) ^ (-(2:ℝ)*s) / (1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)) ≤ 2 * (Ideal.absNorm 𝔭 : ℝ) ^ (-(2:ℝ))` (K explicit)
- **What**: Per-prime termwise bound for the higher-power tail: the geometric term `N𝔭^{-2s}/(1 - N𝔭^{-s})` is dominated by `2·N𝔭^{-2}`.
- **How**: Set `x = N𝔭`; show `x^{-s} ≤ 1/2` by a 3-step `rpow` `calc` (monotone in base then in exponent down to `2^{-1}`), giving denominator `1 - x^{-s} ≥ 1/2` hence inverse `≤ 2` (`inv_le_comm₀`), and `x^{-2s} ≤ x^{-2}` (`Real.rpow_le_rpow_of_exponent_le`, `nlinarith`); combine via `mul_le_mul`.
- **Hypotheses**: `𝔭` prime and nonzero; `1 < s`.
- **Uses from project**: `two_le_absNorm_of_prime`
- **Used by**: `primeIdealZetaHigherTail_bounded`, `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private
- **Lines**: 305–325 (proof ~15 lines)
- **Notes**: none (15 lines, under 30)

### `theorem primeIdealZetaHigherTail_bounded`
- **Type**: `: ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(2:ℝ)*s) / (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) ≤ C` (K explicit)
- **What**: The geometric higher-power tail `Σ_{𝔭,k≥2} N𝔭^{-ks}` is bounded on a right neighbourhood of `s=1` (Sharifi 7.1.12 bounded-tail step).
- **How**: Takes `C = 2·Σ_𝔭 N𝔭^{-2}`; for each `s>1` bounds the tsum termwise by `primeIdealHigherTail_term_le`, with nonnegativity (via `absNorm_rpow_neg_lt_one`) and RHS summability (`summable_prime2_absNorm_rpow` at exponent `2`), via `Summable.of_nonneg_of_le.tsum_le_tsum` and `tsum_mul_left`.
- **Hypotheses**: None (existential constant).
- **Uses from project**: `summable_prime2_absNorm_rpow`, `primeIdealHigherTail_term_le`, `absNorm_rpow_neg_lt_one`.
- **Used by**: `abs_tsum_neg_log_one_sub_sub_rpow_le`
- **Visibility**: public
- **Lines**: 327–355 (proof ~22 lines)
- **Notes**: none (22 lines, under 30)

### `private theorem primeIdealZetaSum_univ_eq_tsum_prime2`
- **Type**: `(s : ℝ) : primeIdealZetaSum (univ) s = ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)` (K explicit)
- **What**: Re-indexes the `univ` partial Dirichlet sum over the bare 2-part nonzero-prime subtype.
- **How**: `Equiv.subtypeEquivRight` dropping the `∈ univ` condition, `Equiv.tsum_eq`, then `rfl`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum_def`
- **Used by**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`
- **Visibility**: private
- **Lines**: 357–364 (proof ~3 lines)
- **Notes**: none

### `private theorem one_sub_absNorm_rpow_pos`
- **Type**: `{𝔭 : Ideal (𝓞 K)} (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) {s : ℝ} (hs : 1 < s) : (0 : ℝ) < 1 - (Ideal.absNorm 𝔭 : ℝ) ^ (-s)` (K explicit)
- **What**: For a nonzero prime `𝔭` and `1 < s`, the Euler-factor denominator `1 - N𝔭^{-s}` is positive.
- **How**: `absNorm_rpow_neg_lt_one` gives `N𝔭^{-s} < 1`; `linarith`.
- **Hypotheses**: `𝔭` prime and nonzero; `1 < s`.
- **Uses from project**: `absNorm_rpow_neg_lt_one`
- **Used by**: `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`, `abs_tsum_neg_log_one_sub_sub_rpow_le`.
- **Visibility**: private
- **Lines**: 366–370 (proof ~2 lines)
- **Notes**: none

### `private theorem neg_log_one_sub_sub_le`
- **Type**: `{x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 ≤ -Real.log (1 - x) - x ∧ -Real.log (1 - x) - x ≤ x ^ 2 / (1 - x)`
- **What**: Elementary analytic bound: for `0 ≤ x < 1`, `0 ≤ -log(1-x) - x ≤ x²/(1-x)`.
- **How**: Lower bound from `Real.log_le_sub_one_of_pos` (applied to `1-x`); upper bound from the mathlib power-series remainder estimate `Real.abs_log_sub_add_sum_range_le` at `n=1` (the `Σ x^k/k` truncation), simplified at `range 1` and closed by `linarith`.
- **Hypotheses**: `0 ≤ x < 1`.
- **Uses from project**: []
- **Used by**: `abs_tsum_neg_log_one_sub_sub_rpow_le`
- **Visibility**: private
- **Lines**: 372–381 (proof ~7 lines)
- **Notes**: none

### `private theorem summable_neg_log_one_sub_absNorm_rpow`
- **Type**: `{s : ℝ} (hs : 1 < s) : Summable (fun 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ -Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)))` (K explicit)
- **What**: For `1 < s`, the Euler-factor logs `-log(1 - N𝔭^{-s})` are summable over nonzero primes.
- **How**: `Real.summable_log_one_add_of_summable` applied to the negated summable family `(summable_prime2_absNorm_rpow).neg`, then negate and rewrite `sub_eq_add_neg`.
- **Hypotheses**: `1 < s`.
- **Uses from project**: `summable_prime2_absNorm_rpow`
- **Used by**: `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`, `abs_tsum_neg_log_one_sub_sub_rpow_le`, `logDedekindZeta_sub_primeIdealZetaSum_bounded`.
- **Visibility**: private
- **Lines**: 383–389 (proof ~3 lines)
- **Notes**: none

### `private theorem log_dedekindZeta_re_eq_tsum_neg_log_one_sub`
- **Type**: `{s : ℝ} (hs : 1 < s) : Real.log (dedekindZeta K (s : ℂ)).re = ∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (-Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)))` (K explicit)
- **What**: For real `s > 1`, `log ζ_K(s) = Σ_𝔭 -log(1 - N𝔭^{-s})` (Sharifi 7.1.12).
- **How**: Sets `g 𝔭 = (1 - N𝔭^{-s})⁻¹ > 0` (via `one_sub_absNorm_rpow_pos`); from `summable_neg_log_one_sub_absNorm_rpow` the logs are summable, so `Real.hasProd_of_hasSum_log` gives a convergent real product, pushed to `ℂ` (`Complex.ofReal_cpow`) and matched against the mathlib Euler product `dedekindZeta_eq_tprod_primeIdeal`; taking `.re` and `Real.log_exp` finishes.
- **Hypotheses**: `1 < s`.
- **Uses from project**: `one_sub_absNorm_rpow_pos`, `summable_neg_log_one_sub_absNorm_rpow`
- **Used by**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`
- **Visibility**: private
- **Lines**: 391–415 (proof ~22 lines)
- **Notes**: none (22 lines, under 30); hinges on mathlib `dedekindZeta_eq_tprod_primeIdeal`, `Real.hasProd_of_hasSum_log`

### `private theorem abs_tsum_neg_log_one_sub_sub_rpow_le`
- **Type**: `: ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |∑' 𝔭 : {𝔭 // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}, (-Real.log (1 - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s)) - (Ideal.absNorm 𝔭.1 : ℝ) ^ (-s))| ≤ C` (K explicit)
- **What**: The remainder `Σ_𝔭 (-log(1 - N𝔭^{-s}) - N𝔭^{-s})` is bounded near `s=1` (Sharifi 7.1.12).
- **How**: Reuses the bound `C` from `primeIdealZetaHigherTail_bounded`; the per-term `f 𝔭` is sandwiched `0 ≤ f 𝔭 ≤ h 𝔭` where `h 𝔭` is the geometric tail term — lower/upper via `neg_log_one_sub_sub_le` (after rewriting `x²` as `N𝔭^{-2s}` via `Real.rpow_natCast`/`Real.rpow_mul`), `h` summable by `Summable.of_nonneg_of_le` with `primeIdealHigherTail_term_le`; `abs_of_nonneg` then `tsum_le_tsum` chains to `C`.
- **Hypotheses**: None (existential constant).
- **Uses from project**: `primeIdealZetaHigherTail_bounded`, `absNorm_rpow_neg_lt_one`, `neg_log_one_sub_sub_le`, `primeIdealHigherTail_term_le`, `one_sub_absNorm_rpow_pos`, `summable_prime2_absNorm_rpow`, `summable_neg_log_one_sub_absNorm_rpow`.
- **Used by**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`
- **Visibility**: private
- **Lines**: 417–452 (proof ~33 lines)
- **Notes**: `long (30–50)` — 33-line proof
- **Note (Uses)**: `summable_neg_log_one_sub_absNorm_rpow` is reachable here but the explicit body references listed are the ones actually named; conservative listing kept.

### `theorem logDedekindZeta_sub_primeIdealZetaSum_bounded`
- **Type**: `: ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re - primeIdealZetaSum (univ) s| ≤ C` (K explicit)
- **What**: Euler-product-log identity with bounded remainder: `log ζ_K(s) = Σ_𝔭 N𝔭^{-s} + O(1)` as `s ↓ 1` (Sharifi 7.1.12).
- **How**: Pulls `C` from `abs_tsum_neg_log_one_sub_sub_rpow_le`; for `s>1` rewrites `log ζ_K` via `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`, the sum via `primeIdealZetaSum_univ_eq_tsum_prime2`, and subtracts termwise using `Summable.tsum_sub` (`summable_neg_log_one_sub_absNorm_rpow`, `summable_prime2_absNorm_rpow`).
- **Hypotheses**: None (existential constant).
- **Uses from project**: `abs_tsum_neg_log_one_sub_sub_rpow_le`, `log_dedekindZeta_re_eq_tsum_neg_log_one_sub`, `primeIdealZetaSum_univ_eq_tsum_prime2`, `summable_neg_log_one_sub_absNorm_rpow`, `summable_prime2_absNorm_rpow`.
- **Used by**: `log_minus_bounded_le_primeIdealZetaSum`, `primeIdealZetaSum_le_log_plus_bounded`.
- **Visibility**: public
- **Lines**: 454–466 (proof ~7 lines)
- **Notes**: none

### `theorem logDedekindZeta_sub_log_inv_sub_one_bounded`
- **Type**: `: ∃ C : ℝ, ∀ᶠ (s : ℝ) in 𝓝[>] (1 : ℝ), |Real.log (dedekindZeta K (s : ℂ)).re - Real.log (1 / (s - 1))| ≤ C` (K explicit)
- **What**: Simple-pole identity: `log ζ_K(s) = log(1/(s-1)) + O(1)` as `s ↓ 1`, from the simple pole of `ζ_K` at `s=1` (Sharifi 7.1.12).
- **How**: Uses mathlib `tendsto_sub_one_mul_dedekindZeta_nhdsGT` (and positivity `dedekindZeta_residue_pos`): `(s-1)·ζ_K(s).re → r > 0`, so it eventually lies in `Ioo (r/2) (2r)`; on that event `log(1/(s-1)) = log ζ_K + log((s-1)ζ_K)` and the residual is bounded by `max |log(r/2)| |log(2r)|` via `Real.log_lt_log` monotonicity and `abs_le_max_abs_abs`.
- **Hypotheses**: None (existential constant).
- **Uses from project**: []
- **Used by**: `log_minus_bounded_le_primeIdealZetaSum`, `primeIdealZetaSum_le_log_plus_bounded`.
- **Visibility**: public
- **Lines**: 468–494 (proof ~22 lines)
- **Notes**: none (22 lines, under 30); hinges on mathlib `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `dedekindZeta_residue_pos`

### `theorem log_minus_bounded_le_primeIdealZetaSum`
- **Type**: `: ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), Real.log (1 / (s - 1)) - C ≤ primeIdealZetaSum (univ) s` (K explicit)
- **What**: Lower bound `log(1/(s-1)) - C ≤ Σ_𝔭 N𝔭^{-s}` (Sharifi 7.1.12).
- **How**: Combines the two `O(1)` bounds (`logDedekindZeta_sub_primeIdealZetaSum_bounded`, `logDedekindZeta_sub_log_inv_sub_one_bounded`) with constant `C₁+C₂`, then `linarith` on the unpacked `abs_le` inequalities.
- **Hypotheses**: None (existential constant).
- **Uses from project**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`, `logDedekindZeta_sub_log_inv_sub_one_bounded`.
- **Used by**: `primeIdealZetaSum_univ_tendsto_log`
- **Visibility**: public
- **Lines**: 496–505 (proof ~4 lines)
- **Notes**: none

### `theorem primeIdealZetaSum_le_log_plus_bounded`
- **Type**: `: ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum (univ) s ≤ Real.log (1 / (s - 1)) + C` (K explicit)
- **What**: Upper bound `Σ_𝔭 N𝔭^{-s} ≤ log(1/(s-1)) + C'` (Sharifi 7.1.12).
- **How**: Same two `O(1)` bounds with constant `C₁+C₂`, then `linarith` on the `abs_le` inequalities.
- **Hypotheses**: None (existential constant).
- **Uses from project**: `logDedekindZeta_sub_primeIdealZetaSum_bounded`, `logDedekindZeta_sub_log_inv_sub_one_bounded`.
- **Used by**: `primeIdealZetaSum_univ_tendsto_log`
- **Visibility**: public
- **Lines**: 507–516 (proof ~4 lines)
- **Notes**: none

### `theorem primeIdealZetaSum_univ_tendsto_log`
- **Type**: `: Tendsto (fun s : ℝ ↦ primeIdealZetaSum (univ) s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 1)` (K explicit)
- **What**: **Sharifi 7.1.12** — the denominator `Σ_𝔭 N𝔭^{-s}` is asymptotic to `log(1/(s-1))` as `s ↓ 1`.
- **How**: `tendsto_ratio_one_of_log_pm_bounded` (project/imported helper) fed the matching upper and lower `O(1)` bounds `primeIdealZetaSum_le_log_plus_bounded` and `log_minus_bounded_le_primeIdealZetaSum`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum_le_log_plus_bounded`, `log_minus_bounded_le_primeIdealZetaSum`.
- **Used by**: `primeIdealZetaSum_univ_tendsto_atTop`
- **Visibility**: public
- **Lines**: 518–531 (proof ~4 lines)
- **Notes**: none; relies on imported `tendsto_ratio_one_of_log_pm_bounded` (from `ForMathlib.LogOneDivSubOne`)

### `theorem primeIdealZetaSum_univ_tendsto_atTop`
- **Type**: `: Tendsto (primeIdealZetaSum (univ : Set (Ideal (𝓞 K)))) (𝓝[>] 1) atTop` (K explicit)
- **What**: The full prime-ideal zeta sum diverges to `+∞` as `s ↓ 1`.
- **How**: Since `½·log(1/(s-1)) → ∞` (`tendsto_log_one_div_sub_one_atTop.const_mul_atTop`), and eventually `½·log(1/(s-1)) ≤ Σ_univ` (from `primeIdealZetaSum_univ_tendsto_log` giving ratio `> ½`, via `lt_div_iff₀`), `tendsto_atTop_mono'` concludes.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum_univ_tendsto_log`
- **Used by**: `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`, `hasDirichletDensity_univ`.
- **Visibility**: public
- **Lines**: 533–543 (proof ~7 lines)
- **Notes**: none; uses imported `tendsto_log_one_div_sub_one_atTop`

### `theorem primeIdealZetaSum_le_card_of_finite`
- **Type**: `(hS : S.Finite) {s : ℝ} (hs : 0 < s) : primeIdealZetaSum S s ≤ Nat.card {𝔭 // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}` (K explicit)
- **What**: For finite `S` and `s > 0`, the partial sum is bounded by the number of qualifying primes (finitely many terms, each `≤ 1`).
- **How**: The subtype is `Finite` (subset of finite `S`) hence `Fintype`; `tsum_fintype` makes it a finite sum, each term `N𝔭^{-s} ≤ 1` by `Real.rpow_le_one_of_one_le_of_nonpos` (base `≥ 1` since norm `≠ 0`), summed to `Fintype.card` via `Finset.sum_const`.
- **Hypotheses**: `S` finite; `0 < s`.
- **Uses from project**: `primeIdealZetaSum_def`
- **Used by**: `hasDirichletDensity_of_finite`
- **Visibility**: public
- **Lines**: 545–563 (proof ~9 lines)
- **Notes**: none

### `theorem tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`
- **Type**: `(U : Set (Ideal (𝓞 K))) (C : ℝ) (hbd : ∀ᶠ s in 𝓝[>] (1 : ℝ), primeIdealZetaSum U s ≤ C) : Tendsto (fun s ↦ primeIdealZetaSum U s / primeIdealZetaSum univ s) (𝓝[>] 1) (𝓝 0)` (K explicit)
- **What**: Squeeze-to-zero engine: if `Σ_U` is eventually bounded by a constant `C` near `s=1`, the density ratio `Σ_U / Σ_univ → 0` (denominator `→ ∞`). Shared by the finite case and the Chebotarev ramified/degree-≥2 tail bound.
- **How**: `tendsto_of_tendsto_of_tendsto_of_le_of_le'` squeeze between `0` and `C / Σ_univ → 0` (`tendsto_const_nhds.div_atTop` using `primeIdealZetaSum_univ_tendsto_atTop`); lower/upper pointwise bounds on `𝓝[>] 1` from `primeIdealZetaSum_nonneg` and `div_le_div_iff_of_pos_right` with `hbd` (denominator positive eventually).
- **Hypotheses**: `Σ_U` eventually `≤ C` near `s=1`.
- **Uses from project**: `primeIdealZetaSum_univ_tendsto_atTop`, `primeIdealZetaSum_nonneg`.
- **Used by**: `hasDirichletDensity_of_finite`
- **Visibility**: public
- **Lines**: 565–583 (proof ~13 lines)
- **Notes**: none

### `theorem hasDirichletDensity_of_finite`
- **Type**: `(hS : S.Finite) : HasDirichletDensity S 0` (K explicit)
- **What**: **Density of a finite set of primes is `0`** (Sharifi 7.1.13).
- **How**: Applies the squeeze engine `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const` with the constant bound from `primeIdealZetaSum_le_card_of_finite` (valid since `s > 1 > 0` on `𝓝[>] 1`).
- **Hypotheses**: `S` finite.
- **Uses from project**: `tendsto_primeIdealZetaSum_div_univ_zero_of_le_const`, `primeIdealZetaSum_le_card_of_finite`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 585–592 (proof ~3 lines)
- **Notes**: none

### `theorem hasDirichletDensity_univ`
- **Type**: `: HasDirichletDensity (univ : Set (Ideal (𝓞 K))) 1` (K explicit)
- **What**: The Dirichlet density of the set of all nonzero prime ideals is `1`.
- **How**: The ratio `Σ_univ / Σ_univ` is eventually `1` (denominator eventually `> 0` since `Σ_univ → ∞` by `primeIdealZetaSum_univ_tendsto_atTop`), via `div_self` and `tendsto_const_nhds.congr'`.
- **Hypotheses**: None.
- **Uses from project**: `primeIdealZetaSum_univ_tendsto_atTop`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 594–601 (proof ~4 lines)
- **Notes**: none

---

## File Summary

**Total declarations: 30** (this excludes the documentation-only `/-! ... -/` section headers).
- **defs: 4** — `primeIdealZetaSum`, `HasDirichletDensity`, `HasUpperDirichletDensity`, `HasLowerDirichletDensity`.
- **lemmas / theorems: 26** (incl. the `primeIdealZetaSum_def` equation lemma; comprises 12 private + 14 public theorems).
- **instances / structures / classes / abbrevs / inductives: 0**. (Two local `Equiv`s `eS`/`eT` and one local `e` are `let`-bound inside proofs, not top-level declarations.)

**Key API (used by ≥ 3 in-file decls):**
- `primeIdealZetaSum` — foundational; used by nearly every decl.
- `primeIdealZetaSum_def` — used by ≥ 8 decls.
- `HasDirichletDensity` — used by ≥ 7 decls.
- `primeIdealZetaSum_nonneg` — used by ≥ 5 decls.
- `summable_prime_absNorm_rpow` — used by 4 decls.
- `summable_prime2_absNorm_rpow` — used by 3 decls.
- `absNorm_rpow_neg_lt_one` — used by 3 decls.
- `primeIdealHigherTail_term_le` — used by 3 decls (`primeIdealZetaHigherTail_bounded`, `abs_tsum_neg_log_one_sub_sub_rpow_le`, plus inline summability bound).
- `logDedekindZeta_sub_primeIdealZetaSum_bounded`, `logDedekindZeta_sub_log_inv_sub_one_bounded` — each used by 2 (just under the threshold).
- `primeIdealZetaSum_univ_tendsto_atTop` — used by 3 decls.

**Unused-in-file declarations (terminal / public-API exports):** `hasDirichletDensity_empty`, `primeIdealZetaSum_biUnion_of_pairwiseDisjoint`, `primeIdealZetaSum_eq_univ_of_forall_prime_mem`, `HasDirichletDensity.of_upper_eq_lower`, `HasDirichletDensity.hasUpper`, `HasDirichletDensity.hasLower`, `HasDirichletDensity.union_of_disjoint`, `HasLowerDirichletDensity.mono`, `hasDirichletDensity_of_finite`, `hasDirichletDensity_univ`. (These are the intended downstream API for the Chebotarev development; "unused" only means no *other decl in this file* calls them.)

**Declarations with `sorry`: none.**

**Declarations with `set_option`: none.**

**Proofs > 50 lines (decompose-needed): none.**

**Proofs 30–50 lines (long):**
- `abs_tsum_neg_log_one_sub_sub_rpow_le` — **33 lines** (lines 417–452).

**Borderline (20–29 lines), for awareness (no flag required):**
- `primeIdealHigherTail_term_le` — ~15 lines (305–325).
- `primeIdealZetaHigherTail_bounded` — ~22 lines (327–355).
- `log_dedekindZeta_re_eq_tsum_neg_log_one_sub` — ~22 lines (391–415).
- `logDedekindZeta_sub_log_inv_sub_one_bounded` — ~22 lines (468–494).
- `primeIdealZetaSum_union_of_disjoint` — ~18 lines (148–171, two inline `Equiv`s).

**External dependency notes:** the file leans on imported project helpers `hasSum_nonzeroIdeal_absNorm_cpow`, `dedekindZeta_eq_tprod_primeIdeal` (`NumberFieldEulerProduct`) and `tendsto_ratio_one_of_log_pm_bounded`, `tendsto_log_one_div_sub_one_atTop` (`ForMathlib.LogOneDivSubOne`), plus mathlib `tendsto_sub_one_mul_dedekindZeta_nhdsGT`, `dedekindZeta_residue_pos`, `Real.hasProd_of_hasSum_log`, `Real.abs_log_sub_add_sum_range_le`.
