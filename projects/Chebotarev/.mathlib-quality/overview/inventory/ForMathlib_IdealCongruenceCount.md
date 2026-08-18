# Inventory — `ForMathlib/IdealCongruenceCount.lean`

Repo-relative path: `projects/Chebotarev/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean`
File length: 3437 lines. Namespace `Chebotarev`. `@[expose] public section` + `noncomputable section`.
**ForMathlib note**: all decls here are author-earmarked for mathlib; generality/naming flags below.
No `sorry` / `set_option` / `admit` / `TODO` anywhere in the file.

Cross-file project deps used (NOT in this file): `eq_of_sum_char_mul_eq_zero`,
`sum_char_self_eq_zero_of_ne_one` (both in sibling `ForMathlib/CharacterOrthogonality.lean`);
`exists_card_inter_smul_lattice_sub_volume_mul_pow_le` / `abs_card_inter_sub_volume_mul_pow_le` /
`ncard_index_image_le_of_diam_le` / `ncard_index_image_chart_le` /
`setFinite_index_image_of_isBounded` (in `ForMathlib/LatticePointCount`);
`normLeOne_frontier_lipschitz_cover_index` / `isBounded_normLeOne` / `measurableSet_normLeOne`
(in `ForMathlib/NormLeOneLipschitz`). These are project decls but external to THIS file, so they
appear in "Uses from project" only when genuinely from this file's siblings is intended — per the
task they are project references and are listed; the **Used by** field only tracks intra-file use.

---

### `private theorem isBounded_image_smul_add`
- **Type**: `LipschitzWith M φ → (c : ℝ) → (v : ι→ℝ) → IsBounded A → IsBounded ((fun y ↦ v + c • φ y) '' A)`
- **What**: The image of a bounded set under an affine-scaled Lipschitz map `y ↦ v + c·φ y` is bounded.
- **How**: Rewrites the image as `v +ᵥ (c • (φ '' A))` set-theoretically, then uses that Lipschitz images of bounded sets are bounded (`LipschitzWith.isBounded_image`) and that scaling/translation preserve boundedness.
- **Hypotheses**: `φ` Lipschitz; `A` bounded; `c` real scalar, `v` translation vector.
- **Uses from project**: []
- **Used by**: `ncard_index1_image_smul_chart_le`, `abs_cardR_translate_sub_volume_le`
- **Visibility**: private
- **Lines**: 83–95 (proof ~9)
- **Notes**: none

### `private theorem diam_ceil_fibre_le`
- **Type**: `(N : ℕ) → (0 < (N:ℝ)) → (w : Fin d → ℤ) → diam (Icc 0 1 ∩ (fun y k ↦ ⌈N·y k⌉)⁻¹' {w}) ≤ 1/N`
- **What**: A fibre of the ceiling-grid map `y ↦ ⌈N·y⌉` inside the unit cube has diameter `≤ 1/N`.
- **How**: For two points in the same fibre, equal ceilings force `|N·yₖ − N·y'ₖ| ≤ 1` per coordinate (`Int.ceil_eq_iff`, `nlinarith`); divide by `N` and use the sup-metric (`dist_pi_le_iff`).
- **Hypotheses**: `N > 0`; points share the ceiling-fibre `w`.
- **Uses from project**: []
- **Used by**: `ncard_index1_image_smul_chart_le`
- **Visibility**: private
- **Lines**: 97–116 (proof ~18)
- **Notes**: none

### `private theorem ncard_index1_image_smul_chart_le`
- **Type**: `LipschitzWith M φ → 1 ≤ c → (v) → (index 1 '' ((fun y ↦ v + c•φ y) '' Icc 0 1)).ncard ≤ (2⌈M⌉₊+1)^card ι · (⌈c⌉₊+1)^(card ι −1)`
- **What**: The number of unit grid cells (`index 1`) meeting a scaled-translated Lipschitz chart image is `O(c^{card ι −1})`.
- **How**: Subdivide `[0,1]^{d−1}` into the `(⌈c⌉₊+1)^{d−1}` ceiling-fibres (each of diameter `≤1/⌈c⌉₊` by `diam_ceil_fibre_le`); on each the scaled image has diameter `≤ M`, so it meets `≤ (2⌈M⌉₊+1)^{card ι}` unit cells via `ncard_index_image_le_of_diam_le` (LatticePointCount); sum over fibres (`Finset.set_ncard_biUnion_le`, `Pi.card_Icc`).
- **Hypotheses**: `φ` Lipschitz with constant `M`; `c ≥ 1`; arbitrary translate `v`.
- **Uses from project**: `diam_ceil_fibre_le`, `isBounded_image_smul_add`
- **Used by**: `abs_cardR_translate_sub_volume_le`
- **Visibility**: private
- **Lines**: 125–208 (proof ~78)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem abs_cardR_translate_sub_volume_le`
- **Type**: `IsBounded s → MeasurableSet s → (∀ j, LipschitzWith M (φ j)) → frontier s ⊆ ⋃ j, φ j '' Icc 0 1 → (w) → 1 ≤ c → |#(s ∩ c⁻¹•(w +ᵥ Λ)) − vol(s)·c^d| ≤ (m·(2⌈M⌉₊+1)^d·3^{d−1})·c^{d−1}`
- **What**: Translate-uniform real-scale lattice-point count with explicit constant: points of `c⁻¹•(w +ᵥ ℤ^ι)` in `s` approximate `vol(s)·c^d` with `O(c^{d−1})` error, constant independent of `w`, `c`, `vol s`.
- **How**: Scaling bijection `x ↦ c•x` and translation bijection `x ↦ x − w` reduce the count to lattice points of `ℤ^ι` in `R = −w +ᵥ c•s`; apply LatticePointCount's `abs_card_inter_sub_volume_mul_pow_le` (n=1), bound boundary cells with `ncard_index1_image_smul_chart_le`, and `(⌈c⌉₊+1)^{d−1} ≤ 3^{d−1}·c^{d−1}`.
- **Hypotheses**: `s` bounded measurable with Lipschitz-cube-covered frontier; arbitrary translate `w`; `c ≥ 1`.
- **Uses from project**: `ncard_index1_image_smul_chart_le`, `isBounded_image_smul_add`
- **Used by**: `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`
- **Visibility**: private
- **Lines**: 220–307 (proof ~80)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `theorem exists_card_coset_inter_smul_sub_volume_mul_rpow_le`
- **Type**: `(T : (ι→ℝ)≃ₗ[ℝ](ι→ℝ)) → IsBounded D → MeasurableSet D → (Lipschitz cube cover of frontier D) → ∃ C, ∀ ξ t, 1 ≤ t → |#((ξ +ᵥ T''ℤ^ι) ∩ t•D) − vol D/|det T|·t^d| ≤ C·t^{d−1}`
- **What**: **The workhorse.** For a full lattice `T '' ℤ^ι` and bounded measurable region `D` with Lipschitz-covered frontier, the count of any coset `ξ + T''ℤ^ι` in `t•D` is `vol D/|det T|·t^d + O(t^{d−1})`, constant uniform in `ξ`.
- **How**: Transport by `T⁻¹`: carry `Λ` to `ℤ^ι`, scale `vol` by `|det T|⁻¹` (`Measure.addHaar_image_linearMap`, `LinearEquiv.det_symm`), compose the Lipschitz cover (`T.symm` is Lipschitz with `‖Ts‖₊`); the frontier-cover is preserved (`image_frontier`); then invoke `abs_cardR_translate_sub_volume_le`.
- **Hypotheses**: `T` linear automorphism; `D` bounded, measurable, Lipschitz-cube-covered frontier.
- **Uses from project**: `abs_cardR_translate_sub_volume_le`
- **Used by**: `exists_card_cell_sub_mul_rpow_le_explicit`
- **Visibility**: public
- **Lines**: 318–386 (proof ~59)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem natCast_algebraNorm_add_nsmul_mul`
- **Type**: `(M:ℕ) → (x y : 𝓞 K) → ((Algebra.norm ℤ (x + M·y) : ℤ) : ZMod M) = ((Algebra.norm ℤ x : ℤ) : ZMod M)`
- **What**: The algebraic norm is constant modulo `M` along the coset `x ↦ x + M·y`.
- **How**: Norm = determinant of the left-multiplication matrix in a chosen `ℤ`-basis (`Algebra.norm_eq_matrix_det`); reducing entries mod `M` kills the `M·(leftMulMatrix y)` summand (`ZMod.natCast_self`), and `det` commutes with the reduction hom.
- **Hypotheses**: none beyond number-field structure.
- **Uses from project**: []
- **Used by**: `norm_zmod_eq_of_emb_sub_mem`
- **Visibility**: private
- **Lines**: 393–404 (proof ~10)
- **Notes**: mathlib-overlap candidate — generic "norm constant mod M on a coset"; check `Algebra.norm` API.

### `private theorem norm_eq_prod_real_emb_mul_prod_complex`
- **Type**: `(y : K) → (Algebra.norm ℚ y : ℝ) = (∏ real places, embedding_of_isReal w y) · (∏ complex places, ‖w.embedding y‖²)`
- **What**: Signed product formula: rational norm factors as product of real embeddings times product of squared complex-embedding norms (the complex factor `≥ 0`, so sign is from the real embeddings).
- **How**: Casts to `ℂ`, groups `Algebra.norm_eq_prod_embeddings` over fibres of `InfinitePlace.mk` (`Finset.prod_fiberwise`); per real place its single real embedding, per complex place the conjugate pair `σ·conj σ = ‖σ‖²` (`Complex.mul_conj`, `normSq_eq_norm_sq`).
- **Hypotheses**: none beyond number-field structure.
- **Uses from project**: []
- **Used by**: `natAbs_norm_eq_neg_one_pow_mul_norm`
- **Visibility**: private
- **Lines**: 414–458 (proof ~43)
- **Notes**: long (30–50). mathlib-overlap candidate — close to existing `InfinitePlace`/`norm` product formulas; verify.

### `private theorem prod_eq_neg_one_pow_card_mul_prod_abs`
- **Type**: `(s : Finset ι) → (f : ι → R) → (∀ w∉s, 0<f w) → (∀ w∈s, f w<0) → ∏ w, f w = (−1)^{#s}·∏ w, |f w|` (`R` linear ordered comm ring)
- **What**: A product of reals with a prescribed sign pattern equals `(−1)^{#negatives}` times the product of absolute values.
- **How**: Split the product over `s` and `sᶜ` (`Finset.prod_mul_prod_compl`), rewrite `(−1)^{#s}` as a product of `−1`s, and combine factor-by-factor with `abs_of_neg`/`abs_of_pos`.
- **Hypotheses**: `f` strictly negative on `s`, strictly positive off `s`.
- **Uses from project**: []
- **Used by**: `natAbs_norm_eq_neg_one_pow_mul_norm`
- **Visibility**: private
- **Lines**: 462–472 (proof ~9)
- **Notes**: mathlib-overlap candidate — fully generic `Finset.prod` sign identity; likely belongs in `Mathlib.Algebra.BigOperators` if not already there.

### `private theorem natAbs_norm_eq_neg_one_pow_mul_norm`
- **Type**: `(y : 𝓞 K) → (s : Finset {w//IsReal w}) → (real coords of mixedEmbedding y neg on s, pos off s) → ((Algebra.norm ℤ y).natAbs : ℤ) = (−1)^{#s}·(Algebra.norm ℤ y)`
- **What**: On a sign-orthant, the absolute integer norm equals a signed (coset-constant) residue `(−1)^{#s}·Norm`.
- **How**: Combine `norm_eq_prod_real_emb_mul_prod_complex` (sign of norm = product of real-embedding signs) with `prod_eq_neg_one_pow_card_mul_prod_abs`; identify real coords with `mixedEmbedding` real components (`mixedEmbedding_apply_isReal`); cancel `(−1)^{2#s}`.
- **Hypotheses**: real coordinates of `mixedEmbedding K y` negative exactly on `s`.
- **Uses from project**: `norm_eq_prod_real_emb_mul_prod_complex`, `prod_eq_neg_one_pow_card_mul_prod_abs`
- **Used by**: `residue_iff_signed_on_orthant`
- **Visibility**: private
- **Lines**: 479–517 (proof ~37)
- **Notes**: long (30–50)

### `private theorem card_norm_le_residue_eq_sum_class`
- **Type**: `(c)[NeZero c] → (a : ZMod c) → (N) → #{I : norm ≤ N ∧ norm ≡ a} = ∑_{C : ClassGroup} #{I : (norm ≤ N ∧ norm ≡ a) ∧ mk0 I = C}`
- **What**: The residue-restricted ideal count splits as a finite sum over the class group of per-class counts.
- **How**: Class group is `Fintype`; each fibre finite via `Ideal.finite_setOf_absNorm_le₀`; bundle as `Fintype.card_sigma` and use `Equiv.sigmaFiberEquiv` (fibre over `ClassGroup.mk0`).
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: []
- **Used by**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `tendsto_cardNormLeResidue_div_eq_sum_class`
- **Visibility**: private
- **Lines**: 524–563 (proof ~38)
- **Notes**: long (30–50)

### `private theorem natCast_eq_iff_mul_natCast_eq`
- **Type**: `(cc NJ m a : ℕ) → 0 < NJ → ((m : ZMod cc) = a) ↔ ((m·NJ : ZMod (cc·NJ)) = a·NJ)`
- **What**: `m ≡ a (mod cc)` iff `m·NJ ≡ a·NJ (mod cc·NJ)` for `NJ > 0`.
- **How**: Unfold to `Nat.ModEq` both sides, apply `Nat.mul_mod_mul_right`, and cancel `NJ` (`Nat.eq_of_mul_eq_mul_right`).
- **Hypotheses**: `NJ > 0`.
- **Uses from project**: []
- **Used by**: `principalize_iff`
- **Visibility**: private
- **Lines**: 568–573 (proof ~3)
- **Notes**: mathlib-overlap candidate — elementary `ZMod`/`Nat.ModEq` scaling; check `ZMod` API.

### `private theorem principalize_iff`
- **Type**: `... (hJ : mk0 J = C⁻¹) → 0 < N(J) → ((N(I) ≤ N ∧ N(I) ≡ a) ∧ mk0 I = C) ↔ (IsPrincipal (J·I) ∧ N(J·I) ≤ N·N(J) ∧ N(J·I) ≡ a.val·N(J) [mod c·N(J)])`
- **What**: Per-ideal principalization correspondence under `I ↦ J·I`: class-`C` residue-`a` norm-`≤N` ⟺ `J·I` principal, norm `≤ N·N(J)`, residue `a·N(J)`.
- **How**: Norm scales by `N(J)` (`map_mul`); `IsPrincipal (J·I) ↔ mk0 I = C` via `mk0_eq_one_iff` and `mk0(J·I)=C⁻¹·mk0 I`; residue transports by `natCast_eq_iff_mul_natCast_eq`; norm bound by `Nat.mul_le_mul_right_iff`.
- **Hypotheses**: `mk0 J = C⁻¹`; `N(J) > 0`.
- **Uses from project**: `natCast_eq_iff_mul_natCast_eq`
- **Used by**: `card_principalize`, `card_principalize_dvd`
- **Visibility**: private
- **Lines**: 581–620 (proof ~28)
- **Notes**: none

### `private theorem card_principalize`
- **Type**: `... (hJ : mk0 J = C⁻¹) → 0 < N(J) → #{class-C, res a, norm ≤ N} = #{J ∣ I, IsPrincipal I, norm ≤ N·N(J), res a·N(J) mod c·N(J)}`
- **What**: `Nat.card`-level principalization: the class-`C` residue count equals the count of `J`-divisible principal ideals with scaled norm/residue.
- **How**: Bijection `Equiv.dvd J` with predicate transport `principalize_iff` and `nonZeroDivisors_dvd_iff_dvd_coe`; `Equiv.subtypeSubtypeEquivSubtypeInter`.
- **Hypotheses**: `mk0 J = C⁻¹`; `N(J) > 0`.
- **Uses from project**: `principalize_iff`
- **Used by**: `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`, `card_principalize_dvd`
- **Visibility**: private
- **Lines**: 627–642 (proof ~14)
- **Notes**: none

### `private theorem map_span_int_linearEquiv`
- **Type**: `(f : E ≃ₗ[ℝ] F) → (S : Set E) → f '' (span ℤ S) = span ℤ (f '' S)` (as sets)
- **What**: An `ℝ`-linear equivalence carries the `ℤ`-span of a set to the `ℤ`-span of its image.
- **How**: `Submodule.map_span` applied to `f.restrictScalars ℤ`, then `congrArg SetLike.coe`.
- **Hypotheses**: `f` `ℝ`-linear equiv.
- **Uses from project**: []
- **Used by**: `exists_latticeEquiv_image_idealLattice`, `span_image_basisFun_eq`, `chart_lattice_eq_map`, `smul_chart_lattice_eq`, `exists_card_fibre_dvd_eq_card_cell` (indirectly), etc.
- **Visibility**: private
- **Lines**: 646–649 (proof ~3)
- **Notes**: mathlib-overlap candidate — generic; near `Submodule.map_span` / `Set.image` span lemmas.

### `private theorem cone_normLe_eq_smul_normLeOne`
- **Type**: `1 ≤ t → {x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ t^d} = t • normLeOne K`
- **What**: The norm-`≤ t^d` slice of the fundamental cone is the real dilation `t • normLeOne K`.
- **How**: Cone is scale-stable (`smul_mem_iff_mem`); norm scales by `t^d` (`mixedEmbedding.norm_smul`, `|t|=t`); explicit two-way set membership.
- **Hypotheses**: `t ≥ 1`.
- **Uses from project**: []
- **Used by**: `mem_smul_cell_iff_norm_le_and_filter_eq`
- **Visibility**: private
- **Lines**: 656–677 (proof ~21)
- **Notes**: none

### `private theorem exists_latticeEquiv_image_idealLattice`
- **Type**: `(J) → ∃ T : (index K→ℝ)≃ₗ[ℝ](index K→ℝ), T '' ℤ^{index K} = Φ '' (idealLattice K (mk0 K J))` (`Φ = (stdBasis K).equivFunL`)
- **What**: Transporting the ideal lattice along the chart `Φ` yields a full lattice `T '' ℤ^ι` for an explicit linear automorphism `T`.
- **How**: Build basis `c = (fractionalIdealLatticeBasis).map Φ` reindexed to `index K` (cardinality match via `fractionalIdeal_rank`/`finrank`); `T := (basisFun).equiv c`; then `T '' ℤ^ι = span ℤ (range c) = Φ '' (span ℤ idealLatticeBasis)` (`map_span_int_linearEquiv`, `span_idealLatticeBasis`).
- **Hypotheses**: `J` nonzero (in `(Ideal 𝓞K)⁰`).
- **Uses from project**: `map_span_int_linearEquiv`
- **Used by**: `exists_card_idealSet_residue_le`, `exists_card_idealSet_residue_real_le_dvd`
- **Visibility**: private
- **Lines**: 687–714 (proof ~27)
- **Notes**: none

### `private theorem exists_lipschitz_cube_cover_hyperplane_slab`
- **Type**: `(j : ι) → 0 ≤ R → ∃ M φ, LipschitzWith M φ ∧ {x : x j = 0 ∧ ∀ i,|x i|≤R} ⊆ φ '' Icc 0 1`
- **What**: A bounded slab of a coordinate hyperplane `{x j = 0}` is covered by a single Lipschitz image of the unit cube.
- **How**: Parametrise the `card ι − 1` free coordinates affinely `c ↦ 2R·c − R` (bijection `Fin(card ι−1) ≃ {i//i≠j}`), set coord `j` to `0`; Lipschitz constant `2R`; handle `R=0` degenerately.
- **Hypotheses**: `R ≥ 0`.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`
- **Visibility**: private
- **Lines**: 722–765 (proof ~43)
- **Notes**: long (30–50)

### `private theorem exists_lipschitz_cover_union`
- **Type**: `(A B) → (cover A) → (cover B) → cover (A ∪ B)`
- **What**: Union of two Lipschitz-cube-covered sets is Lipschitz-cube-covered.
- **How**: Concatenate the two families over `Fin (m1+m2)` via `finSumFinEquiv`/`Sum.elim`, take `max` of constants (`LipschitzWith.weaken`).
- **Hypotheses**: both `A`, `B` covered.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`
- **Visibility**: private
- **Lines**: 770–791 (proof ~21)
- **Notes**: none

### `private theorem exists_lipschitz_cover_iUnion`
- **Type**: `[Finite γ] → (A : γ → Set) → (∀ g, cover (A g)) → cover (⋃ g, A g)`
- **What**: A finite-indexed union of Lipschitz-cube-covered sets is covered.
- **How**: `choose` the per-`g` data; concatenate over `Σ g, Fin (mf g)` via `Fintype.equivFin`, take `Finset.sup` of constants.
- **Hypotheses**: `γ` finite; each `A g` covered.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`
- **Visibility**: private
- **Lines**: 796–813 (proof ~17)
- **Notes**: none

### `private theorem frontier_signOrthant_subset`
- **Type**: `[Finite κ] → (g : κ → ι) → (s : Finset κ) → frontier {y : (∀k∈s, y(g k)≤0) ∧ (∀k∉s, 0≤y(g k))} ⊆ ⋃ k, {y : y(g k)=0}`
- **What**: The frontier of a closed sign-orthant lies in the union of the relevant coordinate hyperplanes.
- **How**: Orthant closed; strict version open and contained; a boundary point is in the orthant but not its interior (`interior_eq_compl_closure_compl`), forcing some `y(g k)=0` (else it would lie in the open strict orthant).
- **Hypotheses**: `κ` finite.
- **Uses from project**: []
- **Used by**: `exists_frontier_cover_inter_orthant`
- **Visibility**: private
- **Lines**: 819–846 (proof ~27)
- **Notes**: none

### `private theorem exists_frontier_cover_inter_orthant`
- **Type**: `(g)(s)(D₀) → IsBounded D₀ → (cover frontier D₀) → cover (frontier (D₀ ∩ orthant))`
- **What**: Intersecting a bounded Lipschitz-frontier-covered region with a sign-orthant keeps a Lipschitz-cube-covered frontier.
- **How**: `frontier (D₀∩O) ⊆ frontier D₀ ∪ (closure D₀ ∩ frontier O)` (`frontier_inter_subset`); orthant boundary in coordinate hyperplanes (`frontier_signOrthant_subset`), each bounded slice covered (`exists_lipschitz_cube_cover_hyperplane_slab`); combine with `exists_lipschitz_cover_union` / `exists_lipschitz_cover_iUnion`.
- **Hypotheses**: `D₀` bounded with covered frontier.
- **Uses from project**: `exists_lipschitz_cube_cover_hyperplane_slab`, `exists_lipschitz_cover_union`, `exists_lipschitz_cover_iUnion`, `frontier_signOrthant_subset`
- **Used by**: `exists_card_cell_sub_mul_rpow_le_explicit`
- **Visibility**: private
- **Lines**: 854–883 (proof ~29)
- **Notes**: none

### `private theorem mem_span_int_basisFun_iff`
- **Type**: `[Finite ι] → (v : ι→ℝ) → v ∈ span ℤ (range (Pi.basisFun ℝ ι)) ↔ ∀ i, ∃ n:ℤ, v i = n`
- **What**: A vector lies in the standard integer lattice iff all coordinates are integers.
- **How**: `(Pi.basisFun).mem_span_iff_repr_mem` + `Pi.basisFun_repr`.
- **Hypotheses**: `ι` finite.
- **Uses from project**: []
- **Used by**: `exists_int_coord_of_mem`, `sub_mem_nsmul_of_coord_eq`, `mem_coset_iff_cos_eq`, `card_fibre_eq_card_cell`, `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 887–891 (proof ~4)
- **Notes**: mathlib-overlap candidate — generic standard-lattice membership; check `Pi.basisFun`/`Submodule.span` API.

### `private theorem card_isPrincipal_dvd_norm_le_residue`
- **Type**: `(J)(m b : ℕ)(s : ℝ) → #{J ∣ I, IsPrincipal I, N(I) ≤ s, N(I) ≡ b mod m}·torsionOrder K = #{a ∈ idealSet K J : norm a ≤ s ∧ intNorm a ≡ b}`
- **What**: Residue-decorated refinement of mathlib's `card_isPrincipal_dvd_norm_le`: the count of `J`-divisible principal ideals (norm `≤ s`, residue `b`) times the torsion order equals the residue-restricted cone-point count.
- **How**: Per-norm-value fibre equivalence `idealSetEquivNorm` (residue is a function of the norm value, rides along); `Equiv.ofFiberEquiv` over `Finset.Iic ⌊s⌋₊`; empty fibres on both sides where `i ≢ b`; `torsionOrder = card (torsion K)`.
- **Hypotheses**: none beyond number-field structure (handles `s < 0` via empties).
- **Uses from project**: []
- **Used by**: `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`, `card_isPrincipal_dvd_norm_le_residue_natBound`
- **Visibility**: private
- **Lines**: 901–962 (proof ~55)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem exists_card_cell_sub_mul_rpow_le_explicit`
- **Type**: `(T)(m)(hm)(D₀ bounded measurable, cover)(g)(s) → ∃ C, ∀ ξ t, 1≤t → |#((ξ +ᵥ ((m·)∘T)''ℤ^ι) ∩ t•(D₀∩orthant)) − vol(D₀∩orthant)/|det((m·)∘T)|·t^d| ≤ C·t^{d−1}`
- **What**: Per-cell effective count (explicit constant): the workhorse specialised to the `m`-sublattice and an orthant-cut region.
- **How**: Apply `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` to `T' = (m·)∘T` and `Ds = D₀∩orthant`, with frontier cover from `exists_frontier_cover_inter_orthant`; orthant is closed (measurable).
- **Hypotheses**: `(m:ℝ) ≠ 0`; `D₀` bounded, measurable, covered.
- **Uses from project**: `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`, `exists_frontier_cover_inter_orthant`
- **Used by**: `exists_card_cell_sub_mul_rpow_le`, `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 970–1008 (proof ~22)
- **Notes**: none

### `private theorem exists_card_cell_sub_mul_rpow_le`
- **Type**: `(T)(m)(hm)(D₀ …)(g)(s) → ∃ leadC C, ∀ ξ t, 1≤t → |#(... ) − leadC·t^d| ≤ C·t^{d−1}`
- **What**: Implicit-constant form of the per-cell count.
- **How**: Re-bind the explicit constant of `exists_card_cell_sub_mul_rpow_le_explicit` as `leadC = vol(Ds)/|det((m·)∘T)|`.
- **Hypotheses**: as above.
- **Uses from project**: `exists_card_cell_sub_mul_rpow_le_explicit`
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 1013–1030 (proof ~5)
- **Notes**: UNUSED in file — only the `_explicit` form is consumed downstream.

### `private theorem exists_int_coord_of_mem`
- **Type**: `(J)(T)(hT)(x ∈ idealLattice K (mk0 K J))(i) → ∃ n:ℤ, (T.symm (Φ x)) i = n`
- **What**: The chart-`T` integer coordinates of an ideal-lattice point are integers.
- **How**: `Φ x ∈ T '' ℤ^ι` (from `hT`), so `T.symm (Φ x) ∈ ℤ^ι`; apply `mem_span_int_basisFun_iff`.
- **Hypotheses**: `hT` identifies the chart lattice; `x` in the ideal lattice.
- **Uses from project**: `mem_span_int_basisFun_iff`
- **Used by**: `sub_mem_nsmul_of_coord_eq`, `mem_coset_iff_cos_eq`
- **Visibility**: private
- **Lines**: 1038–1053 (proof ~15)
- **Notes**: none

### `private theorem sub_mem_nsmul_of_coord_eq`
- **Type**: `(m)(J)(T)(hT)(x₁,x₂ in idealLattice)(coords equal mod m) → x₁ − x₂ ∈ (m:ℝ)•idealLattice`
- **What**: Two ideal-lattice points with equal reduced integer coordinates mod `m` differ by an element of the `m`-sublattice.
- **How**: Integer coords differ by `m·p` (`round_intCast`, `ZMod.intCast_zmod_eq_zero_iff_dvd`); the difference `T.symm(Φ x₁)−T.symm(Φ x₂) = m•p` with `p ∈ ℤ^ι`; pull back through `T`, `Φ` injective.
- **Hypotheses**: both in ideal lattice; coordinates agree mod `m`.
- **Uses from project**: `exists_int_coord_of_mem`, `mem_span_int_basisFun_iff`
- **Used by**: `residue_fibre_const_aux`
- **Visibility**: private
- **Lines**: 1059–1104 (proof ~44)
- **Notes**: long (30–50)

### `private theorem norm_zmod_eq_of_emb_sub_mem`
- **Type**: `(m)(J)(x y : 𝓞 K) → (mixedEmbedding x − mixedEmbedding y ∈ (m:ℝ)•idealLattice) → ((norm ℤ x):ZMod m) = (norm ℤ y)`
- **What**: If mixed embeddings of `x,y` differ by an `m`-sublattice vector, their algebraic norms agree mod `m`.
- **How**: Unfold sublattice membership to `x − y = m·w` for `w ∈ 𝓞 K` (`mem_idealLattice`, `mixedEmbedding_injective`, `RingOfIntegers.coe_injective`), then `natCast_algebraNorm_add_nsmul_mul`.
- **Hypotheses**: embedding difference in `m`-sublattice.
- **Uses from project**: `natCast_algebraNorm_add_nsmul_mul`
- **Used by**: `residue_fibre_const_aux`
- **Visibility**: private
- **Lines**: 1112–1134 (proof ~22)
- **Notes**: none

### `private theorem mixedEmbedding_preimageOfMemIntegerSet_idealSetMap`
- **Type**: `(J)(a : idealSet K J) → mixedEmbedding K (preimageOfMemIntegerSet (idealSetMap K J a) : K) = (a : mixedSpace K)`
- **What**: The mixed embedding of the integer generator attached to a cone point `a` is `a` itself.
- **How**: `mixedEmbedding_preimageOfMemIntegerSet` + `idealSetMap_apply`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `residue_iff_signed_on_orthant`, `residue_fibre_const_aux`
- **Visibility**: private
- **Lines**: 1137–1141 (proof ~2)
- **Notes**: none

### `private theorem residue_iff_signed_on_orthant`
- **Type**: `(m b)(J)(a)(s)(real coords of a neg on s, pos off s) → (intNorm a ≡ b mod m) ↔ ((−1)^{#s}·norm ℤ gen_a ≡ b mod m)`
- **What**: On an orthant the absolute norm-residue condition becomes the signed residue condition.
- **How**: `intNorm a = |norm ℤ gen_a|`; apply `natAbs_norm_eq_neg_one_pow_mul_norm` (via `mixedEmbedding ... = a`) and cast.
- **Hypotheses**: sign pattern `s` on the real coords of `a`.
- **Uses from project**: `natAbs_norm_eq_neg_one_pow_mul_norm`, `mixedEmbedding_preimageOfMemIntegerSet_idealSetMap`
- **Used by**: `residue_fibre_const_aux`
- **Visibility**: private
- **Lines**: 1148–1165 (proof ~14)
- **Notes**: none

### `private theorem mem_coset_iff_cos_eq`
- **Type**: `(m)[NeZero m](hm)(J)(T)(hT)(k)(x ∈ idealLattice) → (Φ x ∈ T k' +ᵥ ((m·)∘T)''ℤ^ι) ↔ (∀ i, round((T.symm (Φ x)) i) ≡ k i mod m)`
- **What**: A lattice point's chart image lies in the `m`-coset indexed by `k` iff its reduced integer coordinates equal `k` mod `m`.
- **How**: Integer coords `n` (via `exists_int_coord_of_mem`, `round_intCast`); divisibility `m ∣ n−k.val` ⟺ membership; unfold the affine coset through `T` and `(m·)`.
- **Hypotheses**: `m ≠ 0`, `x` in ideal lattice.
- **Uses from project**: `exists_int_coord_of_mem`, `mem_span_int_basisFun_iff`
- **Used by**: `card_fibre_eq_card_cell`, `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 1173–1224 (proof ~50)
- **Notes**: long (30–50). Contains `lia` tactic at line 1224 (Lean lia, fine).

### `private theorem realComponent_ne_zero_of_mem_fundamentalCone`
- **Type**: `(x ∈ fundamentalCone K)(w : {w//IsReal w}) → x.1 w ≠ 0`
- **What**: Real components of a fundamental-cone point are nonzero.
- **How**: `fundamentalCone.normAtPlace_pos_of_mem` + `normAtPlace_apply_of_isReal`.
- **Hypotheses**: `x` in the fundamental cone.
- **Uses from project**: []
- **Used by**: `mem_smul_cell_iff_norm_le_and_filter_eq`, `residue_fibre_const_aux`
- **Visibility**: private
- **Lines**: 1228–1233 (proof ~5)
- **Notes**: none

### `private theorem mem_smul_cell_iff_norm_le_and_filter_eq`
- **Type**: `(J)(s)(1≤t)(x ∈ idealSet K J) → (Φ x ∈ t•(Φ''normLeOne ∩ orthant_s)) ↔ (norm x ≤ t^d ∧ filter (x.1 w < 0) = s)`
- **What**: Chart image of a cone point lies in the dilated orthant cell iff norm `≤ t^d` and the negative real coordinates are exactly `s`.
- **How**: Cone homogeneity `cone_normLe_eq_smul_normLeOne`; `Φ`-linearity; real coords of `Φ x` are `x.1` (`stdBasis_apply_isReal`); nonvanishing (`realComponent_ne_zero_of_mem_fundamentalCone`); sign bookkeeping with `nlinarith`.
- **Hypotheses**: `t ≥ 1`, `x ∈ idealSet K J`.
- **Uses from project**: `cone_normLe_eq_smul_normLeOne`, `realComponent_ne_zero_of_mem_fundamentalCone`
- **Used by**: `card_fibre_eq_card_cell`, `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 1242–1302 (proof ~52)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem mem_idealSet_of_chart_mem_smul_cell`
- **Type**: `(I)(t≠0)(z ∈ idealLattice, Φ z = y, y ∈ t•(Φ''normLeOne ∩ Os)) → z ∈ idealSet K I`
- **What**: If a lattice point's chart lies in the dilated cell, the point is a cone point of `idealSet K I`.
- **How**: Extract `z ∈ t•normLeOne` from the region (`Set.smul_set_inter₀`, `image_smul_comm`), then cone homogeneity (`smul_mem_of_mem`) gives fundamental-cone membership.
- **Hypotheses**: `t ≠ 0`; `z` in ideal lattice; chart in cell.
- **Uses from project**: []
- **Used by**: `card_fibre_eq_card_cell`, `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 1309–1326 (proof ~17)
- **Notes**: none

### `private theorem card_fibre_eq_card_cell`
- **Type**: `(m)[NeZero m](hm)(J)(T)(hT)(s)(k)(1≤t) → #{a∈idealSet K J : norm ≤ t^d ∧ filter=s ∧ coset=k} = #((T k' +ᵥ ((m·)∘T)''ℤ^ι) ∩ t•(Φ''normLeOne ∩ orthant_s))`
- **What**: Cone points (norm `≤ t^d`, orthant `s`, coset `k`) biject with lattice points of the coset in the dilated orthant cell.
- **How**: Injection `f = Φ∘(·)`; characterise its range as the cell intersection using `mem_coset_iff_cos_eq` (coset side) and `mem_smul_cell_iff_norm_le_and_filter_eq` (region side); back direction via `mem_idealSet_of_chart_mem_smul_cell`; `Nat.card_range_of_injective`.
- **Hypotheses**: `m ≠ 0`, `t ≥ 1`, `hT` chart identity.
- **Uses from project**: `mem_coset_iff_cos_eq`, `mem_smul_cell_iff_norm_le_and_filter_eq`, `mem_idealSet_of_chart_mem_smul_cell`, `mem_span_int_basisFun_iff`
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le_explicit`
- **Visibility**: private
- **Lines**: 1336–1403 (proof ~49)
- **Notes**: long (30–50)

### `private theorem residue_fibre_const_aux`
- **Type**: `(m b)(J)(T)(hT)(s)(k)(a a' : idealSet K J)(same orthant s, same coset k) → ((intNorm a ≡ b) ↔ (intNorm a' ≡ b))`
- **What**: Constancy step: two cone points sharing orthant `s` and `m`-coset `k` carry the same norm-residue.
- **How**: Both reduce to the signed residue (`residue_iff_signed_on_orthant`); their generators have equal norm mod `m` because their embeddings differ by an `m`-sublattice vector (`sub_mem_nsmul_of_coord_eq` from equal coords) so `norm_zmod_eq_of_emb_sub_mem` applies.
- **Hypotheses**: same orthant and coset.
- **Uses from project**: `residue_iff_signed_on_orthant`, `realComponent_ne_zero_of_mem_fundamentalCone`, `norm_zmod_eq_of_emb_sub_mem`, `sub_mem_nsmul_of_coord_eq`, `mixedEmbedding_preimageOfMemIntegerSet_idealSetMap`
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 1410–1456 (proof ~46)
- **Notes**: long (30–50)

### `private theorem exists_card_residue_fibre_sub_mul_rpow_le_explicit`
- **Type**: `(m)[NeZero m](hm)(b)(J)(T)(hT)(hcov)(s)(k) → ∃ C, ∀ t≥1, |#{a : norm ≤ t^d ∧ res b ∧ orthant s ∧ coset k} − (if cell-realizes-b then vol(Φ''normLeOne ∩ orthant)/|det((m·)∘T)| else 0)·t^d| ≤ C·t^{d−1}`
- **What**: Per-(orthant, coset) effective residue count with explicit leading constant.
- **How**: Case on whether the cell realizes residue `b`; if so drop the residue filter (constancy via `residue_fibre_const_aux`) and apply `card_fibre_eq_card_cell` then the cell estimate `exists_card_cell_sub_mul_rpow_le_explicit`; else the set is empty.
- **Hypotheses**: `m ≠ 0`; `hcov` frontier cover of `Φ''normLeOne`.
- **Uses from project**: `exists_card_cell_sub_mul_rpow_le_explicit`, `card_fibre_eq_card_cell`, `residue_fibre_const_aux`
- **Used by**: `exists_card_residue_fibre_sub_mul_rpow_le`, `exists_card_idealSet_residue_real_le_dvd`
- **Visibility**: private
- **Lines**: 1463–1551 (proof ~58)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem exists_card_residue_fibre_sub_mul_rpow_le`
- **Type**: `(m)[NeZero m](hm)(b)(J)(T)(hT)(hcov)(s)(k) → ∃ L C, ∀ t≥1, |#{...} − L·t^d| ≤ C·t^{d−1}`
- **What**: Implicit-constant per-(orthant, coset) effective residue count.
- **How**: Re-bind the explicit constant of `exists_card_residue_fibre_sub_mul_rpow_le_explicit`.
- **Hypotheses**: as above.
- **Uses from project**: `exists_card_residue_fibre_sub_mul_rpow_le_explicit`
- **Used by**: `exists_card_idealSet_residue_le`
- **Visibility**: private
- **Lines**: 1559–1590 (proof ~12)
- **Notes**: none

### `private theorem finite_idealSet_norm_le`
- **Type**: `(J)(s : ℝ) → Finite {a ∈ idealSet K J : norm a ≤ s}`
- **What**: Bounded-norm cone points form a finite set.
- **How**: Inject (via `integerSetEquiv ∘ idealSetMap`) into the product of {ideals of norm `≤ ⌊s⌋` (`Ideal.finite_setOf_absNorm_le₀`)} × torsion group; injectivity from `integerSetEquiv`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `card_idealSet_residue_eq_sum_cell`
- **Visibility**: private
- **Lines**: 1597–1619 (proof ~22)
- **Notes**: none

### `private theorem card_idealSet_residue_eq_sum_cell`
- **Type**: `(m)[NeZero m](b)(I₀)(Tc)(S : ℝ) → #{a : norm ≤ S ∧ res b} = ∑_{p : Finset{real}×(index→ZMod m)} #{a : (norm ≤ S ∧ res b) ∧ orthant=p.1 ∧ coset=p.2}`
- **What**: The cone-point residue count partitions over `(orthant, coset)` cells.
- **How**: Fibre over the classifier `cls = (filter neg, reduced coords mod m)`; finiteness from `finite_idealSet_norm_le`; `Equiv.sigmaFiberEquiv`, `Nat.card_sigma`.
- **Hypotheses**: none beyond `NeZero m`.
- **Uses from project**: `finite_idealSet_norm_le`
- **Used by**: `card_residue_sum_bound_aux`
- **Visibility**: private
- **Lines**: 1625–1669 (proof ~30)
- **Notes**: long (30–50)

### `private theorem card_residue_sum_bound_aux`
- **Type**: `(m)[NeZero m](b)(I₀)(Tc)(S)(1≤S)(Lc Cc : cells→ℝ)(per-cell estimates at tN=S^{1/d}) → |#{a: norm ≤ S ∧ res b} − (∑ Lc)·S| ≤ (∑ Cc)·S^{1−1/d}`
- **What**: Summing step: per-cell effective estimates at `tN = S^{1/d}` give the global cone-residue estimate.
- **How**: `card_idealSet_residue_eq_sum_cell`; substitute `tN^d = S`, `tN^{d−1} = S^{1−1/d}` (`Real.rpow` algebra); triangle inequality over the finite cell partition.
- **Hypotheses**: `S ≥ 1`; per-cell bounds.
- **Uses from project**: `card_idealSet_residue_eq_sum_cell`
- **Used by**: `exists_card_idealSet_residue_le`, `exists_card_idealSet_residue_real_le_dvd`
- **Visibility**: private
- **Lines**: 1676–1719 (proof ~43)
- **Notes**: long (30–50)

### `private theorem exists_card_idealSet_residue_le`
- **Type**: `(m)[NeZero m](b)(J) → ∃ κ C', ∀ N≥1, |#{a∈idealSet K J : norm ≤ N·N(J) ∧ intNorm a ≡ b mod m} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: **The Widmer/GRS geometric core**: effective cone-point count with a norm-residue condition, `κ·N + O(N^{1−1/d})`.
- **How**: Get chart `T` (`exists_latticeEquiv_image_idealLattice`) and frontier cover (`normLeOne_frontier_lipschitz_cover_index`); `choose` per-cell estimates (`exists_card_residue_fibre_sub_mul_rpow_le`); apply `card_residue_sum_bound_aux` at `S = N·N(J)`; rescale `(N·NJ)^{1−1/d}` via `Real.mul_rpow`.
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: `exists_latticeEquiv_image_idealLattice`, `exists_card_residue_fibre_sub_mul_rpow_le`, `card_residue_sum_bound_aux` (+ siblings `normLeOne_frontier_lipschitz_cover_index`)
- **Used by**: `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 1745–1775 (proof ~30)
- **Notes**: long (30–50)

### `private theorem exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`
- **Type**: `(m)[NeZero m](b)(J) → ∃ κ C', ∀ N≥1, |#{J ∣ I, IsPrincipal I, N(I) ≤ N·N(J), N(I)≡b mod m} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: Effective count of `J`-divisible principal ideals with a norm residue.
- **How**: Torsion bridge `card_isPrincipal_dvd_norm_le_residue` at `s = N·N(J)` equates ideal count × `torsionOrder K` with the cone-point count; divide the cone-point estimate (`exists_card_idealSet_residue_le`) by the nonzero torsion order.
- **Hypotheses**: `m ≠ 0`.
- **Uses from project**: `exists_card_idealSet_residue_le`, `card_isPrincipal_dvd_norm_le_residue`
- **Used by**: `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 1788–1823 (proof ~27)
- **Notes**: none

### `private theorem exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`
- **Type**: `(c)[NeZero c](a : ZMod c)(C) → ∃ κ C', ∀ N≥1, |#{I : (N(I) ≤ N ∧ N(I)≡a mod c) ∧ mk0 I = C} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: Per-class effective residue count.
- **How**: Principalize to `J`-divisible principal ideals (`card_principalize`, `mk0 J = C⁻¹`); apply `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le` at modulus `c·N(J)` and residue `a.val·N(J)`.
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: `card_principalize`, `exists_card_dvd_principal_residue_eq_sub_mul_rpow_le`
- **Used by**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `exists_tendsto_cardNormLeResidueClass_div`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 1834–1850 (proof ~9)
- **Notes**: none

### `private theorem tendsto_div_atTop_of_sub_mul_rpow_le`
- **Type**: `{f : ℕ→ℝ}{κ C'}{d} → 0<d → (∀ N≥1, |f N − κ·N| ≤ C'·N^{1−1/d}) → Tendsto (fun N ↦ f N / N) atTop (nhds κ)`
- **What**: An effective estimate pins `κ` as the limit of `f N / N` (relative error `O(N^{−1/d}) → 0`).
- **How**: `tendsto_rpow_neg_atTop`; squeeze `|f N/N − κ| ≤ |C'|·N^{−1/d}` (`squeeze_zero'`, `tendsto_iff_norm_sub_tendsto_zero`).
- **Hypotheses**: `d > 0`; effective bound.
- **Uses from project**: []
- **Used by**: `exists_tendsto_cardNormLeResidue_div`, `exists_tendsto_cardNormLeResidueClass_div`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, `tendsto_count_div_of_cone_bridge`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`, `cardNormLeResidueClass_density_transfer`
- **Visibility**: private
- **Lines**: 1858–1882 (proof ~24)
- **Notes**: mathlib-overlap candidate — purely analytic (asymptotic ⟹ limit of ratio); generic, could go to `Mathlib.Analysis`.

### `theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`
- **Type**: `(K)(c)[NeZero c](a : ZMod c) → ∃ κ C', ∀ N≥1, |#{I : N(I) ≤ N ∧ N(I)≡a mod c} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: **Top-level result.** Effective ideal count by norm residue: `κ_a·N + O(N^{1−1/d})`.
- **How**: Split by ideal class (`card_norm_le_residue_eq_sum_class`); sum per-class effective counts (`exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`) and bound the total error by triangle inequality over the class group.
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: `card_norm_le_residue_eq_sum_class`, `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`
- **Used by**: `exists_tendsto_cardNormLeResidue_div`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`
- **Visibility**: public
- **Lines**: 1890–1906 (proof ~9)
- **Notes**: none

### `private def cardNormLeResidue`
- **Type**: `(K)(c : ℕ)(a : ZMod c)(N : ℕ) : ℕ := Nat.card {I : N(I) ≤ N ∧ N(I) ≡ a mod c}`
- **What**: Abbreviation for the number of nonzero integral ideals of norm `≤ N` with norm residue `a (mod c)`.
- **How**: Direct `Nat.card` of the subtype.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_eq_of_mem_subgroup`, `tendsto_cardNormLeResidue_div_eq_sum_class`, `cardNormLeResidue_density_transfer`, `cardNormLeResidue_density_const_of_realized`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`
- **Visibility**: private
- **Lines**: 1912–1915 (def, ~3)
- **Notes**: none

### `private theorem exists_tendsto_cardNormLeResidue_div`
- **Type**: `(K)(c)[NeZero c](a) → ∃ κ, Tendsto (fun N ↦ cardNormLeResidue K c a N / N) atTop (nhds κ)`
- **What**: The density `lim cardNormLeResidue/N` exists.
- **How**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le` + `tendsto_div_atTop_of_sub_mul_rpow_le`.
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `tendsto_div_atTop_of_sub_mul_rpow_le`
- **Used by**: `cardNormLeResidue_density_eq_of_mem_subgroup`, `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`, `cardNormLeResidue_density_transfer`, `cardNormLeResidue_density_const_of_realized`, `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`
- **Visibility**: private
- **Lines**: 1919–1924 (proof ~5)
- **Notes**: none

### `private theorem cardNormLeResidue_density_eq_of_mem_subgroup`
- **Type**: `{c}[NeZero c]{S}(Fourier-decay hF)(a,a'∈S)(densities κ,κ') → κ = κ'`
- **What**: Under Fourier-decay, the residue-count densities of any `a, a' ∈ S` coincide.
- **How**: `hF` says every nontrivial Fourier coefficient of `s ↦ κ_s` on `S` vanishes; `eq_of_sum_char_mul_eq_zero` (finite-abelian Fourier inversion) forces `κ_·` constant; uniqueness of limits.
- **Hypotheses**: `hF` (vanishing nontrivial-character twists).
- **Uses from project**: `exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue` (+ sibling `eq_of_sum_char_mul_eq_zero`)
- **Used by**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`
- **Visibility**: private
- **Lines**: 1932–1963 (proof ~20)
- **Notes**: none

### `theorem exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`
- **Type**: `(K)(c)[NeZero c](S)(hF) → ∃ κ C', ∀ a∈S, ∀ N≥1, |#{I : N(I)≤N ∧ N(I)≡a} − κ·N| ≤ C'·N^{1−1/d}`
- **What**: **Top-level result.** Uniform per-residue count: a single `(κ, C')` serves all `a ∈ S` simultaneously, given the Fourier-decay hypothesis.
- **How**: Per-residue leading constants are limits of `count/N` (`tendsto_div_atTop_of_sub_mul_rpow_le`), hence constant on `S` (`cardNormLeResidue_density_eq_of_mem_subgroup`); `κ` = that common value, `C'` = sum of per-residue error constants over `ZMod c`.
- **Hypotheses**: `c ≠ 0`; `hF`.
- **Uses from project**: `exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`, `exists_tendsto_cardNormLeResidue_div`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `cardNormLeResidue_density_eq_of_mem_subgroup`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 1973–2000 (proof ~14)
- **Notes**: none (terminal consumer — exported API)

### `private def cardNormLeResidueClass`
- **Type**: `(c)(y : ZMod c)(C : ClassGroup)(N) : ℕ := Nat.card {I : (N(I) ≤ N ∧ N(I)≡y) ∧ mk0 I = C}`
- **What**: Per-class norm-residue count.
- **How**: Direct `Nat.card`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `exists_tendsto_cardNormLeResidueClass_div`, `tendsto_cardNormLeResidue_div_eq_sum_class`, `cardNormLeResidueClass_eq_dvd`, `card_principalize_dvd`, `cardNormLeResidueClassDvd_div_density`, `cardNormLeResidueClassDvd_eq_div`, `cardNormLeResidueClassDvd_div_density_routeA`, `tendsto_cardNormLeResidueClass_div_transfer`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`, `cardNormLeResidueClass_density_transfer`, `cardNormLeResidue_density_transfer`
- **Visibility**: private
- **Lines**: 2030–2033 (def, ~3)
- **Notes**: none

### `private theorem exists_tendsto_cardNormLeResidueClass_div`
- **Type**: `(c)[NeZero c](y)(C) → ∃ κ, Tendsto (fun N ↦ cardNormLeResidueClass c y C N / N) atTop (nhds κ)`
- **What**: The per-class density `κ_{C,y}` exists.
- **How**: `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le` + `tendsto_div_atTop_of_sub_mul_rpow_le`.
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`, `tendsto_div_atTop_of_sub_mul_rpow_le`
- **Used by**: `tendsto_cardNormLeResidueClass_div_transfer`, `cardNormLeResidue_density_transfer`
- **Visibility**: private
- **Lines**: 2038–2043 (proof ~5)
- **Notes**: none

### `private theorem tendsto_cardNormLeResidue_div_eq_sum_class`
- **Type**: `(c)[NeZero c](y){κ}(hκ density)(κf)(hκf per-class densities) → κ = ∑_C κf C`
- **What**: The norm-residue density splits over the class group: `κ_y = ∑_C κ_{C,y}`.
- **How**: `cardNormLeResidue = ∑_C cardNormLeResidueClass` (`card_norm_le_residue_eq_sum_class`); pass to limits (`tendsto_finsetSum`, uniqueness).
- **Hypotheses**: `c ≠ 0`; both densities given.
- **Uses from project**: `cardNormLeResidue`, `card_norm_le_residue_eq_sum_class`, `cardNormLeResidueClass`
- **Used by**: `cardNormLeResidue_density_transfer`
- **Visibility**: private
- **Lines**: 2049–2061 (proof ~5)
- **Notes**: none

### `private def cardNormLeResidueClassDvd`
- **Type**: `(c)(𝔟)(y : ZMod c)(D : ClassGroup)(N) : ℕ := Nat.card {J : 𝔟 ∣ J ∧ ((N(J) ≤ N ∧ N(J)≡y) ∧ mk0 J = D)}`
- **What**: `𝔟`-divisible per-class norm-residue count.
- **How**: Direct `Nat.card`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `cardNormLeResidueClass_eq_dvd`, `cardNormLeResidueClassDvd_floor_collapse`, `card_principalize_dvd`, `cardNormLeResidueClassDvd_div_density`, `cardNormLeResidueClassDvd_eq_div`, `cardNormLeResidueClassDvd_div_density_routeA`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`, `cardNormLeResidueClass_density_transfer`
- **Visibility**: private
- **Lines**: 2066–2070 (def, ~4)
- **Notes**: none

### `private theorem cardNormLeResidueClass_eq_dvd`
- **Type**: `(c)[NeZero c](𝔟)(hu : IsUnit (N(𝔟) mod c))(x)(C)(N) → cardNormLeResidueClass c x C N = cardNormLeResidueClassDvd c 𝔟 (x·N(𝔟)) (C·[𝔟]) (N·N(𝔟))`
- **What**: **Route A** (exact bijection): `I ↦ 𝔟·I` carries class-`C` residue-`x` norm-`≤N` ideals onto `𝔟`-divisible class-`C·[𝔟]` residue-`x·N(𝔟)` norm-`≤N·N(𝔟)` ideals.
- **How**: `Equiv.dvd 𝔟`; norm scales by `N(𝔟)`, class by `[𝔟]`, residue transports (unit `hu.mul_left_inj`), `𝔟 ∣ 𝔟·I` automatic; `Equiv.subtypeSubtypeEquivSubtypeInter`.
- **Hypotheses**: `N(𝔟) mod c` a unit.
- **Uses from project**: `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`
- **Used by**: `cardNormLeResidueClassDvd_eq_div`, `cardNormLeResidueClass_density_transfer`
- **Visibility**: private
- **Lines**: 2077–2108 (proof ~24)
- **Notes**: none

### `private theorem Nat.le_iff_le_mul_div_of_dvd`
- **Type**: `{a m : ℕ} → 0<m → m ∣ a → (N) → a ≤ N ↔ a ≤ m·(N/m)`
- **What**: For a multiple `a` of `m`, `a ≤ N` iff `a ≤ m·⌊N/m⌋`.
- **How**: Write `a = m·k`; `Nat.le_div_iff_mul_le`, `Nat.mul_div_le`.
- **Hypotheses**: `m > 0`, `m ∣ a`.
- **Uses from project**: []
- **Used by**: `cardNormLeResidueClassDvd_floor_collapse`
- **Visibility**: private (declared in `Nat` namespace — see Notes)
- **Lines**: 2112–2116 (proof ~4)
- **Notes**: mathlib-overlap candidate — generic `Nat` divisibility/floor lemma; also **namespaced into `Nat.`** which for a ForMathlib decl risks clobbering — flag for naming review.

### `private theorem cardNormLeResidueClassDvd_floor_collapse`
- **Type**: `(c)[NeZero c](𝔟)(y)(D)(N) → cardNormLeResidueClassDvd c 𝔟 y D N = cardNormLeResidueClassDvd c 𝔟 y D (N(𝔟)·⌊N/N(𝔟)⌋)`
- **What**: Norm-window collapse: a `𝔟`-divisible count at bound `N` equals the one at the largest multiple of `N(𝔟)` below `N` (every `𝔟`-divisible norm is a multiple of `N(𝔟)`).
- **How**: `Equiv.subtypeEquivRight` rewriting the bound via `Nat.le_iff_le_mul_div_of_dvd` (with `N(𝔟) ∣ N(J)` from `map_dvd absNorm`).
- **Hypotheses**: `c ≠ 0`.
- **Uses from project**: `cardNormLeResidueClassDvd`, `Nat.le_iff_le_mul_div_of_dvd`
- **Used by**: `cardNormLeResidueClassDvd_eq_div`
- **Visibility**: private
- **Lines**: 2123–2134 (proof ~8)
- **Notes**: none

### `private theorem absNorm_coprime_of_isCoprime_span`
- **Type**: `(J)(n : ℕ) → IsCoprime (J : Ideal) (span {(n:𝓞K)}) → (N(J)).Coprime n`
- **What**: Ideal-coprimality of `J` to `(n)` implies `gcd(N(J), n) = 1`.
- **How**: A prime `p ∣ gcd(N(J),n)` gives a maximal `P ∣ J` over `(p)` (`exists_isMaximal_dvd_of_dvd_absNorm'`); then `(n) ∈ P`, so `J ⊔ (n) ≤ P ≠ ⊤`, contradicting `isCoprime_iff_sup_eq`.
- **Hypotheses**: ideal coprimality.
- **Uses from project**: []
- **Used by**: `exists_mk0_eq_absNorm_coprime`
- **Visibility**: private
- **Lines**: 2141–2166 (proof ~25)
- **Notes**: mathlib-overlap candidate — natural `Ideal.absNorm` ↔ coprimality bridge; check `Ideal` API.

### `private theorem span_image_basisFun_eq`
- **Type**: `[Finite ι] → (T) → span ℤ (T '' (span ℤ (range basisFun))) = span ℤ (range (basisFun.map T))`
- **What**: The `ℤ`-span of `T` applied to the standard lattice equals the span of the mapped basis (so the `IsZLattice`/covolume API applies).
- **How**: `map_span_int_linearEquiv` + `span_coe_eq_restrictScalars` + `Basis.coe_map`/`range_comp`.
- **Hypotheses**: `ι` finite.
- **Uses from project**: `map_span_int_linearEquiv`
- **Used by**: `covolume_image_basisFun_eq_abs_det` (statement form), `smul_chart_lattice_eq` (indirectly)
- **Visibility**: private
- **Lines**: 2181–2189 (proof ~7)
- **Notes**: none

### `private theorem covolume_image_basisFun_eq_abs_det`
- **Type**: `(T) → ZLattice.covolume (span ℤ (range (basisFun.map T))) = |det T|`
- **What**: The covolume of the image lattice `T '' ℤ^ι` (standard volume) is `|det T|`.
- **How**: `ZLattice.covolume_eq_det` with basis `Basis.span`; change-of-basis matrix is the transpose of `LinearMap.toMatrix` of `T` (`det_transpose`).
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `abs_det_latticeEquiv_mul`
- **Visibility**: private
- **Lines**: 2196–2211 (proof ~12)
- **Notes**: mathlib-overlap candidate — clean covolume = `|det|` for a chart lattice; check `ZLattice.covolume` API.

### `private theorem relIndex_mul_ideal_eq_absNorm`
- **Type**: `(J 𝔟) → relIndex ((𝔟·J).toAddSubgroup) (J.toAddSubgroup) = N(𝔟)`
- **What**: The additive relative index of `𝔟J` in `J` (as subgroups of `𝓞 K`) is `N(𝔟)`.
- **How**: `AddSubgroup.relIndex_mul_index` with `index = absNorm` (`absNorm_eq_index`) and `N(𝔟J)=N(𝔟)·N(J)`; cancel `N(J)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `relIndex_idealLattice_eq_absNorm`
- **Visibility**: private
- **Lines**: 2217–2234 (proof ~16)
- **Notes**: mathlib-overlap candidate — natural ideal-index identity; check `Ideal.absNorm`/`relIndex`.

### `private theorem idealLattice_mul_le`
- **Type**: `(J 𝔟) → idealLattice K (mk0 K (𝔟·J)) ≤ idealLattice K (mk0 K J)`
- **What**: The ideal lattice of `𝔟J` is contained in that of `J`.
- **How**: `(𝔟J : Ideal) ⊆ (J : Ideal)` (`mul_le_left`) lifts to fractional ideals (`coeIdeal_le_coeIdeal`) and to the lattices.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `exists_card_fibre_dvd_eq_card_cell`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`, `chart_sublattice_le`
- **Visibility**: private
- **Lines**: 2239–2252 (proof ~13)
- **Notes**: none

### `private theorem idealLattice_toAddSubgroup_eq`
- **Type**: `(J) → (idealLattice K (mk0 K J)).toAddSubgroup = (J.toAddSubgroup).map (mixedEmbedding ∘ algebraMap)`
- **What**: The ideal lattice as an additive subgroup is the image of the ideal under `mixedEmbedding ∘ algebraMap`.
- **How**: Unfold `mem_idealLattice` and `AddSubgroup.mem_map`; two-way membership.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `relIndex_idealLattice_eq_absNorm`
- **Visibility**: private
- **Lines**: 2258–2276 (proof ~18)
- **Notes**: none

### `private theorem relIndex_idealLattice_eq_absNorm`
- **Type**: `(J 𝔟) → relIndex ((idealLattice K (mk0 K (𝔟·J))).toAddSubgroup) ((idealLattice K (mk0 K J)).toAddSubgroup) = N(𝔟)`
- **What**: The relative index of the sublattice `Λ_{𝔟J} ⊆ Λ_J` is `N(𝔟)`.
- **How**: Transport `relIndex_mul_ideal_eq_absNorm` along the injective additive map `mixedEmbedding∘algebraMap` (`relIndex_map_map_of_injective`).
- **Hypotheses**: none.
- **Uses from project**: `idealLattice_toAddSubgroup_eq`, `relIndex_mul_ideal_eq_absNorm`
- **Used by**: `relIndex_chart_eq_absNorm`
- **Visibility**: private
- **Lines**: 2282–2294 (proof ~6)
- **Notes**: none

### `private theorem chart_lattice_eq_map`
- **Type**: `(J)(T)(hT) → span ℤ (range (basisFun.map T)) = (idealLattice K (mk0 K J)).map (Φ.restrictScalars ℤ)`
- **What**: The chart lattice `T '' ℤ^ι` equals `Λ_J.map Φ` as a `ℤ`-submodule.
- **How**: `span_image_basisFun_eq`, `hT`, `Submodule.map_coe`, `span_coe_eq_restrictScalars`.
- **Hypotheses**: `hT` chart identity.
- **Uses from project**: `span_image_basisFun_eq`
- **Used by**: `chart_sublattice_le`, `relIndex_chart_eq_absNorm`
- **Visibility**: private
- **Lines**: 2299–2317 (proof ~8)
- **Notes**: none

### `private theorem chart_sublattice_le`
- **Type**: `(J 𝔟)(T T')(hT)(hT') → span ℤ (range (basisFun.map T')) ≤ span ℤ (range (basisFun.map T))`
- **What**: The chart sublattice (image of `Λ_{𝔟J}`) is contained in the chart lattice (image of `Λ_J`).
- **How**: `chart_lattice_eq_map` for both, then `Submodule.map_mono (idealLattice_mul_le)`.
- **Hypotheses**: chart identities for `J`, `𝔟J`.
- **Uses from project**: `chart_lattice_eq_map`, `idealLattice_mul_le`
- **Used by**: `abs_det_latticeEquiv_mul`, `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 2321–2332 (proof ~3)
- **Notes**: none

### `private theorem relIndex_chart_eq_absNorm`
- **Type**: `(J 𝔟)(T T')(hT)(hT') → relIndex (L'.toAddSubgroup) (L.toAddSubgroup) = N(𝔟)` (`L = span (basisFun.map T)`, `L' = … T'`)
- **What**: The relative index of the chart sublattice `T' '' ℤ^ι ⊆ T '' ℤ^ι` is `N(𝔟)`.
- **How**: Transport `relIndex_idealLattice_eq_absNorm` along `Φ` (`chart_lattice_eq_map`, `relIndex_map_map_of_injective`).
- **Hypotheses**: chart identities.
- **Uses from project**: `chart_lattice_eq_map`, `relIndex_idealLattice_eq_absNorm`
- **Used by**: `abs_det_latticeEquiv_mul`, `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 2337–2356 (proof ~7)
- **Notes**: none

### `private theorem abs_det_latticeEquiv_mul`
- **Type**: `(J 𝔟)(T T')(hT)(hT') → |det T'| = N(𝔟)·|det T|`
- **What**: The covolume/`|det|` scaling of the sublattice chart: `|det T'| = N(𝔟)·|det T|`.
- **How**: `covolume_div_covolume_eq_relIndex` with `relIndex_chart_eq_absNorm`; rewrite covolumes as `|det|` (`covolume_image_basisFun_eq_abs_det`); `field_simp`/`linarith`.
- **Hypotheses**: chart identities.
- **Uses from project**: `chart_sublattice_le`, `relIndex_chart_eq_absNorm`, `covolume_image_basisFun_eq_abs_det`
- **Used by**: `abs_det_smulTrans_mul`
- **Visibility**: private
- **Lines**: 2365–2387 (proof ~10)
- **Notes**: none

### `private theorem crt_single_coset`
- **Type**: `[Finite ι](L L')(L'≤L)[Finite quotient](m)(gcd(card quotient, m)=1)(ξ∈L) → ∃ ξ'∈L', {a : a∈L' ∧ a∈ξ +ᵥ m•L} = ξ' +ᵥ m•L'`
- **What**: **CRT single-coset fact**: when `relIndex(L',L)` is coprime to `m`, an `m`-coset of `L` meets the sublattice `L'` in exactly one `m·L'`-coset.
- **How**: Multiplication by `m` is bijective on the finite quotient `L/L'` (`Nat.Coprime.nsmul_right_bijective`): surjectivity gives the representative `ξ'`, injectivity gives the single-coset collapse `(a∈L ∧ m·a∈L') → a∈L'`.
- **Hypotheses**: `L'≤L`, finite quotient, `gcd(card quotient, m)=1`, `ξ∈L`.
- **Uses from project**: []
- **Used by**: `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 2396–2449 (proof ~53)
- **Notes**: OVER-50 — needs further /decompose-proof pass. mathlib-overlap candidate — generic lattice/CRT statement, no number-field content.

### `private theorem exists_mk0_eq_absNorm_coprime`
- **Type**: `(D : ClassGroup)(n : ℕ) → 0<n → ∃ J, mk0 J = D ∧ (N(J)).Coprime n`
- **What**: **(L1)** Every ideal class has an integral representative whose norm is coprime to a prescribed `n`.
- **How**: From a representative `J₀` of `D⁻¹`, `IsDedekindDomain.exists_sup_span_eq` produces a principal multiple `(a)` with `𝔫·J₀ ⊔ (a) = J₀`; the cofactor `J₁` of `(a)` is in class `D`, coprime to `𝔫 = (n)`; conclude with `absNorm_coprime_of_isCoprime_span`.
- **Hypotheses**: `n > 0`.
- **Uses from project**: `absNorm_coprime_of_isCoprime_span`
- **Used by**: `cardNormLeResidueClassDvd_div_density`
- **Visibility**: private
- **Lines**: 2458–2519 (proof ~57)
- **Notes**: OVER-50 — needs further /decompose-proof pass. Uses `lia` (lines 2466, 2478). mathlib-overlap candidate — "coprime-norm class representative" is a known number-theory fact; check mathlib `ClassGroup`/avoidance lemmas.

### `private theorem image_range_basisFun_eq`
- **Type**: `[Finite ι] → (T) → (T '' range basisFun) = range (basisFun.map T)`
- **What**: The image of the standard basis range under `T` is the range of the mapped basis.
- **How**: `Basis.coe_map`, `Set.range_comp`.
- **Hypotheses**: `ι` finite.
- **Uses from project**: []
- **Used by**: `smul_chart_lattice_eq`, `exists_card_fibre_dvd_eq_card_cell`
- **Visibility**: private
- **Lines**: 2521–2523 (proof ~2)
- **Notes**: none

### `private theorem smul_chart_lattice_eq`
- **Type**: `[Finite ι](T)(m)(hm) → ((m·)∘T)''ℤ^ι = m•(span ℤ (range (basisFun.map T)))`
- **What**: The `m`-sublattice of the chart lattice in workhorse form: `((m·)∘T)''ℤ^ι = m·(T''ℤ^ι)`.
- **How**: `map_span_int_linearEquiv` + `image_range_basisFun_eq` to rewrite the chart lattice; two-way membership commuting `T` and `m•`.
- **Hypotheses**: `(m:ℝ)≠0`.
- **Uses from project**: `map_span_int_linearEquiv`, `image_range_basisFun_eq`
- **Used by**: `exists_card_fibre_dvd_eq_card_cell`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 2528–2541 (proof ~13)
- **Notes**: none

### `private theorem exists_card_fibre_dvd_eq_card_cell`
- **Type**: `(m)[NeZero m](hm)(J 𝔟)(gcd(N(𝔟),m)=1)(T T')(hT)(hT')(s)(k)(1≤t) → ∃ ξ', #{a∈idealSet K (𝔟J) : norm ≤ t^d ∧ filter=s ∧ J-coset=k} = #((ξ' +ᵥ m•(T''ℤ^ι)) ∩ t•(Φ''normLeOne ∩ orthant_s))`
- **What**: **Sublattice cell count**: `𝔟J`-cone points (partitioned by the `J`-chart) biject with a single `m·Λ_{𝔟J}`-coset inside the dilated orthant cell.
- **How**: `crt_single_coset` (with `relIndex_chart_eq_absNorm`, `chart_sublattice_le`, coprimality) gives the single coset `ξ'`; characterise the injective range of `f = Φ∘(·)` as the coset∩cell using `mem_coset_iff_cos_eq`, `mem_smul_cell_iff_norm_le_and_filter_eq`, `smul_chart_lattice_eq`, `idealLattice_mul_le`, `mem_idealSet_of_chart_mem_smul_cell`.
- **Hypotheses**: `m ≠ 0`, `gcd(N(𝔟),m)=1`, `t ≥ 1`, chart identities.
- **Uses from project**: `relIndex_chart_eq_absNorm`, `chart_sublattice_le`, `crt_single_coset`, `mem_span_int_basisFun_iff`, `image_range_basisFun_eq`, `map_span_int_linearEquiv`, `idealLattice_mul_le`, `mem_smul_cell_iff_norm_le_and_filter_eq`, `mem_idealSet_of_chart_mem_smul_cell`, `mem_coset_iff_cos_eq`, `smul_chart_lattice_eq`
- **Used by**: `exists_card_fibre_dvd_residue_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 2550–2669 (proof ~97)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem abs_det_smulTrans_mul`
- **Type**: `(m)(hm)(J 𝔟)(T T')(hT)(hT') → |det ((m·)∘T')| = N(𝔟)·|det ((m·)∘T)|`
- **What**: The chart-`det` ratio with the `(m·)` factor included: `|det((m·)∘T')| = N(𝔟)·|det((m·)∘T)|`.
- **How**: `abs_det_latticeEquiv_mul` (the `|det(m·)|` factors cancel); `LinearMap.det_comp`, `abs_mul`, `ring`.
- **Hypotheses**: `m ≠ 0`, chart identities.
- **Uses from project**: `abs_det_latticeEquiv_mul`
- **Used by**: `exists_card_fibre_dvd_residue_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 2695–2712 (proof ~3)
- **Notes**: none

### `private theorem exists_card_fibre_dvd_residue_sub_mul_rpow_le`
- **Type**: `(m)[NeZero m](hm)(b)(J 𝔟)(gcd(N(𝔟),m)=1)(T T')(hT)(hT')(hcov)(s)(k) → ∃ C, ∀ t≥1, |#{a∈idealSet K (𝔟J) : (norm ≤ t^d ∧ res b) ∧ orthant s ∧ J-coset k} − (cellconst/N(𝔟))·t^d| ≤ C·t^{d−1}`
- **What**: **(Stage B, fibre)** Per-(orthant, coset) effective `𝔟J`-residue count with leading constant `L_J/N(𝔟)`.
- **How**: Case on whether the `J`-cell realizes `b`: if so the `𝔟J`-residue filter is vacuous (constancy `residue_fibre_const_aux` via `idealLattice_mul_le`), so count = full cell count `exists_card_fibre_dvd_eq_card_cell` ≈ `vol/|det((m·)∘T')|·t^d`, and the det ratio `abs_det_smulTrans_mul` turns this into `(vol/|det((m·)∘T)|)/N(𝔟)`; else empty.
- **Hypotheses**: `m≠0`, `gcd(N(𝔟),m)=1`, chart identities, frontier cover.
- **Uses from project**: `exists_card_cell_sub_mul_rpow_le_explicit`, `abs_det_smulTrans_mul`, `residue_fibre_const_aux`, `idealLattice_mul_le`, `exists_card_fibre_dvd_eq_card_cell`, `smul_chart_lattice_eq`
- **Used by**: `exists_card_idealSet_residue_real_le_dvd`
- **Visibility**: private
- **Lines**: 2724–2823 (proof ~64)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem exists_card_idealSet_residue_real_le_dvd`
- **Type**: `(m)[NeZero m](hm)(b)(J 𝔟)(gcd(N(𝔟),m)=1) → ∃ κ C', (∀ S≥1, |#{a∈idealSet K J : norm ≤ S ∧ res b} − κ·S| ≤ C'·S^{1−1/d}) ∧ (∀ S≥1, |#{a∈idealSet K (𝔟J) : …} − (κ/N(𝔟))·S| ≤ C'·S^{1−1/d})`
- **What**: **(Stage B, summed)** The `J`- and `𝔟J`-cone residue counts share a leading constant up to `N(𝔟)`: both `≈ κ·S` and `≈ (κ/N(𝔟))·S`.
- **How**: Charts via `exists_latticeEquiv_image_idealLattice`; `choose` the explicit per-cell constants from `exists_card_residue_fibre_sub_mul_rpow_le_explicit` (`J`-side) and `exists_card_fibre_dvd_residue_sub_mul_rpow_le` (`𝔟J`-side); sum at `tN=S^{1/d}` via `card_residue_sum_bound_aux`.
- **Hypotheses**: `m≠0`, `gcd(N(𝔟),m)=1`.
- **Uses from project**: `exists_latticeEquiv_image_idealLattice`, `exists_card_residue_fibre_sub_mul_rpow_le_explicit`, `exists_card_fibre_dvd_residue_sub_mul_rpow_le`, `card_residue_sum_bound_aux` (+ sibling `normLeOne_frontier_lipschitz_cover_index`)
- **Used by**: `cardNormLeResidueClassDvd_div_density`
- **Visibility**: private
- **Lines**: 2834–2886 (proof ~46)
- **Notes**: long (30–50)

### `private theorem card_principalize_dvd`
- **Type**: `(c)[NeZero c](𝔟)(y)(N)(D)(J)(mk0 J = D⁻¹)(0<N(J)) → cardNormLeResidueClassDvd c 𝔟 y D N = #{I : 𝔟J ∣ I ∧ (IsPrincipal I ∧ N(I) ≤ N·N(J) ∧ N(I)≡y.val·N(J) mod c·N(J))}`
- **What**: **(Stage C)** Principalization of the `𝔟`-divisible count: equals the count of `𝔟J`-divisible principal ideals with scaled norm/residue.
- **How**: Bijection `Equiv.dvd J` with `principalize_iff`; the divisibility `𝔟 ∣ I ↔ 𝔟J ∣ J·I` is `mul_dvd_mul_iff_left`; `Equiv.subtypeSubtypeEquivSubtype`.
- **Hypotheses**: `mk0 J=D⁻¹`, `N(J)>0`.
- **Uses from project**: `cardNormLeResidueClassDvd`, `principalize_iff`
- **Used by**: `cardNormLeResidueClassDvd_div_density`
- **Visibility**: private
- **Lines**: 2894–2933 (proof ~29)
- **Notes**: none

### `private theorem tendsto_count_div_of_cone_bridge`
- **Type**: `(NJ)(0<NJ)(κ₀ C')(cnt : ℕ→ℕ)(coneR : ℝ→ℝ)(bridge: cnt N·torsionOrder = coneR(N·NJ))(cone estimate) → Tendsto (cnt N / N) atTop (nhds (κ₀·NJ/torsionOrder))`
- **What**: From a cone estimate + torsion bridge to the count density `κ₀·NJ/torsionOrder`.
- **How**: `tendsto_div_atTop_of_sub_mul_rpow_le` with the bridge substituted and the error rescaled (`(NJ)^{1−1/d} ≤ NJ`).
- **Hypotheses**: `NJ>0`; bridge and cone estimate.
- **Uses from project**: `tendsto_div_atTop_of_sub_mul_rpow_le`
- **Used by**: `cardNormLeResidueClassDvd_div_density`
- **Visibility**: private
- **Lines**: 2939–2974 (proof ~35)
- **Notes**: long (30–50)

### `private theorem card_isPrincipal_dvd_norm_le_residue_natBound`
- **Type**: `(I₀)(m b M : ℕ) → #{I₀ ∣ I, IsPrincipal I, N(I) ≤ M, N(I)≡b mod m}·torsionOrder = #{a∈idealSet K I₀ : norm a ≤ (M:ℝ) ∧ intNorm a ≡ b}`
- **What**: The torsion bridge specialised to a `ℕ`-bound `M`.
- **How**: `card_isPrincipal_dvd_norm_le_residue` at `s=(M:ℝ)`, with `Nat.cast_le` to convert the bound.
- **Hypotheses**: none.
- **Uses from project**: `card_isPrincipal_dvd_norm_le_residue`
- **Used by**: `cardNormLeResidueClassDvd_div_density`
- **Visibility**: private
- **Lines**: 2981–2990 (proof ~4)
- **Notes**: none

### `private theorem cardNormLeResidueClassDvd_div_density`
- **Type**: `(c)[NeZero c](𝔟)(hu)(y)(D){κfull}(hκfull : density of cardNormLeResidueClass c y D) → Tendsto (cardNormLeResidueClassDvd c 𝔟 y D N / N) atTop (nhds (κfull/N(𝔟)))`
- **What**: **(Geometric Route B / Stage D)** The `𝔟`-divisible class-`D` density is `κfull/N(𝔟)`.
- **How**: Coprime representative `J` of `D⁻¹` (`exists_mk0_eq_absNorm_coprime`); two cone bridges (`card_principalize`/`card_principalize_dvd` + `card_isPrincipal_dvd_norm_le_residue_natBound`); the shared cone estimate `exists_card_idealSet_residue_real_le_dvd` gives both densities through `tendsto_count_div_of_cone_bridge`; uniqueness of limits cancels the `N(𝔟)` and torsion factors.
- **Hypotheses**: `N(𝔟) mod c` a unit; `hκfull`.
- **Uses from project**: `exists_mk0_eq_absNorm_coprime`, `exists_card_idealSet_residue_real_le_dvd`, `cardNormLeResidueClass`, `card_principalize`, `card_isPrincipal_dvd_norm_le_residue_natBound`, `cardNormLeResidueClassDvd`, `card_principalize_dvd`, `tendsto_count_div_of_cone_bridge`
- **Used by**: `tendsto_cardNormLeResidueClass_div_transfer`
- **Visibility**: private
- **Lines**: 3000–3051 (proof ~43)
- **Notes**: long (30–50)

### `private theorem cardNormLeResidueClassDvd_eq_div`
- **Type**: `(c)[NeZero c](𝔟)(hu){xC y}{CC D}(xC·N(𝔟)=y)(CC·[𝔟]=D)(N) → cardNormLeResidueClassDvd c 𝔟 y D N = cardNormLeResidueClass c xC CC ⌊N/N(𝔟)⌋`
- **What**: **Route-A count identity (floor form)**: the `𝔟`-divisible class-`D` residue-`y` count at `N` equals the class-`CC` residue-`xC` count at `⌊N/N(𝔟)⌋`.
- **How**: Combine `cardNormLeResidueClassDvd_floor_collapse` with `cardNormLeResidueClass_eq_dvd`.
- **Hypotheses**: `N(𝔟) mod c` a unit; `xC·N(𝔟)=y`, `CC·[𝔟]=D`.
- **Uses from project**: `cardNormLeResidueClassDvd_floor_collapse`, `cardNormLeResidueClass_eq_dvd`
- **Used by**: `cardNormLeResidueClassDvd_div_density_routeA`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 3058–3067 (proof ~3)
- **Notes**: none

### `private theorem cardNormLeResidueClassDvd_div_density_routeA`
- **Type**: `(c)[NeZero c](𝔟)(hu)(y)(D){κCC}(hκCC : density of cardNormLeResidueClass c (y·u⁻¹) (D·[𝔟]⁻¹)) → Tendsto (cardNormLeResidueClassDvd c 𝔟 y D N / N) atTop (nhds (κCC/N(𝔟)))`
- **What**: **Route A as a density (elementary)**: the `𝔟`-divisible density is `κ_{CC,xC}/N(𝔟)`.
- **How**: `cardNormLeResidueClassDvd_eq_div` turns the count into `cardNormLeResidueClass c xC CC ⌊N/N(𝔟)⌋`; the floor ratio `⌊N/N(𝔟)⌋/N → 1/N(𝔟)` (`Nat.div_add_mod`, squeeze); compose with `hκCC`.
- **Hypotheses**: `N(𝔟) mod c` a unit; `hκCC`.
- **Uses from project**: `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`, `cardNormLeResidueClassDvd_eq_div`
- **Used by**: `tendsto_cardNormLeResidueClass_div_transfer`
- **Visibility**: private
- **Lines**: 3075–3136 (proof ~52)
- **Notes**: OVER-50 — needs further /decompose-proof pass

### `private theorem tendsto_cardNormLeResidueClass_div_transfer`
- **Type**: `(c)[NeZero c](𝔟)(hu)(x)(C){κ}(hκ : density of cardNormLeResidueClass c x C) → Tendsto (cardNormLeResidueClass c (x·N(𝔟)) (C·[𝔟]) N / N) atTop (nhds κ)`
- **What**: **The geometry-of-numbers density transfer** (Lang VI §3 Thm 3; GRS Thm 1): the per-class density is invariant under `(class, residue) ↦ (class·[𝔟], residue·N(𝔟))`.
- **How**: Pin the common `𝔟`-divisible density two ways — geometric (`cardNormLeResidueClassDvd_div_density`) and Route-A (`cardNormLeResidueClassDvd_div_density_routeA`) — whose `N(𝔟)` factors cancel (`div_left_inj'`, uniqueness).
- **Hypotheses**: `N(𝔟) mod c` a unit; `hκ`.
- **Uses from project**: `cardNormLeResidueClass`, `exists_tendsto_cardNormLeResidueClass_div`, `cardNormLeResidueClassDvd_div_density`, `cardNormLeResidueClassDvd_div_density_routeA`
- **Used by**: `cardNormLeResidueClassDvd_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 3146–3176 (proof ~21)
- **Notes**: none

### `private theorem exists_sub_mul_rpow_le_of_div`
- **Type**: `{f : ℕ→ℝ}{κ C₀}{d NB} → 0<d → 0<NB → f 0 = 0 → (∀ M≥1, |f M − κ·M| ≤ C₀·M^{1−1/d}) → ∃ C', ∀ N≥1, |f ⌊N/NB⌋ − (κ/NB)·N| ≤ C'·N^{1−1/d}`
- **What**: Floor-division transfer of an `O(N^{1−1/d})` effective bound, leading constant scaling by `1/NB`, new error constant `|C₀|+|κ|`.
- **How**: Split `f⌊N/NB⌋ − (κ/NB)·N` into the bound term and a floor-defect term bounded by `|κ|·(N/NB − ⌊N/NB⌋) < |κ|` (`Nat.div_add_mod`, `nlinarith`).
- **Hypotheses**: `d>0`, `NB>0`, `f 0 = 0`, effective bound.
- **Uses from project**: []
- **Used by**: `cardNormLeResidueClassDvd_sub_mul_rpow_le`
- **Visibility**: private
- **Lines**: 3181–3220 (proof ~38)
- **Notes**: long (30–50). mathlib-overlap candidate — purely analytic floor-division asymptotic.

### `private theorem cardNormLeResidueClassDvd_sub_mul_rpow_le`
- **Type**: `(c)[NeZero c](𝔟)(hu)(y)(D){κfull}(hκfull) → ∃ C', ∀ N≥1, |cardNormLeResidueClassDvd c 𝔟 y D N − (κfull/N(𝔟))·N| ≤ C'·N^{1−1/d}`
- **What**: **Effective form of the `𝔟`-divisible count** (Lang VI §3 Thm 3; GRS Thm 1): leading constant `κfull/N(𝔟)`.
- **How**: Route-A count identity `cardNormLeResidueClassDvd_eq_div` reduces to the per-class estimate `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le` for `(xC, CC)`; the leading constant is pinned `= κfull` by `tendsto_cardNormLeResidueClass_div_transfer`; apply `exists_sub_mul_rpow_le_of_div`.
- **Hypotheses**: `N(𝔟) mod c` a unit; `hκfull`.
- **Uses from project**: `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le`, `cardNormLeResidueClass`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `tendsto_cardNormLeResidueClass_div_transfer`, `exists_sub_mul_rpow_le_of_div`, `cardNormLeResidueClassDvd_eq_div`
- **Used by**: `cardNormLeResidueClass_density_transfer`
- **Visibility**: private
- **Lines**: 3231–3273 (proof ~42)
- **Notes**: long (30–50)

### `private theorem cardNormLeResidueClass_density_transfer`
- **Type**: `(c)[NeZero c](𝔟)(hu)(x)(C){κ κ'}(hκ : density at (x,C))(hκ' : density at (x·N(𝔟), C·[𝔟])) → κ = κ'`
- **What**: **Per-class realizer transfer** (the geometric heart): `κ_{C,x} = κ_{C·[𝔟], x·N(𝔟)}`.
- **How**: Route A (`cardNormLeResidueClass_eq_dvd`) + the limit form of the effective kernel `cardNormLeResidueClassDvd_sub_mul_rpow_le`; the `N(𝔟)` factors cancel (uniqueness, `mul_div_cancel₀`).
- **Hypotheses**: `N(𝔟) mod c` a unit; both densities given.
- **Uses from project**: `cardNormLeResidueClass`, `cardNormLeResidueClassDvd`, `cardNormLeResidueClassDvd_sub_mul_rpow_le`, `tendsto_div_atTop_of_sub_mul_rpow_le`, `cardNormLeResidueClass_eq_dvd`
- **Used by**: `cardNormLeResidue_density_transfer`
- **Visibility**: private
- **Lines**: 3283–3319 (proof ~36)
- **Notes**: long (30–50)

### `private theorem cardNormLeResidue_density_transfer`
- **Type**: `(c)[NeZero c](𝔟)(hu)(x){κ κ'}(hκ : density of cardNormLeResidue c x)(hκ' : density of cardNormLeResidue c (x·N(𝔟))) → κ = κ'`
- **What**: **Global realizer transfer**: `κ_x = κ_{x·N(𝔟)}` for the (class-summed) residue densities.
- **How**: Sum the per-class transfer `cardNormLeResidueClass_density_transfer` over the class group, reindexing by `Equiv.mulRight [𝔟]`; split densities via `tendsto_cardNormLeResidue_div_eq_sum_class`.
- **Hypotheses**: `N(𝔟) mod c` a unit; both densities given.
- **Uses from project**: `exists_tendsto_cardNormLeResidueClass_div`, `cardNormLeResidue`, `tendsto_cardNormLeResidue_div_eq_sum_class`, `cardNormLeResidueClass_density_transfer`
- **Used by**: `cardNormLeResidue_density_const_of_realized`
- **Visibility**: private
- **Lines**: 3325–3348 (proof ~14)
- **Notes**: none

### `private theorem cardNormLeResidue_density_const_of_realized`
- **Type**: `{c}[NeZero c]{S}(hS : every a∈S realized as a norm residue)(a,a'∈S){κ κ'}(densities) → κ = κ'`
- **What**: **κ-constancy over the realized-residue subgroup**: densities of `a, a' ∈ S` coincide when all of `S` is realized as ideal-norm residues.
- **How**: Both densities transfer from the residue-`1` density via `cardNormLeResidue_density_transfer` along the realizers `𝔟`, `𝔟'` of `a`, `a'`.
- **Hypotheses**: `hS` (realization on `S`).
- **Uses from project**: `cardNormLeResidue`, `exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_transfer`
- **Used by**: `tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`
- **Visibility**: private
- **Lines**: 3356–3384 (proof ~18)
- **Notes**: none

### `theorem tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`
- **Type**: `(K)(c)[NeZero c](S)(hS : every a∈S realized)(χ : S→*ℂˣ)(χ≠1) → Tendsto (fun N ↦ (∑_{s∈S} χ(s)·#{N(I)≤N, N(I)≡s})/N) atTop (nhds 0)`
- **What**: **Top-level result — the `hF` producer.** For a realized subgroup `S` and a nontrivial character `χ`, the `χ`-twisted residue-count average over `S` tends to `0` (row orthogonality).
- **How**: Per-residue densities are constant on `S` (`cardNormLeResidue_density_const_of_realized`); the limit of the twisted average is `(∑_{s} χ(s))·κ₁ = 0` by `sum_char_self_eq_zero_of_ne_one`.
- **Hypotheses**: `c ≠ 0`; `hS`; `χ ≠ 1`.
- **Uses from project**: `exists_tendsto_cardNormLeResidue_div`, `cardNormLeResidue_density_const_of_realized`, `cardNormLeResidue` (+ sibling `sum_char_self_eq_zero_of_ne_one`)
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 3400–3435 (proof ~36)
- **Notes**: long (30–50). Terminal consumer — exported API; intended to discharge the `hF` hypothesis of the uniform theorem.

---

## File Summary

**Total declarations: 85** — defs **3** (`cardNormLeResidue`, `cardNormLeResidueClass`,
`cardNormLeResidueClassDvd`) / lemmas+theorems **82** / instances **0** / structures/classes/abbrevs/inductives **0**.

**Public (4 — the exported API):** `exists_card_coset_inter_smul_sub_volume_mul_rpow_le`,
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le`,
`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`,
`tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`. All others `private`.

**Key API (used by ≥3 in-file):**
- `mem_span_int_basisFun_iff` (5), `map_span_int_linearEquiv` (≥5), `cardNormLeResidue` (6),
  `cardNormLeResidueClass` (11), `cardNormLeResidueClassDvd` (8),
  `tendsto_div_atTop_of_sub_mul_rpow_le` (6), `exists_tendsto_cardNormLeResidue_div` (5),
  `exists_card_norm_le_residue_class_eq_sub_mul_rpow_le` (3),
  `exists_card_cell_sub_mul_rpow_le_explicit` (3), `residue_fibre_const_aux` (3,
  counting the `_explicit`/dvd consumers), `idealLattice_mul_le` (3),
  `mem_smul_cell_iff_norm_le_and_filter_eq` (3), `mem_coset_iff_cos_eq` (3),
  `mem_idealSet_of_chart_mem_smul_cell` (3).

**Unused decls (in this file):** `exists_card_cell_sub_mul_rpow_le` (only the `_explicit` form is
used downstream). The four **public** terminal consumers
(`exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le_uniform`,
`tendsto_sum_char_mul_cardNormLeResidue_div_of_realized`, the workhorse, and the base per-residue
theorem) are "unused in file" by design — they are the module's external interface.

**Decls with `sorry`:** none.

**Decls with `set_option`:** none.

**Proofs >50 lines (decompose-needed) — 11:**
- `exists_card_fibre_dvd_eq_card_cell` (~97), `abs_cardR_translate_sub_volume_le` (~80),
  `ncard_index1_image_smul_chart_le` (~78), `exists_card_fibre_dvd_residue_sub_mul_rpow_le` (~64),
  `exists_card_coset_inter_smul_sub_volume_mul_rpow_le` (~59),
  `exists_card_residue_fibre_sub_mul_rpow_le_explicit` (~58),
  `exists_mk0_eq_absNorm_coprime` (~57), `card_isPrincipal_dvd_norm_le_residue` (~55),
  `crt_single_coset` (~53), `mem_smul_cell_iff_norm_le_and_filter_eq` (~52),
  `cardNormLeResidueClassDvd_div_density_routeA` (~52).

**Proofs 30–50 lines — 18:** `norm_eq_prod_real_emb_mul_prod_complex` (~43),
`natAbs_norm_eq_neg_one_pow_mul_norm` (~37), `card_norm_le_residue_eq_sum_class` (~38),
`exists_lipschitz_cube_cover_hyperplane_slab` (~43), `sub_mem_nsmul_of_coord_eq` (~44),
`mem_coset_iff_cos_eq` (~50), `card_fibre_eq_card_cell` (~49), `residue_fibre_const_aux` (~46),
`card_idealSet_residue_eq_sum_cell` (~30), `card_residue_sum_bound_aux` (~43),
`exists_card_idealSet_residue_le` (~30), `tendsto_count_div_of_cone_bridge` (~35),
`exists_card_idealSet_residue_real_le_dvd` (~46), `cardNormLeResidueClassDvd_div_density` (~43),
`exists_sub_mul_rpow_le_of_div` (~38), `cardNormLeResidueClassDvd_sub_mul_rpow_le` (~42),
`cardNormLeResidueClass_density_transfer` (~36),
`tendsto_sum_char_mul_cardNormLeResidue_div_of_realized` (~36).

**ForMathlib name/statement-overlap flags (likely already in mathlib or naming risk — verify before PR):**
- `natCast_eq_iff_mul_natCast_eq` — elementary `ZMod`/`Nat.ModEq` scaling identity.
- `mem_span_int_basisFun_iff` — standard-lattice ⟺ integer-coordinate membership of `Pi.basisFun`.
- `map_span_int_linearEquiv` — `f '' (span ℤ S) = span ℤ (f '' S)`; near `Submodule.map_span`.
- `prod_eq_neg_one_pow_card_mul_prod_abs` — fully generic `Finset.prod` sign identity.
- `Nat.le_iff_le_mul_div_of_dvd` — generic, AND declared in the **`Nat.`** namespace (clobber risk
  for a ForMathlib decl — rename/relocate).
- `tendsto_div_atTop_of_sub_mul_rpow_le`, `exists_sub_mul_rpow_le_of_div` — purely analytic
  asymptotic ⟹ limit-of-ratio lemmas (no number theory); candidates for `Mathlib.Analysis`.
- `covolume_image_basisFun_eq_abs_det` — `ZLattice.covolume (T''ℤ^ι) = |det T|`.
- `relIndex_mul_ideal_eq_absNorm`, `absNorm_coprime_of_isCoprime_span` — natural `Ideal.absNorm`
  identities (index = norm; coprime ideal ⟹ coprime norms).
- `crt_single_coset` — generic lattice/CRT single-coset fact, no number-field content.
- `exists_mk0_eq_absNorm_coprime` — coprime-norm class representative (standard avoidance).
- `natCast_algebraNorm_add_nsmul_mul`, `norm_eq_prod_real_emb_mul_prod_complex` — generic
  `Algebra.norm` / `InfinitePlace` facts; check for existing forms.

**General ForMathlib caveat:** several private helpers are stated only for `index K → ℝ` /
specific number-field charts but are mathematically generic (lattice/`Submodule`/`Finset`/analysis
level); for mathlib they should be re-examined for the maximally-general signature (`Fintype ι`,
abstract `ZLattice`, abstract `CommGroup` Fourier) before extraction.
