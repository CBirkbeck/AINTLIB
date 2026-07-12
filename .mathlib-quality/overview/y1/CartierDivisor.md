# Inventory: `projects/ModularCurves/ModularCurves/LevelStructure/CartierDivisor.lean`

Phase-1 /overview inventory (y1). File: 2,964 lines, namespace `ModularCurves`
(sub-namespaces `RelEffCartierDiv`, `IsOfficialCartier`; section `FullSections`).
Subject: relative effective Cartier divisors and full sets of sections (KM Ch. 1, §§1.1–1.9)
— the substrate for Drinfeld level structures.

Project imports: `ModularCurves.EllipticCurve.GroupLaw`, `ForMathlib.CharpolyNorm`,
`ForMathlib.FinrankExact`, `ForMathlib.IdealSheafComapMul`, `ForMathlib.NormBaseChange`,
`ForMathlib.SheafDisjointUnion`, `ForMathlib.StandardSmoothStalkDVR`.
Note: no name from `EllipticCurve.GroupLaw` or `ForMathlib.IdealSheafComapMul` is used in this
file (verified by grep) — those two imports are positioning/transitive only.
Downstream in-project consumers of this file: `EllipticCurve/PoleSheaf.lean`,
`LevelStructure/ExactOrder.lean`.

Standing variables: `{C S : Scheme.{u}}`, `{π : C ⟶ S}` (in `RelEffCartierDiv` /
`IsOfficialCartier`); `(R B : Type u) [CommRing R] [CommRing B] [Algebra R B]` (in
`FullSections`).

---

## 1. `RelEffCartierDiv`
- **Type**: structure (data: `ideal : C.IdealSheafData` + 3 Prop/instance fields `finite`, `flat`, `lfp`)
- **What**: relative effective Cartier divisor in `C/S` in the working KM 1.2.3 form: a closed subscheme (given by its ideal sheaf) finite + flat + locally of finite presentation over `S` (= finite locally free).
- **How**: definition; no proof.
- **Hypotheses**: `(π : C ⟶ S)`.
- **Uses from project**: [].
- **Used by (in file)**: subject of the whole `RelEffCartierDiv` namespace — `degree`, `sectionDivisor`, `sectionsDivisor`, `baseChange(_prop/_ideal)`, `ext`, `flatPullback(_prop/_ideal/_id/_flatPullback)`, `isOfficial`, `officialAux_exists_finite_chart`, `sectionsDivisor_degree`, `IsOfficialCartier.toRelEffCartierDiv`. KEY API.
- **Visibility**: public.
- **Lines**: 61–73 (13).
- **Notes**: docstring records that the official definition (invertible ideal sheaf, KM 1.1.1) is deferred to ticket `T-D1` (API gap AG-LB).

## 2. `IsOfficialCartier`
- **Type**: structure (Prop; fields `flat`, `locallyPrincipal`)
- **What**: official effective Cartier divisor predicate on an ideal sheaf `J` (KM 1.1.1, affine-local form): subscheme flat over `S` and `J` affine-locally `Ideal.span {f}` with `f` a nonzerodivisor.
- **How**: definition; no proof.
- **Hypotheses**: `(π : C ⟶ S) (J : C.IdealSheafData)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionDivisor_isOfficial`, `RelEffCartierDiv.isOfficial`, `IsOfficialCartier.locallyOfFinitePresentation`, `IsOfficialCartier.isFinite`, `IsOfficialCartier.toRelEffCartierDiv`. KEY API (5 users).
- **Visibility**: public.
- **Lines**: 75–92 (18).
- **Notes**: invertible-ideal-MODULE interface deferred to ticket `T-D19` (AG-LB).

## 3. `RelEffCartierDiv.degree`
- **Type**: noncomputable def
- **What**: degree of the divisor at `s : S` = `Scheme.Hom.finrank` of the finite locally free `D ⟶ S` (KM 1.2).
- **How**: direct: feeds `D.finite`, `D.flat` as instances into mathlib's `Scheme.Hom.finrank`.
- **Hypotheses**: `(D : RelEffCartierDiv π) (s : S)`.
- **Uses from project**: [] (`Scheme.Hom.finrank` is mathlib `Morphisms/FlatRank`).
- **Used by (in file)**: `sectionDivisor_degree`, `sectionsDivisor_degree`.
- **Visibility**: public.
- **Lines**: 98–103 (6).

## 4. `RelEffCartierDiv.isPullback_sectionBaseChange`
- **Type**: theorem
- **What**: base-change square of a section is cartesian: `T` is the fibre product of `C ×_S T ⟶ C` against the section `z` (via `pullback.lift (t ≫ z) (𝟙 T)`).
- **How**: hand-built limit cone: `IsPullback.of_isLimit'` + `Limits.PullbackCone.IsLimit.mk`, with the fibre-map computation `hb'` from `s.condition` and `Limits.pullback.lift_fst/lift_snd`; uniqueness by postcomposing with `pullback.snd`.
- **Hypotheses**: `(z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S)`.
- **Uses from project**: [].
- **Used by (in file)**: `ker_sectionBaseChange`.
- **Visibility**: public.
- **Lines**: 105–139 (35; proof body ~27).

## 5. `RelEffCartierDiv.ker_sectionBaseChange`
- **Type**: theorem
- **What**: kernel ideal of a base-changed section = scheme-theoretic preimage (`.comap (pullback.fst π t)`) of the section's kernel.
- **How**: `z` is a closed immersion (`IsClosedImmersion.of_comp` from `hz`); rewrite along the isoPullback of #4 with `Scheme.Hom.ker_comp_of_isIso` and `Scheme.IdealSheafData.ker_fst_of_isClosedImmersion` (mathlib IdealSheaf/Functorial).
- **Hypotheses**: `[IsSeparated π] (z) (hz) (t : T ⟶ S)`.
- **Uses from project**: [].
- **Used by (in file)**: none (exported for downstream base-change work, cf. ExactOrder/PoleSheaf).
- **Visibility**: public.
- **Lines**: 141–154 (14).

## 6. `RelEffCartierDiv.sectionDivisor`
- **Type**: noncomputable def
- **What**: **T-D3 single-section case (KM 1.2.2)** — the divisor `[P]` of a section `z`: `RelEffCartierDiv` with ideal `z.ker`.
- **How**: `z` closed immersion by `IsClosedImmersion.of_comp`; `z.ker.subschemeι ≫ π = inv z.toImage` (`Scheme.Hom.toImage_imageι`, `IsIso.eq_inv_comp`), so finite/flat/lfp transport from the identity by `infer_instance`.
- **Hypotheses**: `(π) [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionDivisor_degree`, `sectionDivisor_isOfficial`.
- **Visibility**: public.
- **Lines**: 156–175 (20).

## 7. `RelEffCartierDiv.sectionDivisor_degree`
- **Type**: theorem
- **What**: **T-D3** — `(sectionDivisor π z hz).degree s = 1`.
- **How**: same iso reduction as #6 then `Scheme.Hom.finrank_eq_one_of_isIso` (mathlib FlatRank) + `simp`.
- **Hypotheses**: `(π) [IsSeparated π] (z) (hz) (s : S)`.
- **Uses from project**: [].
- **Used by (in file)**: none in code (cited in `sectionsIdeal_finrank`'s docstring).
- **Visibility**: public.
- **Lines**: 177–190 (14).

### section `KerPrincipal` (200–956) — T-D22 (HB-REGIMM, KM 1.2.2 / GME §2.1.4)

## 8. `kerPrincipalAux_basis_expand`
- **Type**: private theorem
- **What**: in a module with a singleton basis, `m = b.repr m default • b default`.
- **How**: `b.repr.injective` + `Finsupp.ext`, `Module.Basis.repr_self`.
- **Hypotheses**: `[CommRing A] [Module A M] [Unique ι] (b : Module.Basis ι A M) (m : M)`.
- **Uses from project**: [].
- **Used by (in file)**: `kerPrincipalAux_le_span_sup`, `kerPrincipalAux_nzd` (×3 sites).
- **Visibility**: private.
- **Lines**: 202–209 (8).

## 9. `kerPrincipalAux_exists_repr_one`
- **Type**: private theorem
- **What**: kernel of a retraction `σ : A →ₐ[R] R` (with `Ω[A⁄R]` free of rank one) contains `x` whose differential's basis coordinate maps to `1` under `σ` — surjectivity of the retraction-twisted conormal map `I/I² → R ⊗ Ω`.
- **How**: span induction over `KaehlerDifferential.span_range_derivation` (key lemma `Submodule.span_induction`), Leibniz bookkeeping via `Derivation.leibniz` / `Derivation.map_algebraMap`; then correct `x₀` by subtracting `algebraMap R A (σ x₀)`.
- **Hypotheses**: `[CommRing R] [CommRing A] [Algebra R A] [Unique ι] (b : Basis ι A Ω[A⁄R]) (σ : A →ₐ[R] R)`.
- **Uses from project**: [].
- **Used by (in file)**: `kerPrincipalAux_le_span_sup`, `kerPrincipalAux_nzd`.
- **Visibility**: private.
- **Lines**: 211–265 (55). **Notes**: proof >30 lines (~47).

## 10. `kerPrincipalAux_le_span_sup`
- **Type**: private theorem
- **What**: conormal step of T-D22: `I := ker σ` satisfies `I ≤ (f) ⊔ I•I` for an explicit `f ∈ I` (both directions of the conormal iso `I/I² ≅ R ⊗ Ω[A⁄R]` proved by hand).
- **How**: generator from #9; injectivity via the canonical derivation `𝔇 : a ↦ [a − φ(σa)]` into `A ⧸ I•I` (constructed as a `Derivation` — Leibniz check by `Submodule.Quotient.eq` + ring identity), lifted by `Derivation.liftKaehlerDifferential_comp_D`; membership split by `Submodule.mem_sup`.
- **Hypotheses**: as #9.
- **Uses from project**: [].
- **Used by (in file)**: `kerPrincipalAux_exists_gen`.
- **Visibility**: private.
- **Lines**: 267–364 (98, incl. `open scoped Pointwise in`). **Notes**: proof >30 lines (~86).

## 11. `kerPrincipalAux_unique_index`
- **Type**: `@[reducible]` private noncomputable def
- **What**: for nontrivial standard-smooth `A/R` of relative dimension 1, `Unique (Module.Free.ChooseBasisIndex A Ω[A⁄R])`.
- **How**: `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` gives rank 1; `Module.Free.rank_eq_card_chooseBasisIndex` + `Cardinal.eq_one_iff_unique`.
- **Hypotheses**: `[Nontrivial A] [Algebra.IsStandardSmoothOfRelativeDimension 1 R A]`.
- **Uses from project**: [].
- **Used by (in file)**: `kerPrincipalAux_exists_gen`, `kerPrincipalAux_nzd` (×2 sites).
- **Visibility**: private.
- **Lines**: 366–381 (16). **Notes**: `haveI` inside the *statement* (instance-in-type); `@[reducible]`.

## 12. `kerPrincipalAux_exists_gen`
- **Type**: private theorem
- **What**: T-D22 pure-algebra heart: `∃ f ∈ ker σ, ∃ r, r − 1 ∈ ker σ ∧ ∀ x ∈ ker σ, r·x ∈ (f)` (Nakayama-inverted generator).
- **How**: #10 + Nakayama: key lemma `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup`; FG of the kernel from `Algebra.FinitePresentation.ker_fG_of_surjective`.
- **Hypotheses**: `[Nontrivial A] [IsStandardSmoothOfRelativeDimension 1 R A] (σ : A →ₐ[R] R)`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 383–403 (21).

## 13. `kerPrincipalAux_nzd`
- **Type**: private theorem
- **What**: **T-D22 nonzerodivisor leg** (EGA IV 17.12.1 / KM 1.2.2): a generator `f` of `ker σ` is a nonzerodivisor in `A`.
- **How**: localize at `g` = basis coordinate of `df` (`Localization.Away g`); `df'` generates `Ω[A'⁄R]` (span induction over `KaehlerDifferential.span_range_map_derivation_of_isLocalization`); `Ω[A'⁄R[X]] = 0` and injectivity of `mapBaseChange`, hence formal smoothness over `R[X]` via the Jacobi–Zariski sequence — key lemmas `Algebra.H1Cotangent.exact_δ_mapBaseChange`, `Algebra.H1Cotangent.exact_map_δ`; then `Algebra.Smooth.flat` and `Module.Flat.isSMulRegular_of_nonZeroDivisors` (on `X`) give `f` regular in `A'`; endgame: binomial decomposition `gⁿ = φ((σg)ⁿ) + f·c` and unit cancellation `IsUnit.mul_right_eq_zero`.
- **Hypotheses**: `[IsStandardSmoothOfRelativeDimension 1 R A] (σ) (f) (hf : ker σ = span {f})`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 405–648 (244). **Notes**: longest proof in file (>30, ~227 lines); candidate for decomposition once sorry-free consumers stabilise (producer's call).

## 14. `kerPrincipalAux_ideal_map_span`
- **Type**: private lemma
- **What**: an ideal `I` with witness `r·I ⊆ (f)`, `f ∈ I`, becomes exactly `Ideal.span {algebraMap A B f}` in any `Away r` localization `B`.
- **How**: `le_antisymm`; unit of `r` via `IsLocalization.map_units`, coefficients through `Ideal.mem_span_singleton'`.
- **Hypotheses**: `[IsLocalization.Away r B] (I f) (hfI) (hr)`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 651–669 (19).

## 15. `kerPrincipalAux_retraction`
- **Type**: private lemma (`variable (π) in`)
- **What**: on a retraction pair of opens (`V ≤ π⁻¹U`, `U ≤ z⁻¹V`), `π.appLE U V ≫ z.appLE V U = 𝟙 Γ(S,U)`.
- **How**: `Scheme.Hom.appLE_comp_appLE` then generalize `z ≫ π` to `𝟙 S` and use `S.presheaf.map_id`.
- **Hypotheses**: `(z) (hz : z ≫ π = 𝟙 S) (hVU) (hUV)`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor` (×2 sites), `sectionsIdealAux_piece_free`.
- **Visibility**: private.
- **Lines**: 671–683 (13).

## 16. `kerPrincipalAux_le_preimage_basicOpen`
- **Type**: private lemma
- **What**: if `z.appLE V U t = 1` then `U ≤ z ⁻¹ᵁ C.basicOpen t`.
- **How**: germ computation: `Scheme.mem_basicOpen`, `Scheme.Hom.germ_stalkMap_apply`, `TopCat.Presheaf.germ_res_apply`, `isUnit_of_map_unit`.
- **Hypotheses**: `(z) (hUV) (t) (ht : z.appLE V U hUV t = 1)`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 685–702 (18).

## 17. `kerPrincipalAux_preimage_le`
- **Type**: private lemma (`variable (π) in`)
- **What**: `V ≤ π⁻¹U ⟹ z⁻¹V ≤ U` for a section `z`.
- **How**: pointwise, `π.base (z.base s) = s` from `hz`.
- **Hypotheses**: `(z) (hz) (hVU)`.
- **Uses from project**: [].
- **Used by (in file)**: `kerPrincipalAux_ker_app`.
- **Visibility**: private.
- **Lines**: 704–715 (12).

## 18. `kerPrincipalAux_ker_app`
- **Type**: private lemma (`variable (π) in`)
- **What**: `RingHom.ker (z.app V) = RingHom.ker (z.appLE V U)` on a retraction pair.
- **How**: the restriction `homOfLE hUV` is an iso of opens (#17 gives the inverse), so `S.presheaf.map` of it is injective (`ConcreteCategory.bijective_of_isIso`).
- **Hypotheses**: `(z) (hz) (hVU) (hUV)`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor` (×2), `sectionsIdealAux_piece_free`.
- **Visibility**: private.
- **Lines**: 717–732 (16).

## 19. `kerPrincipalAux_stdSmooth_shrink`
- **Type**: private lemma (`variable (π) in`)
- **What**: standard-smoothness (rel. dim. 1) of `π.appLE` survives a simultaneous basic-open shrink `D(g)` / `D(π.appLE g)` of base and total space.
- **How**: `IsAffineOpen.appLE_eq_away_map` + `(RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves 1).away`.
- **Hypotheses**: `(hU₀ hV₀ : IsAffineOpen …) (e₀) (hstd) (g)`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 734–748 (15).

## 20. `kerPrincipalAux_stdSmooth_res`
- **Type**: private lemma (`variable (π) in`)
- **What**: standard-smoothness (rel. dim. 1) survives a basic-open shrink of the source only.
- **How**: factor through `C.presheaf.map` (a dim-0 localization: `RingHom.isStandardSmoothOfRelativeDimension_holdsForLocalizationAway`) and compose via `RingHom.IsStandardSmoothOfRelativeDimension.comp` (1 = 0 + 1).
- **Hypotheses**: `(hV : IsAffineOpen V) (hVU) (hstd) (t)`.
- **Uses from project**: [].
- **Used by (in file)**: `exists_affineOpen_ker_principal_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 750–772 (23).

## 21. `exists_affineOpen_ker_principal_nonZeroDivisor`
- **Type**: theorem
- **What**: **T-D22 = HB-REGIMM (KM 1.2.2 / GME §2.1.4)**: around every `c : C`, the kernel ideal of a section of a smooth separated relative curve is principal on a nonzerodivisor on some affine open `V ∋ c`.
- **How**: case split on `c ∈ support`. Off-section: unit ideal on a small affine via `IsAffineOpen.fromSpec_image_zeroLocus` + `PrimeSpectrum.zeroLocus_empty_iff_eq_top`. On-section: standard-smooth chart from `hsm.exists_isStandardSmoothOfRelativeDimension` (mathlib Morphisms/Smooth); shrink to a retraction pair (#19); algebra heart #12 for `(f₀, r)`; `c ∈ D(r)` via `IsLocalRing.isUnit_or_isUnit_one_sub_self`; kernel dictionary `Scheme.Hom.ker_apply` + #18; ideal transport `Scheme.IdealSheafData.map_ideal_basicOpen` + #14; nonzerodivisor by #13 on the `D(r)`-retraction pair (#20).
- **Hypotheses**: `(π) [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π) (z) (hz) (c : C)`.
- **Uses from project**: [] (all cross-file inputs are mathlib; in-file: #12, #13, #14, #15, #16, #18, #19, #20).
- **Used by (in file)**: `sectionDivisor_isOfficial`, `sectionsIdealAux_exists_multiChart`.
- **Visibility**: public.
- **Lines**: 774–943 (170). **Notes**: proof >30 lines (~162); the T-D22 workhorse.

## 22. `sectionDivisor_isOfficial`
- **Type**: theorem
- **What**: the divisor of a section of a smooth separated relative curve is official Cartier (avoids the general finite-flat⇒Cartier comparison and its sorry'd boxes).
- **How**: package `(sectionDivisor …).flat` with #21.
- **Hypotheses**: `(hsm) [IsSeparated π] (z) (hz)`.
- **Uses from project**: [].
- **Used by (in file)**: none (terminal result / downstream API).
- **Visibility**: public.
- **Lines**: 945–954 (10). **Notes**: sorry-free path to officiality for sections, unlike the general `isOfficial` (#70).

### `sectionsIdealAux` block (958–1507) — register boxes T-D3/T-D1: `Σᵢ[Pᵢ]` is finite locally free of rank `n`

## 23. `sectionsIdealAux_isClosedImmersion`
- **Type**: private lemma
- **What**: a section of a separated morphism is a closed immersion.
- **How**: `IsClosedImmersion.of_comp` applied to `z ≫ π = 𝟙`.
- **Hypotheses**: `[IsSeparated π] (hz)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_support_prod`, `sectionsIdealAux_exists_groupChart`, `sectionsIdealAux_piece_free`, `sectionsIdealAux_exists_chart` (htop'). KEY helper (4 users).
- **Visibility**: private.
- **Lines**: 969–973 (5). **Notes**: duplicates the inline `haveI hzc` idiom used in #5/#6/#7/#21 — intra-file dedup candidate (producer WIP file; leave).

## 24. `sectionsIdealAux_ideal_eq_top_of_disjoint`
- **Type**: private lemma
- **What**: an ideal sheaf evaluates to `⊤` on any affine open disjoint from its support.
- **How**: zeroLocus-empty: `Scheme.IdealSheafData.zeroLocus_inter_subset_supportSet`, `IsAffineOpen.fromSpec_image_zeroLocus`, `PrimeSpectrum.zeroLocus_empty_iff_eq_top`.
- **Hypotheses**: `(I : C.IdealSheafData) (W : C.affineOpens) (h : Disjoint …)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_exists_chart` (htop').
- **Visibility**: private.
- **Lines**: 975–985 (11).

## 25. `sectionsIdealAux_basicOpen_span_nzd`
- **Type**: private lemma
- **What**: "principal on a nonzerodivisor" persists under restriction to an affine basic open.
- **How**: `Scheme.IdealSheafData.map_ideal_basicOpen` + `Ideal.map_span`; nzd side by `IsLocalization.map_nonZeroDivisors_le`.
- **Hypotheses**: `(hspan) (hnzd) (t)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_exists_multiChart` (×2 sites), `sectionsIdealAux_exists_groupChart`, `sectionsIdealAux_exists_chart` (hprin'). KEY helper (3 users).
- **Visibility**: private.
- **Lines**: 987–999 (13).

## 26. `sectionsIdealAux_exists_multiChart`
- **Type**: private lemma
- **What**: multi-section chart: around any `c : C` an affine open on which *every* section kernel in a finite family is principal on a nonzerodivisor.
- **How**: `Finset.induction_on` over the section set; single-section input #21; common refinement `exists_basicOpen_le_affine_inter` (mathlib AffineScheme); restriction stability #25; base case chart from `iSup_affineOpens_eq_top`.
- **Hypotheses**: `(π) [IsSeparated π] (hsm) (P : Fin n → {z // z ≫ π = 𝟙 S}) (c)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_exists_groupChart`.
- **Visibility**: private.
- **Lines**: 1001–1036 (36). **Notes**: proof ~28 lines (just under 30).

## 27. `sectionsIdealAux_ideal_prod`
- **Type**: private lemma
- **What**: `(∏ i ∈ s, I i).ideal U = ∏ i ∈ s, (I i).ideal U` on an affine open.
- **How**: `Finset.induction_on`; `Scheme.IdealSheafData.ideal_mul`, `one_eq_top` (mathlib).
- **Hypotheses**: `(s : Finset ι) (I : ι → C.IdealSheafData) (U : C.affineOpens)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_piece_free`.
- **Visibility**: private.
- **Lines**: 1038–1047 (10).

## 28. `sectionsIdealAux_support_prod`
- **Type**: private lemma
- **What**: support of `∏ᵢ ker(Pᵢ)` = union of the section images.
- **How**: `Finset.induction_on`; `Scheme.IdealSheafData.support_mul`, `Scheme.Hom.support_ker`, closures of closed ranges (`isClosedEmbedding.isClosed_range.closure_eq`).
- **Hypotheses**: `(π) [IsSeparated π] (P)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_exists_chart` (hsupp).
- **Visibility**: private.
- **Lines**: 1049–1069 (21).

## 29. `sectionsIdealAux_free_quotient`
- **Type**: private theorem (equation-compiler recursion on `m`)
- **What**: **KM 1.1.2 filtration, packaged**: nonzerodivisors `f i` each generating the kernel of a retraction `σ i` ⟹ `A ⧸ (∏ f i) ≃ₗ[R] (Fin m → R)` (free of rank `m`).
- **How**: induction on `m` with the SES `0 → A/(t) →(·f₀) A/(f₀t) →(σ₀) R → 0`: injectivity from `f₀` nonzerodivisor, exactness via `LinearMap.exact_iff` + `Ideal.mem_span_singleton'`; splitting by the **project lemma** `Function.Exact.nonempty_linearEquiv_prod_of_projective` (T-D24); reindexing by `LinearEquiv.sumArrowLequivProdArrow` + `finSumFinEquiv`.
- **Hypotheses**: `[CommRing R] [CommRing A] [Algebra R A]`, per-index nzd + kernel-span hypotheses.
- **Uses from project**: `Function.Exact.nonempty_linearEquiv_prod_of_projective` (ForMathlib/FinrankExact).
- **Used by (in file)**: itself (recursion), `sectionsIdealAux_piece_free`.
- **Visibility**: private.
- **Lines**: 1072–1153 (82). **Notes**: proof >30 lines (~72).

## 30. `sectionsIdealAux_base_section`
- **Type**: private lemma
- **What**: `π.base (z.base x) = x` for a section `z`.
- **How**: rewrite `(z ≫ π).base` along `hz`.
- **Hypotheses**: `(π) (hz) (x)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_exists_groupChart`, `sectionsIdealAux_exists_chart` (×3 sites).
- **Visibility**: private.
- **Lines**: 1155–1160 (6). **Notes**: same content as the inline `hπz` in #21 — micro-dedup candidate.

## 31. `sectionsIdealAux_exists_groupChart`
- **Type**: private lemma
- **What**: group chart: around a fibre point `c` over `s`, an affine chart inside `π⁻¹U₀` avoiding all sections not through `c`, on which every section ideal is principal-on-nzd.
- **How**: start from #26; carve the open `Os` = chart ∩ `π⁻¹U₀` ∩ complements of "bad" section images (closed by `isClosedEmbedding.isClosed_range`, via #23); shrink by `IsAffineOpen.exists_basicOpen_le`; restrict principality by #25.
- **Hypotheses**: `(π) [IsSeparated π] (hsm) (P) (U₀ : S.affineOpens) (hs) (c) (hcπ : π.base c = s)`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdealAux_exists_chart`.
- **Visibility**: private.
- **Lines**: 1162–1203 (42). **Notes**: proof >30 lines (~31).

## 32. `sectionsIdealAux_piece_free`
- **Type**: private theorem
- **What**: piece freeness: on an affine `W'` over affine `U` meeting only the sections in `g` (others' ideals = ⊤), the divisor piece's coordinate ring `Γ(C,W')⧸(∏ᵢ ker Pᵢ).ideal W'` is `≃ₗ[Γ(S,U)] (Fin g.card → Γ(S,U))`.
- **How**: bundle each retraction as an `AlgHom` via #15; kernel dictionary #18 + `Scheme.Hom.ker_apply`; product ideal = span of the product of generators (#27, `Ideal.prod_span_singleton`, `Finset.prod_filter_mul_prod_filter_not`); conclude with #29 reindexed along `g.equivFin`.
- **Hypotheses**: `(π) [IsSeparated π] (P) (U) (W') (hVU) (g) (hsec) (hprin) (htop) [alg] (halg)`.
- **Uses from project**: [] directly (via #29: FinrankExact).
- **Used by (in file)**: `sectionsIdealAux_exists_chart`.
- **Visibility**: private.
- **Lines**: 1206–1260 (55). **Notes**: proof >30 lines (~39); takes the algebra structure as an explicit instance argument + compatibility `halg`.

## 33. `sectionsIdealAux_exists_chart`
- **Type**: private theorem
- **What**: **master chart** (local model of KM 1.2.2/1.2.3 for `Σᵢ[Pᵢ]`): every `s : S` has an affine `U` with `q⁻¹U` affine (`q` = subscheme structure map) and `(q.app U).hom` finite + flat + finitely presented of constant `finrank` `n`.
- **How**: 9-step construction. Group charts #31 per point of the finite fibre-image set `G`; base shrink `IsAffineOpen.exists_basicOpen_le`; pieces `K.subschemeι ⁻¹ᵁ W'c` cover `q⁻¹U` (support computation #28) and are pairwise disjoint (section-value argument `hval`); each piece is affine (`Scheme.IdealSheafData.opensRange_subschemeCover_map`), so `q⁻¹U` is affine by `IsAffineOpen.iSup_of_disjoint` (mathlib Limits); per-piece freeness #32 transported along `Scheme.IdealSheafData.subschemeObjIso`; global sections glue to the product by the **project lemma** `TopCat.Sheaf.bijective_restrict_pi_of_pairwise_disjoint`; rank count `Finset.card_eq_sum_card_fiberwise`; conclusions by `RingHom.finite_algebraMap`, `RingHom.flat_algebraMap_iff`, `RingHom.finitePresentation_algebraMap`, `Module.rankAtStalk_eq_finrank_of_free`.
- **Hypotheses**: `(π) [IsSeparated π] (hsm) (P) (s)`.
- **Uses from project**: `TopCat.Sheaf.bijective_restrict_pi_of_pairwise_disjoint` (ForMathlib/SheafDisjointUnion); transitively FinrankExact via #32/#29.
- **Used by (in file)**: `sectionsIdeal_isFinite`, `sectionsIdeal_flat`, `sectionsIdeal_lfp`, `sectionsIdeal_finrank`. KEY internal API (4 users).
- **Visibility**: private.
- **Lines**: 1263–1497 (235). **Notes**: proof >30 lines (~220); second-longest proof in file.

## 34. `sectionsIdealAux_isPullback`
- **Type**: private lemma
- **What**: restriction of `q` over an affine open with affine preimage is a pullback of `Spec.map (q.app U)`.
- **How**: `IsPullback.of_horiz_isIso` with `Scheme.Opens.toSpecΓ_naturality`; both `toSpecΓ` legs are isos via `isoSpec_hom`.
- **Hypotheses**: `(q : X ⟶ S) (U : S.affineOpens) (haff : IsAffineOpen (q ⁻¹ᵁ U))`.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsIdeal_isFinite`, `sectionsIdeal_flat`, `sectionsIdeal_lfp`, `sectionsIdeal_finrank`. KEY internal API (4 users).
- **Visibility**: private.
- **Lines**: 1500–1507 (8).

## 35. `sectionsIdeal_isFinite`
- **Type**: theorem
- **What**: **register box T-D3/T-D1 (KM 1.2.2 + 1.2.3), finiteness**: `(∏ᵢ ker Pᵢ).subschemeι ≫ π` is finite.
- **How**: Zariski-local at target: `IsZariskiLocalAtTarget.of_iSup_eq_top` over the charts of #33; per-chart via `IsFinite.SpecMap_iff` + `MorphismProperty.of_isPullback` (#34).
- **Hypotheses**: `(π) [IsSeparated π] (hsm) (P : Fin n → {z // z ≫ π = 𝟙 S})`.
- **Uses from project**: [] directly (transitively #33).
- **Used by (in file)**: `sectionsDivisor`, `sectionsIdeal_finrank` (×2 sites).
- **Visibility**: public.
- **Lines**: 1510–1533 (24). **Notes**: docstring banks the KM 1.2.3 verbatim quote for T-D3.

## 36. `sectionsIdeal_flat`
- **Type**: theorem
- **What**: register box, flatness leg of #35.
- **How**: identical skeleton with `Flat.SpecMap_iff`.
- **Hypotheses**: as #35.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsDivisor`, `sectionsIdeal_finrank` (×2 sites).
- **Visibility**: public.
- **Lines**: 1535–1550 (16). **Notes**: #35/#36/#37 are triplet-identical proofs modulo the `SpecMap_iff` lemma — decompose/uniformise candidate once file is sorry-free.

## 37. `sectionsIdeal_lfp`
- **Type**: theorem
- **What**: register box, finite-presentation leg of #35.
- **How**: identical skeleton with `LocallyOfFinitePresentation.SpecMap_iff`.
- **Hypotheses**: as #35.
- **Uses from project**: [].
- **Used by (in file)**: `sectionsDivisor`.
- **Visibility**: public.
- **Lines**: 1552–1567 (16).

## 38. `sectionsIdeal_finrank`
- **Type**: theorem
- **What**: **register box T-D3 (KM 1.2.6), degree**: the divisor sum has `finrank = n` at every `s`.
- **How**: transport rank through two pullback squares: `Scheme.Hom.finrank_of_isPullback` (morphismRestrict square, then #34) and `Scheme.Hom.finrank_SpecMap_eq_finrank`; chart rank from #33.
- **Hypotheses**: as #35 plus `(s : S)`; statement carries `haveI := sectionsIdeal_isFinite/flat` (instances inside the statement).
- **Uses from project**: [].
- **Used by (in file)**: `sectionsDivisor_degree`.
- **Visibility**: public.
- **Lines**: 1569–1595 (27). **Notes**: docstring credits the SES splitting to T-D24 (`Function.Exact.nonempty_linearEquiv_prod_of_projective`).

## 39. `sectionsDivisor`
- **Type**: noncomputable def (`open scoped Classical in`)
- **What**: **DS4a/T-D3** — the divisor `Σᵢ [Pᵢ]` as a `RelEffCartierDiv π`: ideal `∏ᵢ ker Pᵢ` when `IsSeparated π ∧ SmoothOfRelativeDimension 1 π` holds (fields by #35/#36/#37), else junk value `⊤` (fields from `IsClosedImmersion.iff_isFinite_and_mono` + instances).
- **How**: `dite` on the bundled hypothesis pair.
- **Hypotheses**: `(π) (P : Fin n → {z // z ≫ π = 𝟙 S})` — deliberately NO instance hypotheses (they are inside the `dite`).
- **Uses from project**: [].
- **Used by (in file)**: `sectionsDivisor_degree`.
- **Visibility**: public.
- **Lines**: 1597–1611 (15). **Notes**: **NO docstring** (only public undocumented decl in the file); junk-value pattern keeps the def total.

## 40. `sectionsDivisor_degree`
- **Type**: theorem
- **What**: **T-D3a, specification of DS4a**: `(sectionsDivisor π P).degree s = n` under KM 1.2.1's standing hypotheses.
- **How**: unfold the `dite` with `dif_pos`; conclude by #38.
- **Hypotheses**: `[IsSeparated π] (hsm) (P) (s)`.
- **Uses from project**: [].
- **Used by (in file)**: none (terminal specification).
- **Visibility**: public.
- **Lines**: 1613–1629 (17). **Notes**: docstring carries the 2026-07-06 ADVERSARIAL FIX record (hypotheses REQUIRED; `Spec k` and nodal counterexamples).

### Base change & flat pullback (1631–1751)

## 41. `baseChange_prop`
- **Type**: private lemma
- **What**: any base-change-stable, iso-respecting `MorphismProperty` holding for `D → S` holds for the base-changed divisor's structure map.
- **How**: paste pullback squares (`IsPullback.paste_vert` of the two `of_hasPullback` squares), `MorphismProperty.of_isPullback`, then cancel the `toImage` iso by `MorphismProperty.cancel_left_of_respectsIso`; ker of a closed immersion rewritten via `Scheme.Hom.toImage_imageι`.
- **Hypotheses**: `(P) [P.IsStableUnderBaseChange] [P.RespectsIso] (D) (t) (hD)`.
- **Uses from project**: [].
- **Used by (in file)**: `baseChange` (×3 fields).
- **Visibility**: private.
- **Lines**: 1631–1653 (23). **Notes**: the docstring block at 1631–1635 (T-D12, KM 1.1) reads as documentation for `baseChange` (#42) but is attached to this private lemma; #42 itself is undocumented — doc-placement nit for cleanup later.

## 42. `baseChange`
- **Type**: noncomputable def
- **What**: base change of a divisor along `t : T ⟶ S` (ideal = kernel of the pulled-back closed immersion `pullback.snd`), a divisor for `pullback.snd π t` (T-D12).
- **How**: three applications of #41 at `@IsFinite`, `@Flat`, `@LocallyOfFinitePresentation`.
- **Hypotheses**: `(D : RelEffCartierDiv π) (t : T ⟶ S)`.
- **Uses from project**: [].
- **Used by (in file)**: `baseChange_ideal`, `baseChange_baseChange_ideal`.
- **Visibility**: public.
- **Lines**: 1655–1660 (6). **Notes**: no docstring of its own (see #41 note).

## 43. `baseChange_ideal`
- **Type**: theorem
- **What**: `(D.baseChange t).ideal = D.ideal.comap (pullback.fst π t)`.
- **How**: swap the pullback legs by `pullbackSymmetry_hom_comp_fst`, then `Scheme.Hom.ker_comp_of_isIso`, `Scheme.IdealSheafData.ker_fst_of_isClosedImmersion`, `ker_subschemeι` (all mathlib IdealSheaf).
- **Hypotheses**: `(D) (t)`.
- **Uses from project**: [].
- **Used by (in file)**: `baseChange_baseChange_ideal`.
- **Visibility**: public.
- **Lines**: 1662–1674 (13).

## 44. `ext`
- **Type**: `@[ext]` theorem
- **What**: divisors with equal ideal sheaves are equal.
- **How**: destructure both; remaining fields are propositional instances, so `rfl` after `obtain rfl`.
- **Hypotheses**: `(h : D₁.ideal = D₂.ideal)`.
- **Uses from project**: [].
- **Used by (in file)**: `flatPullback_id`, `flatPullback_flatPullback`.
- **Visibility**: public.
- **Lines**: 1676–1682 (7).

## 45. `flatPullback_prop`
- **Type**: private lemma
- **What**: analogue of #41 for pullback along an `S`-morphism `f : C' ⟶ C` with `P f`: `P` transfers to the pulled-back divisor over `π'`.
- **How**: `pullback.condition` + `P.comp_mem` with `MorphismProperty.pullback_fst`, then the same toImage-iso cancellation as #41.
- **Hypotheses**: `(P) [IsStableUnderBaseChange] [IsStableUnderComposition] [RespectsIso] (D) (f) (w : f ≫ π = π') (hf : P f) (hD)`.
- **Uses from project**: [].
- **Used by (in file)**: `flatPullback` (×3 fields).
- **Visibility**: private.
- **Lines**: 1684–1699 (16). **Notes**: no docstring.

## 46. `flatPullback`
- **Type**: noncomputable def
- **What**: **KM 1.1.4** — flat pullback `f*(D)` of a divisor along a finite flat finitely-presented `S`-morphism `f : C' ⟶ C`.
- **How**: three applications of #45.
- **Hypotheses**: `(D) (f) (w) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]`.
- **Uses from project**: [].
- **Used by (in file)**: `flatPullback_ideal`, `flatPullback_id`, `flatPullback_flatPullback`. KEY API (3 users).
- **Visibility**: public.
- **Lines**: 1701–1718 (18). **Notes**: docstring documents why finiteness of `f` is needed beyond KM (the `𝔾ₘ ↪ 𝔸¹_{ℤₚ}` / `V(x²−p)` counterexample) — our divisors carry properness.

## 47. `flatPullback_ideal`
- **Type**: theorem
- **What**: `(D.flatPullback f w).ideal = D.ideal.comap f` (KM p. 6).
- **How**: same rewrite chain as #43 (`pullbackSymmetry_hom_comp_fst`, `ker_comp_of_isIso`, `ker_fst_of_isClosedImmersion`, `ker_subschemeι`).
- **Hypotheses**: as #46.
- **Uses from project**: [].
- **Used by (in file)**: `flatPullback_id`, `flatPullback_flatPullback`.
- **Visibility**: public.
- **Lines**: 1720–1733 (14).

## 48. `flatPullback_id`
- **Type**: theorem
- **What**: flat pullback along `𝟙 C` is the identity.
- **How**: #44 + #47 + `Scheme.IdealSheafData.comap_id` (mathlib).
- **Hypotheses**: `(D)`.
- **Uses from project**: [].
- **Used by (in file)**: none (functoriality API for downstream).
- **Visibility**: public.
- **Lines**: 1735–1739 (5).

## 49. `flatPullback_flatPullback`
- **Type**: theorem
- **What**: contravariant composition of flat pullbacks.
- **How**: #44 + #47 (×3) + `Scheme.IdealSheafData.comap_comp` (mathlib).
- **Hypotheses**: two composable pullback data with the six instance hypotheses.
- **Uses from project**: [].
- **Used by (in file)**: none (functoriality API for downstream).
- **Visibility**: public.
- **Lines**: 1741–1751 (11).

### `sliceAux` block (1753–2018) — T-FLAT1-SLICE (EGA IV 11.3.10 slicing criterion)

## 50. `sliceAux_ker_mkₐ`
- **Type**: private theorem
- **What**: `LinearMap.ker (Ideal.Quotient.mkₐ R I).toLinearMap = I.restrictScalars R`.
- **How**: `ext` + `Ideal.Quotient.eq_zero_iff_mem`.
- **Hypotheses**: `(R A) [CommRing …] [Algebra R A] (I)`.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_span_flat`.
- **Visibility**: private.
- **Lines**: 1753–1757 (5).

## 51. `sliceAux_span_flat`
- **Type**: private theorem
- **What**: flat 2-out-of-3 for a principal ideal: `A` `R`-flat and `A⧸(f)` `R`-flat ⟹ `(f)` (as `R`-module) flat.
- **How**: `B ⊗ (f) ↪ B ⊗ A` for all `B` via `LinearMap.lTensor_injective_of_exact_of_flat` on `(f) ↪ A ↠ A⧸(f)` (#50 for the kernel identification); then the naturality square + `Module.Flat.iff_rTensor_preserves_injective_linearMap` and `Function.Injective.of_comp`.
- **Hypotheses**: `[Module.Flat R A] (f) (hq : Module.Flat R (A ⧸ span {f}))`.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_tmul_ann_subsingleton`.
- **Visibility**: private.
- **Lines**: 1759–1788 (30).

## 52. `sliceAux_range_mulLeft`
- **Type**: private theorem
- **What**: `range (LinearMap.mulLeft R f) = (span {f}).restrictScalars R`.
- **How**: `ext` + `Ideal.mem_span_singleton`.
- **Hypotheses**: `(R A) (f)`.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_tmul_ann_subsingleton`.
- **Visibility**: private.
- **Lines**: 1790–1799 (10).

## 53. `sliceAux_tmul_ann_subsingleton`
- **Type**: private theorem
- **What**: **homological input (EGA IV 11.3.8, Tor-free half)**: under #51's hypotheses plus `f` fibrewise-nzd, `K ⊗[R] ker(·f) = 0` for every field `K` over `R`.
- **How**: rTensor of `·f` is injective on `A ⊗ K` from the fibrewise nzd hypothesis (key lemma `mul_left_mem_nonZeroDivisors_eq_zero_iff`); conjugate to lTensor by `TensorProduct.comm`; factor through `μ.rangeRestrict` (range flat by #51+#52); identify `K ⊗ ker` with `ker(K ⊗ ·)` via `LinearMap.kerLTensorEquivOfSurjective` (mathlib Flat/Equalizer) and `LinearMap.ker_rangeRestrict`.
- **Hypotheses**: `[Module.Flat R A] (f) (hq) (hfib : ∀ K field over R, f ⊗ₜ 1 ∈ nonZeroDivisors (A ⊗[R] K))`.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_nzd_of_isNoetherianRing`.
- **Visibility**: private.
- **Lines**: 1801–1855 (55). **Notes**: proof >30 lines (~42).

## 54. `sliceAux_baseChange`
- **Type**: private noncomputable def
- **What**: the canonical surjection `M ⊗[R] N →ₗ[R] M ⊗[A] N` for `A`-modules over an `R`-algebra.
- **How**: `TensorProduct.lift` of the restrict-scalars mk map.
- **Hypotheses**: two `IsScalarTower R A ·` module towers.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_baseChange_surjective`.
- **Visibility**: private.
- **Lines**: 1857–1867 (11).

## 55. `sliceAux_baseChange_surjective`
- **Type**: private theorem
- **What**: #54 is surjective.
- **How**: `TensorProduct.induction_on`.
- **Hypotheses**: as #54.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_ann_subsingleton`.
- **Visibility**: private.
- **Lines**: 1869–1881 (13).

## 56. `sliceAux_ann_subsingleton`
- **Type**: private theorem
- **What**: **support/Nakayama input**: for Noetherian `A`, an ideal `Ann` with `K ⊗[R] Ann = 0` for every field `K` over `R` is zero.
- **How**: `Ann` is `A`-finite; if `Ann ≤ 𝔪` maximal, the fibre `Ann ⧸ 𝔪·Ann` is a quotient of `(A⧸𝔪) ⊗[R] Ann = 0` (surjection #55, `TensorProduct.quotTensorEquivQuotSMul`), so `𝔪 ∉ Supp` — key lemmas `Module.support_quotient`, `Module.mem_support_iff_of_finite`, `Module.support_eq_empty_iff`; contradiction, hence `Supp = ∅`.
- **Hypotheses**: `[IsNoetherianRing A] (Ann) (hI)`.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_nzd_of_isNoetherianRing`.
- **Visibility**: private.
- **Lines**: 1883–1913 (31).

## 57. `sliceAux_nzd_of_isNoetherianRing`
- **Type**: private theorem
- **What**: **T-FLAT1-SLICE at the Noetherian stage (EGA IV 11.3.8)**: slicing nzd criterion for Noetherian `A` — no dévissage.
- **How**: annihilator `ker(·f)` killed on all field fibres by #53; bridge `restrictScalars`; #56 kills it; `LinearMap.ker_eq_bot` gives injectivity of `mulLeft A f`.
- **Hypotheses**: `[Module.Flat R A] [IsNoetherianRing A] (f) (hq) (hfib)`.
- **Uses from project**: [].
- **Used by (in file)**: `sliceAux_nzd_of_noetherianBase`.
- **Visibility**: private.
- **Lines**: 1915–1943 (29).

## 58. `sliceAux_nzd_of_noetherianBase`
- **Type**: private theorem
- **What**: #57 with the noetherianity moved to the base `R` (then `A` is Noetherian).
- **How**: `Algebra.FiniteType.isNoetherianRing` + #57.
- **Hypotheses**: `[Algebra.FinitePresentation R A] [Module.Flat R A] [IsNoetherianRing R] (f) (hq) (hfib)`.
- **Uses from project**: [].
- **Used by (in file)**: `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 1945–1955 (11).

## 59. `sliceAux_exists_noetherianStage` — **CODE-SORRY**
- **Type**: private theorem
- **What**: **[ISOLATED SUB-PIECE — Noetherian approximation, EGA IV 11.2.6 / Stacks 07RF spreading-out]**: descend the whole datum `(A, f, hq, hfib)` to a Noetherian base `R'` with a ring map `ψ : A' → A` lifting every annihilator relation `f·a = 0`.
- **How**: `sorry` (entire proof, term-mode, line 1979). Docstring records that `ModularCurves.exists_noetherian_descent_flat` (ForMathlib/NoethApprox — *not* imported here) provides the flat descent `A ≃ R ⊗[R₀] A₀`; what remains is the *compatible* spreading-out of `hq`/`hfib` plus filtered-colimit descent of the relation — infrastructure mathlib lacks.
- **Hypotheses**: `[Algebra.FinitePresentation R A] [Module.Flat R A] (f) (hq) (hfib)`.
- **Uses from project**: [] in code (docstring cites ForMathlib/NoethApprox).
- **Used by (in file)**: `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor`.
- **Visibility**: private.
- **Lines**: 1957–1979 (23). **Notes**: **CODE-sorry #1 (line 1979) — producer WIP, cleanup-UNTOUCHABLE.**

## 60. `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor`
- **Type**: theorem
- **What**: **[REGISTERED BOX: T-FLAT1-SLICE]** (EGA IV 11.3.10 "critère de platitude par fibres", nzd part): `A` finitely presented flat over `R`, `A⧸(f)` flat, `f` nzd in every field fibre ⟹ `f ∈ nonZeroDivisors A`. Marked *do not use outside `RelEffCartierDiv.isOfficial` without registering the consumer*.
- **How**: obtain the Noetherian stage from #59, apply #58 there, descend the relation `f·x = 0` through `ψ`.
- **Hypotheses**: `[Algebra.FinitePresentation R A] [Module.Flat R A] (f) (hq) (hfib)`.
- **Uses from project**: [].
- **Used by (in file)**: `officialAux_away_nzd`.
- **Visibility**: public.
- **Lines**: 1981–2018 (38). **Notes**: sorry-free itself but **sorry-tainted via #59**; docstring documents why the noetherian-free local form is FALSE (rank-one non-discrete valuation-ring counterexample) — the FP hypotheses are load-bearing.

### `officialAux` block (2020–2694) — KM 1.2.3 (⇐): working divisor ⇒ official Cartier

## 61. `officialAux_flat_ideal_inf_le`
- **Type**: private theorem
- **What**: flatness of `A⧸I` over `R` forces `I ⊓ pA ≤ pA·I` (i.e. `Tor₁ᴿ(A⧸I, R⧸p) = 0`, ≤ direction).
- **How**: tensor-diagram chase: `qq := lid ∘ rTensor p.subtype` injective by `Module.Flat.rTensor_preserves_injective_linearMap`; exactness `lTensor_exact` of `p ⊗ I → p ⊗ A → p ⊗ A/I`; range computation `Ideal.subtype_rTensor_range` (mathlib TensorProduct/Quotient) and `Ideal.smul_top_eq_map`; membership check by `TensorProduct.induction_on`.
- **Hypotheses**: `(I) (hflat : Module.Flat R (A ⧸ I)) (p : Ideal R)`.
- **Uses from project**: [].
- **Used by (in file)**: `officialAux_stalk_span`.
- **Visibility**: private.
- **Lines**: 2020–2088 (69). **Notes**: proof >30 lines (~63).

## 62. `officialAux_exists_mem_fibre_principal`
- **Type**: private theorem
- **What**: fibre principality (wave-2 transport): in `O = A_q ⧸ p·A_q` (DVR-fibre local ring) the ideal `I` becomes principal, generated by the image of some `f ∈ I`.
- **How**: build the fibre curve `κ ⊗[R] A` over `κ = FractionRing (R⧸p)` (finiteness of the quotient via `Algebra.TensorProduct.tensorQuotientEquiv`); κ-algebra structure on `O` by `IsLocalization.lift` at `nonZeroDivisors (R⧸p)`; `Ψ : κ ⊗ A →ₐ[κ] O` via `Algebra.TensorProduct.lift`; apply the **project lemma** `ModularCurves.exists_span_nonZeroDivisor_map_localizationAtPrime` at the prime `q̄ = Ψ⁻¹(𝔪_O)`; transport the span equation along `Ψ̂ = IsLocalization.lift`; descend to a generator in `I` by Nakayama — key lemmas `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`, `Ideal.span_singleton_mul_left_unit`.
- **Hypotheses**: `[IsStandardSmoothOfRelativeDimension 1 R A] (I) (hfin : Module.Finite R (A⧸I)) (q) [q.IsPrime] (hIq)`.
- **Uses from project**: `ModularCurves.exists_span_nonZeroDivisor_map_localizationAtPrime` (ForMathlib/StandardSmoothStalkDVR).
- **Used by (in file)**: `officialAux_stalk_span`.
- **Visibility**: private.
- **Lines**: 2090–2250 (161). **Notes**: proof >30 lines (~145).

## 63. `officialAux_stalk_span`
- **Type**: private theorem
- **What**: **fibre-stalk principality (T-FLAT1 crux)**: for `A` std-smooth of rel. dim. 1, `I` with `A⧸I` flat+finite over `R`, `q ⊇ I` prime: `I·A_q` is principal on the image of some `f ∈ I`.
- **How**: localize #61 via `IsLocalization.map_inf` (mathlib Localization/Ideal) to get `JS ⊓ pS ≤ pS•JS`; combine with the fibre generator from #62; conclude by Nakayama `Submodule.le_of_le_smul_of_le_jacobson_bot` (mod-`𝔪` congruences moved by `Ideal.Quotient.eq_zero_iff_mem`).
- **Hypotheses**: `(I) (hfg : I.FG) (hflat) (hfin) (q) [q.IsPrime] (hIq)`.
- **Uses from project**: [] directly (via #62: StandardSmoothStalkDVR).
- **Used by (in file)**: `officialAux_exists_away_span`.
- **Visibility**: private.
- **Lines**: 2252–2318 (67). **Notes**: proof >30 lines (~54).

## 64. `officialAux_spread`
- **Type**: private theorem
- **What**: spread principality from the stalk `A_q` to a basic open `A[1/r]`, `r ∉ q`.
- **How**: elementary denominator clearing on the finite generating set: `IsLocalization.mk'_surjective`, `IsLocalization.eq_iff_exists`; take `r` = product of the denominators (`Finset.dvd_prod_of_mem`, unit via `isUnit_of_dvd_unit`).
- **Hypotheses**: `(A) (I) (hfg) (f) (hfI) (q) [q.IsPrime] (hq : I·A_q = (f))`.
- **Uses from project**: [].
- **Used by (in file)**: `officialAux_exists_away_span`.
- **Visibility**: private.
- **Lines**: 2320–2380 (61). **Notes**: proof >30 lines (~53); pure commutative algebra, mathlib-able shape.

## 65. `officialAux_finite_quotient_loc`
- **Type**: private theorem
- **What**: a localized quotient of a finite quotient is finite: `B⧸I` finite over field `K`, `S = M⁻¹B` ⟹ `S⧸I·S` finite over `K`.
- **How**: `B⧸I` Artinian (`IsArtinianRing.of_finite`); `IsArtinianRing.localization_surjective` makes `S⧸IS` a quotient; `Module.Finite.trans`.
- **Hypotheses**: `[Field K] (M) (S) [IsLocalization M S] (I) (hfin)`.
- **Uses from project**: [].
- **Used by (in file)**: `officialAux_fibre_nzd`.
- **Visibility**: private.
- **Lines**: 2382–2407 (26). **Notes**: docstring flags it re-derives the `private` `stalkDVRAux_finite_quotient_loc` from ForMathlib/StandardSmoothStalkDVR (not importable because private) — cross-file dedup blocked on visibility; candidate to publicise the ForMathlib one.

## 66. `officialAux_fibre_nzd`
- **Type**: private theorem
- **What**: field-fibre nzd input to the slicing box: the generator's image in `A[1/r] ⊗_R K` is a nonzerodivisor for every field `K` over `R`.
- **How**: `K ⊗ A[1/r]` is a std-smooth curve over `K` (`IsStandardSmoothOfRelativeDimension.trans` + `localization_away`) and a localization of `K ⊗ A` (`IsLocalization.tensorProduct_tensorProduct_right`, mathlib Localization/BaseChange); the quotient by the span is finite over `K` (#65 + `Algebra.TensorProduct.tensorQuotientEquiv`, ideal bookkeeping by `Ideal.map_mapₐ`); conclude with the **project lemma** `ModularCurves.mem_nonZeroDivisors_of_finite_quotient`; transport by `Algebra.TensorProduct.comm`.
- **Hypotheses**: `[IsStandardSmoothOfRelativeDimension 1 R A] (I) (hfin) (f r) (hspan) (K) [Field K] [Algebra R K]`.
- **Uses from project**: `ModularCurves.mem_nonZeroDivisors_of_finite_quotient` (ForMathlib/StandardSmoothStalkDVR).
- **Used by (in file)**: `officialAux_away_nzd`.
- **Visibility**: private.
- **Lines**: 2409–2483 (75). **Notes**: proof >30 lines (~61).

## 67. `officialAux_away_nzd`
- **Type**: private theorem
- **What**: the principal generator's image in `A[1/r]` is a nonzerodivisor, via the registered slicing box.
- **How**: std-smoothness of the away localization gives `FinitePresentation` + `Flat`; quotient flatness via `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` + `Module.Flat.trans`; fibrewise input #66; apply #60.
- **Hypotheses**: `[IsStandardSmoothOfRelativeDimension 1 R A] (I) (hflat) (hfin) (f r) (hspan)`.
- **Uses from project**: [] directly (via #66; box #60).
- **Used by (in file)**: `officialAux_exists_away_span`.
- **Visibility**: private.
- **Lines**: 2485–2525 (41). **Notes**: proof exactly ~30 lines (borderline); **sorry-tainted via #60 ← #59**; this is the registered consumer of box T-FLAT1-SLICE.

## 68. `officialAux_exists_away_span`
- **Type**: private theorem
- **What**: **T-FLAT1-SLICE ideal-theoretic core**: given `I.FG`, `A⧸I` flat+finite, `I ≤ q`, produce `r ∉ q` and `f ∈ I` with `I·A[1/r] = (f)` and `f` nzd in `A[1/r]` — the affine-local input to `isOfficial`.
- **How**: chain #63 (stalk span) → #64 (spread) → #67 (nzd).
- **Hypotheses**: `[IsStandardSmoothOfRelativeDimension 1 R A] (I) (hfg) (hflat) (hfin) (q) [q.IsPrime] (hIq)`.
- **Uses from project**: [] directly.
- **Used by (in file)**: `isOfficial`.
- **Visibility**: private.
- **Lines**: 2527–2543 (17). **Notes**: sorry-tainted via #67.

## 69. `officialAux_exists_finite_chart` — **CODE-SORRY**
- **Type**: private theorem
- **What**: **[ISOLATED SUB-PIECE — finiteness/fibre-isolation input to `isOfficial`]**: around a support point of `D` there is a standard-smooth affine chart `(U₀, V₀)` on which `Γ(C,V₀)⧸I` is a *finite* `Γ(S,U₀)`-module.
- **How**: `sorry` (entire proof, line 2567). Docstring explains this is the one genuinely chart-sensitive input (finiteness is target-local, not source-local; `V(tx−1) ⊆ 𝔸¹` escape-to-infinity counterexample) — needs the KM 1.2.3 fibre-isolation construction (mirrored for sums of sections by #31/#33).
- **Hypotheses**: `(π) [IsSeparated π] (hsm) (D) (c) (hc : c ∈ D.ideal.support)`.
- **Uses from project**: [].
- **Used by (in file)**: `isOfficial`.
- **Visibility**: private.
- **Lines**: 2545–2567 (23). **Notes**: **CODE-sorry #2 (line 2567) — producer WIP, cleanup-UNTOUCHABLE**; statement uses `letI` inside the goal to state module finiteness.

## 70. `isOfficial`
- **Type**: theorem
- **What**: **KM 1.2.3 (⇐), noetherian-free route**: a working (finite locally free) divisor on a smooth separated relative curve is an official Cartier divisor.
- **How**: off-support: unit-ideal chart (zeroLocus-empty, as #21's negative branch, with `PrimeSpectrum.zeroLocus_empty_iff_eq_top`). On-support: finite chart from #69; flatness/finite-presentation of `Γ(C,V₀)⧸I` transported source-locally from `D.flat`/`D.lfp` through `Scheme.IdealSheafData.subschemeObjIso` with `HasRingHomProperty.appLE`; `I.FG` by `Algebra.FinitePresentation.ker_fG_of_surjective`; the point's prime via `IsAffineOpen.primeIdealOf` with `I ≤ q` from support membership; ring core #68 gives `(r, f)`; translate `Localization.Away r` to `Γ(C, D(r))` by `IsLocalization.algEquiv` and `map_ideal_basicOpen`, nzd transported by `MulEquivClass.map_nonZeroDivisors`.
- **Hypotheses**: `(π) [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π) (D : RelEffCartierDiv π)`.
- **Uses from project**: [] directly (transitively: StandardSmoothStalkDVR via #62/#66).
- **Used by (in file)**: none (headline result; downstream consumers).
- **Visibility**: public.
- **Lines**: 2569–2694 (126). **Notes**: proof >30 lines (~120); **sorry-tainted twice** (#69 directly; #59 via #68→#67→#60).

## 71. `baseChange_baseChange_ideal`
- **Type**: theorem
- **What**: iterated base change = base change along the composite, up to `pullbackLeftPullbackSndIso` (ideal-sheaf form).
- **How**: #43 three times + `Scheme.IdealSheafData.comap_comp` + `pullbackLeftPullbackSndIso_hom_fst`.
- **Hypotheses**: `(D) (t : T ⟶ S) (t' : T' ⟶ T)`.
- **Uses from project**: [].
- **Used by (in file)**: none (cocycle API for downstream).
- **Visibility**: public.
- **Lines**: 2696–2704 (9).

### namespace `IsOfficialCartier` (2709–2755) — KM 1.2.3 (⇒)

## 72. `IsOfficialCartier.locallyOfFinitePresentation`
- **Type**: theorem
- **What**: an official divisor on a smooth relative curve has `LocallyOfFinitePresentation (J.subschemeι ≫ π)`.
- **How**: the closed immersion is lfp because its `appLE` on a principal chart is surjective with f.g. kernel — key lemmas `HasRingHomProperty.iff_exists_appLE`, `RingHom.FinitePresentation.of_surjective`, `Scheme.IdealSheafData.ker_subschemeι_app`; then compose with the lfp smooth `π` (`SmoothOfRelativeDimension.smooth`).
- **Hypotheses**: `(hsm) (h : IsOfficialCartier π J)`.
- **Uses from project**: [].
- **Used by (in file)**: `toRelEffCartierDiv`.
- **Visibility**: public.
- **Lines**: 2713–2735 (23).

## 73. `IsOfficialCartier.isFinite` — **CODE-SORRY**
- **Type**: theorem
- **What**: **KM 1.2.3 (⇒)**: an official divisor proper over the base is finite over it (intended route: Zariski's main theorem, proper + locally quasi-finite).
- **How**: `sorry` (entire proof, line 2742).
- **Hypotheses**: `(hsm) (h) [IsProper (J.subschemeι ≫ π)]`.
- **Uses from project**: [].
- **Used by (in file)**: `toRelEffCartierDiv`.
- **Visibility**: public.
- **Lines**: 2737–2742 (6). **Notes**: **CODE-sorry #3 (line 2742) — producer WIP, cleanup-UNTOUCHABLE.**

## 74. `IsOfficialCartier.toRelEffCartierDiv`
- **Type**: noncomputable def
- **What**: **KM 1.2.3 (⇒), packaged**: a proper official divisor as a `RelEffCartierDiv`.
- **How**: fields: `J`, #73, `h.flat`, #72.
- **Hypotheses**: `(hsm) (h) [IsProper (J.subschemeι ≫ π)]`.
- **Uses from project**: [].
- **Used by (in file)**: none (terminal packaging).
- **Visibility**: public.
- **Lines**: 2744–2753 (10). **Notes**: sorry-tainted via #73.

### section `FullSections` (2758–2962) — KM 1.8.2 / 1.9.1 / 1.9.2

## 75. `AlgHom.sectionBaseChange`
- **Type**: noncomputable def
- **What**: base change of a section `P : B →ₐ[R] R` to `A ⊗[R] B →ₐ[A] A`.
- **How**: `(Algebra.TensorProduct.rid R A A).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id A A) P)`.
- **Hypotheses**: `(R B) (A) [CommRing A] [Algebra R A] (P)`.
- **Uses from project**: [].
- **Used by (in file)**: `IsFullSetOfSectionsAlg`, `sectionBaseChange_tensor_map`, `isFullSetOfSectionsAlg_iff_fields`, `IsFullSetOfSectionsCharpoly`, `isFullSetOfSectionsAlg_iff_charpoly`. KEY API (5 users).
- **Visibility**: public.
- **Lines**: 2762–2768 (7). **Notes**: declared as `ModularCurves.AlgHom.sectionBaseChange` — root-namespace-shadowing name (`AlgHom.…` inside `ModularCurves`), naming-audit flag for later cleanup.

## 76. `IsFullSetOfSectionsAlg`
- **Type**: def (Prop)
- **What**: **full set of sections, affine norm form** (KM 1.8.2; universal-norm form of KM 1.9.1): for every `R`-algebra `A` and `f ∈ A ⊗[R] B`, `Norm(f) = ∏ᵢ (Pᵢ)_A(f)`.
- **How**: definition; no proof.
- **Hypotheses**: `[Module.Free R B] [Module.Finite R B] (P : Fin n → (B →ₐ[R] R))`.
- **Uses from project**: [].
- **Used by (in file)**: `isFullSetOfSectionsAlg_iff_fields`, `isFullSetOfSectionsAlg_iff_charpoly`.
- **Visibility**: public.
- **Lines**: 2770–2793 (24). **Notes**: docstring carries the 2026-07-06 ADVERSARIAL FIX record — `[Module.Free] [Module.Finite]` REQUIRED (mathlib `Algebra.norm` is junk without a finite basis; determinant-line counterexample); KM's projective case must go via a trivialising cover (T-D4).

## 77. `eq_of_forall_field_hom_eq`
- **Type**: theorem
- **What**: in a reduced ring, `x = y` as soon as every hom to a field identifies them.
- **How**: difference lies in every prime hence in the nilradical: `nilradical_eq_sInf`, residue-field embedding `IsFractionRing.injective (A₀⧸p) (FractionRing (A₀⧸p))`, then `nilradical_eq_zero` (IsReduced).
- **Hypotheses**: `[CommRing A₀] [IsReduced A₀] (h)`.
- **Uses from project**: [].
- **Used by (in file)**: `isFullSetOfSectionsAlg_iff_fields`.
- **Visibility**: public.
- **Lines**: 2795–2812 (18). **Notes**: general-purpose commutative-algebra fact stated at file level — mathlib-able / relocation candidate.

## 78. `sectionBaseChange_tensor_map`
- **Type**: theorem
- **What**: sections base-change functorially along `ψ : A →ₐ[R] A'`.
- **How**: `TensorProduct` induction; `Algebra.smul_def` on the tmul case.
- **Hypotheses**: `(ψ) (P) (f)`.
- **Uses from project**: [].
- **Used by (in file)**: `isFullSetOfSectionsAlg_iff_fields` (×2 sites), `isFullSetOfSectionsAlg_iff_charpoly`.
- **Visibility**: public.
- **Lines**: 2814–2825 (12).

## 79. `isFullSetOfSectionsAlg_iff_fields`
- **Type**: theorem
- **What**: **T-D2 = KM 1.9.2**: over a *reduced* base, full-set-of-sections need only be checked after base change to every field.
- **How**: reduce to the universal element `f₀ = Σⱼ Xⱼ ⊗ bⱼ` over `A₀ = MvPolynomial ι R` (reduced — instance from `Mathlib.Algebra.MvPolynomial.Nilpotent`): the universal norm identity holds by #77 tested along every field character, using the **project lemma** `norm_tensor_map` and #78; any `(A, f)` is a specialization `φ = MvPolynomial.aeval (coords of f)` (basis `Algebra.TensorProduct.basis`, `bb.sum_repr`), and both sides push forward along `φ` (`norm_tensor_map`, `map_prod`).
- **Hypotheses**: `[IsReduced R] [Module.Free R B] [Module.Finite R B] (P)`.
- **Uses from project**: `norm_tensor_map` (ForMathlib/NormBaseChange).
- **Used by (in file)**: none (terminal result).
- **Visibility**: public.
- **Lines**: 2827–2894 (68). **Notes**: proof >30 lines (~59).

## 80. `IsFullSetOfSectionsCharpoly`
- **Type**: def (Prop)
- **What**: **full set of sections, charpoly form** (KM 1.8.2 form (1)): `charpoly (lmul f) = ∏ᵢ (X − f(Pᵢ))` for all `A`, `f`.
- **How**: definition; no proof.
- **Hypotheses**: `[Module.Free R B] [Module.Finite R B] (P)`.
- **Uses from project**: [].
- **Used by (in file)**: `isFullSetOfSectionsAlg_iff_charpoly`.
- **Visibility**: public.
- **Lines**: 2896–2905 (10).

## 81. `isFullSetOfSectionsAlg_iff_charpoly`
- **Type**: theorem
- **What**: **KM 1.8.2**: norm form ⟺ charpoly form.
- **How**: (⇒) apply the norm identity over `A[X]` to `X ⊗ 1 − 1 ⊗ f` ("T − f"): the **project lemma** `Algebra.charpoly_lmul_eq_norm` (ForMathlib/CharpolyNorm) plus `Algebra.norm_eq_of_algEquiv` along `Algebra.TensorProduct.cancelBaseChange` and #78. (⇐) evaluate at `T = 0`: `LinearMap.det_eq_sign_charpoly_coeff`, `Polynomial.coeff_zero_eq_eval_zero`; the rank is `n` by comparing `natDegree` (`LinearMap.charpoly_natDegree`, `Polynomial.natDegree_prod_of_monic`); sign killed by `Even.neg_one_pow`.
- **Hypotheses**: `[Module.Free R B] [Module.Finite R B] (P)`.
- **Uses from project**: `Algebra.charpoly_lmul_eq_norm` (ForMathlib/CharpolyNorm).
- **Used by (in file)**: none (terminal result).
- **Visibility**: public.
- **Lines**: 2907–2960 (54). **Notes**: proof >30 lines (~45).

---

### File Summary

- **Totals**: **81 declarations** — 4 defs-as-structures/Props (`RelEffCartierDiv`, `IsOfficialCartier`, `IsFullSetOfSectionsAlg`, `IsFullSetOfSectionsCharpoly`), 8 further defs (`degree`, `sectionDivisor`, `sectionsDivisor`, `baseChange`, `flatPullback`, `toRelEffCartierDiv`, `AlgHom.sectionBaseChange`, plus private `kerPrincipalAux_unique_index`, `sliceAux_baseChange`), 69 theorems/lemmas. 2,964 lines. No instances, no `@[simp]` lemmas; one `@[ext]` (`RelEffCartierDiv.ext`), one `@[reducible]` (private `kerPrincipalAux_unique_index`).
- **Private/public counts**: **46 private / 35 public**. Private helpers are cleanly prefix-grouped: `kerPrincipalAux_*` (13), `sectionsIdealAux_*` (12), `sliceAux_*` (10), `officialAux_*` (9), plus `baseChange_prop`, `flatPullback_prop`.
- **Key API (3+ in-file users)**: `RelEffCartierDiv` (+ fields; ~15 users), `IsOfficialCartier` (5), `AlgHom.sectionBaseChange` (5), `flatPullback` (3), and the private hubs `sectionsIdealAux_exists_chart` (4), `sectionsIdealAux_isPullback` (4), `sectionsIdealAux_isClosedImmersion` (4), `sectionsIdealAux_basicOpen_span_nzd` (3). Central 2-user chokepoints worth knowing: `exists_affineOpen_ker_principal_nonZeroDivisor` (T-D22 workhorse feeding both the single-section and multi-section routes) and the registered box `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor` (sole registered consumer: `officialAux_away_nzd`).
- **Unused-in-file (public; presumed downstream/terminal API)**: `ker_sectionBaseChange`, `sectionDivisor_degree`, `sectionDivisor_isOfficial`, `sectionsDivisor_degree`, `flatPullback_id`, `flatPullback_flatPullback`, `isOfficial`, `baseChange_baseChange_ideal`, `IsOfficialCartier.toRelEffCartierDiv`, `isFullSetOfSectionsAlg_iff_fields`, `isFullSetOfSectionsAlg_iff_charpoly`. (In-project downstream importers exist: `EllipticCurve/PoleSheaf.lean`, `LevelStructure/ExactOrder.lean`.) No unused *private* declarations.
- **CODE-sorry list (3 sorry terms — producer WIP, cleanup-UNTOUCHABLE)**:
  1. `RelEffCartierDiv.sliceAux_exists_noetherianStage` (private, line 1979) — Noetherian-approximation spreading-out (EGA IV 11.2.6 / Stacks 07RF); the sole gap in box T-FLAT1-SLICE.
  2. `RelEffCartierDiv.officialAux_exists_finite_chart` (private, line 2567) — fibre-isolation finite chart (KM 1.2.3) feeding `isOfficial`.
  3. `IsOfficialCartier.isFinite` (public, line 2742) — KM 1.2.3 (⇒), proper ⇒ finite via ZMT.
  Sorry-*tainted* closure (sorry-free proofs depending on the above — do not treat as clean targets): `nonZeroDivisor_of_flat_of_fibrewise_nonZeroDivisor`, `officialAux_away_nzd`, `officialAux_exists_away_span`, `RelEffCartierDiv.isOfficial`, `IsOfficialCartier.toRelEffCartierDiv`. Everything else in the file (including the whole T-D22 and T-D3 chains: `exists_affineOpen_ker_principal_nonZeroDivisor`, `sectionDivisor_isOfficial`, `sectionsIdeal_*`, `sectionsDivisor_degree`, `FullSections`) is sorry-free.
- **set_option list**: none in the file.
- **Proofs >30 lines (proof body)**: 17 — `kerPrincipalAux_exists_repr_one` (~47), `kerPrincipalAux_le_span_sup` (~86), `kerPrincipalAux_nzd` (~227, longest), `exists_affineOpen_ker_principal_nonZeroDivisor` (~162), `sectionsIdealAux_free_quotient` (~72), `sectionsIdealAux_exists_groupChart` (~31), `sectionsIdealAux_piece_free` (~39), `sectionsIdealAux_exists_chart` (~220), `sliceAux_tmul_ann_subsingleton` (~42), `officialAux_flat_ideal_inf_le` (~63), `officialAux_exists_mem_fibre_principal` (~145), `officialAux_stalk_span` (~54), `officialAux_spread` (~53), `officialAux_fibre_nzd` (~61), `isOfficial` (~120), `isFullSetOfSectionsAlg_iff_fields` (~59), `isFullSetOfSectionsAlg_iff_charpoly` (~45). Borderline ~28–30: `isPullback_sectionBaseChange`, `sectionsIdealAux_exists_multiChart`, `officialAux_away_nzd`.
- **Uses from project (cross-file)**: exactly six lemmas — `Function.Exact.nonempty_linearEquiv_prod_of_projective` (ForMathlib/FinrankExact, in #29), `TopCat.Sheaf.bijective_restrict_pi_of_pairwise_disjoint` (ForMathlib/SheafDisjointUnion, in #33), `ModularCurves.exists_span_nonZeroDivisor_map_localizationAtPrime` and `ModularCurves.mem_nonZeroDivisors_of_finite_quotient` (ForMathlib/StandardSmoothStalkDVR, in #62/#66), `norm_tensor_map` (ForMathlib/NormBaseChange, in #79), `Algebra.charpoly_lmul_eq_norm` (ForMathlib/CharpolyNorm, in #81). The imports `ModularCurves.EllipticCurve.GroupLaw` and `ModularCurves.ForMathlib.IdealSheafComapMul` contribute **no names** used in this file (verified). `ModularCurves.exists_noetherian_descent_flat` (ForMathlib/NoethApprox) is cited in #59's docstring only, and NoethApprox is not imported.
- **Other observations for later phases** (not actionable while the file carries producer sorries): `sectionsDivisor` (#39) is the only undocumented public decl; #41/#45 docstring placement; `sectionsIdeal_isFinite/flat/lfp` are triplet-identical proofs; the closed-immersion-of-a-section and `π∘z = id` facts are re-proved inline in ~5 places (#23/#30 exist but post-date some call sites); `officialAux_finite_quotient_loc` (#65) duplicates a `private` ForMathlib lemma; `eq_of_forall_field_hom_eq` (#77) is a general reduced-ring fact, mathlib-able. TODO markers: none; two dated ADVERSARIAL FIX records (lines 1616, 2781) document required hypotheses with counterexamples.
