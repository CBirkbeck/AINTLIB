# Inventory — `projects/AdicSpaces/Adic spaces/FarguesFontaine/YStalks.lean`

996 lines. Three namespace blocks: `FarguesFontaine` (lines 27–431), `ValuationSpectrum`
(433–481, two sub-blocks), `FarguesFontaine` again (483–993). Whole file inside
`noncomputable section` (line 25 – line 996).

Imports: `«Adic spaces».FarguesFontaine.YCharts`, `«Adic spaces».StructureSheafStalks`,
`«Adic spaces».RelativeDescentHuber`, `«Adic spaces».FarguesFontaine.ChartVObj`,
`«Adic spaces».SpaQCviaSpvAI`.

Open: `TopologicalRing ValuationSpectrum WittVector NNReal TopologicalSpace CategoryTheory
TopCat AlgebraicGeometry`.

File-level `set_option linter.overlappingInstances false` (line 23) — the only `set_option`
in the file. **No `sorry`, no `admit`, no `maxHeartbeats` bump, no TODO/FIXME.**

Ambient variables (lines 29–32, repeated at 485–488): `(p : ℕ) [Fact p.Prime]`,
`(F : Type*)` a perfectoid field of characteristic `p` (topological / uniform /
nonarchimedean), `(ϖ : PseudoUniformizer F)`. The `ValuationSpectrum` block instead has
`{A : Type*}` a Huber ring with a `PlusSubring`.

Mathematically the file does three things: (i) it discharges Wedhorn 8.14 (stalks of the
ambient structure presheaf are local, with maximal ideal = support of the stalk valuation)
**at every point of 𝒴**, using the fact that 𝒴-interior rational localizations are Tate;
(ii) it packages 𝒴 as a topological space / presheafed space / object `yVPreObj` of Wedhorn's
category 𝒱^pre; (iii) it proves the **𝒴-relative sheaf condition** `isSheafyOn_Y` by covering
any quasi-compact 𝒴-interior rational open by a single "run chart" and transporting the
chart's own sheafiness down through the relative-descent (keystone) machinery.

---

### `instance (anonymous) : HasLocLiftPowerBounded (Ainf p F)`
- **Type**: `noncomputable instance : HasLocLiftPowerBounded (Ainf p F)`
- **What**: Registers the localization-lift power-boundedness package (the "M8" package that makes `restrictionMapHom` and the rational presheaf work) for the ambient, **non-Tate** Huber ring `A_inf = W(𝒪_F)`.
- **How**: Applies the project's `hasLocLiftPowerBounded_Ainf` at the canonical pseudo-uniformizer `IsTateRing.pseudoUniformizer (A := F)` of the perfectoid field; the docstring records that the uniformizer only feeds the ϖ-independent T2/completeness inputs, so the instance is genuinely uniformizer-free.
- **Hypotheses**: `F` a perfectoid field of char `p` (so it is Tate and has a pseudo-uniformizer); `p` prime.
- **Uses from project**: `hasLocLiftPowerBounded_Ainf`, `Ainf`, `HasLocLiftPowerBounded`, `IsTateRing.pseudoUniformizer`
- **Used by**: implicitly by every declaration in the file that mentions `presheafValue`/`restrictionMapHom` over `A_inf` (`rationalShrink_Y`, `stalkShrink_Y`, `IsSheafyOn`, `isSheafyOn_window`, `isSheafyOn_runChart`, `isSheafyOn_Y`, …) — never named explicitly
- **Visibility**: public (anonymous instance)
- **Lines**: 34–38 (term, 3 lines)
- **Notes**: none

### `theorem rationalShrink_Y`
- **Type**: `(D : RationalLocData (Ainf p F)) (hD : D.IsRational) (hDY : rationalOpen D.T D.s ⊆ Y p F ϖ) (v' : Spv (Ainf p F)) (hv : v' ∈ rationalOpen D.T D.s ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) (b : presheafValue D) (hnz : ¬ (pointValue D hv).vle b 0) : ∃ D' hD' (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s), rationalOpen D'.T D'.s ⊆ Y p F ϖ ∧ v' ∈ rationalOpen D'.T D'.s ∧ IsUnit (restrictionMapHom D D' h b)`
- **What**: **The rational-level shrink claim of Wedhorn 8.14 over the non-Tate ambient `A_inf`**: if a section `b` over a 𝒴-interior valid rational `D` has nonzero value at a point `v'`, then `b` becomes a **unit** after restricting to some smaller valid rational neighbourhood `D'` of `v'`, still inside 𝒴.
- **How**: 𝒴-interiority makes `presheafValue D` concretely Tate (`isTateRing_presheafValue_of_rationalOpen_subset_Y`, YB1), so it has a topologically nilpotent unit `u`; `exists_pow_vle_of_isContinuous` gives `k` with `|u^k| ≤ |b|` at the point, and `c := u⁻¹^k · b` then satisfies `|1| ≤ |c|` and `|c| ≠ 0` (both by `Spv.mul_vle_mul_left` bookkeeping). `exists_A_level_open_presentation'` converts the two conditions on `c` into an **`A`-level open `W` ⊆ Spv A** that captures them for every `Spa`-point of `presheafValue D` lying over `W`; the general-Huber rational basis `exists_isRational_spaOpen_subset_huber` produces a valid rational `D'` with `spaOpen D' ⊆ (val ⁻¹' W) ∩ spaOpen D`. Unitness of the restriction is then the complete-pair Nullstellensatz criterion `isUnit_iff_forall_not_vle_zero_of_completePair` at `presheafValue_concretePair D'`: a hypothetical `Spa`-point `w''` of `presheafValue D'` killing `b` pulls back (via `comap_restrictionMapHom_mem_spa` and the triangle `restrictionMapHom ∘ canonicalMap = canonicalMap`, `restrictionMapHom_canonicalMap_generic`) to a point over `W`, where the capture forbids `|c| = 0`, contradicting `|b| = 0`.
- **Hypotheses**: `D` valid rational (`IsRational`), `rationalOpen D ⊆ 𝒴` (this is what supplies Tateness), `v'` a point of the rational open lying in `Spa`, `b` of nonzero point value. `A_inf` affinoid / T2 / right-complete are re-derived inside the proof.
- **Uses from project**: `isAffinoidRing_Ainf`, `t2Space_Ainf`, `completeSpace_right_Ainf`, `isTateRing_presheafValue_of_rationalOpen_subset_Y`, `pointValue_mem_spa`, `pointValue_isContinuous`, `exists_pow_vle_of_isContinuous`, `exists_A_level_open_presentation'`, `comap_pointValue`, `exists_isRational_spaOpen_subset_huber`, `isOpen_spaOpen`, `spaOpen`, `mem_spaOpen`, `spaOpen_subset_iff`, `presheafValue_isHuberRing_huber`, `presheafValue_concretePair`, `presheafValue_isAdicComplete`, `isUnit_iff_forall_not_vle_zero_of_completePair`, `comap_restrictionMapHom_mem_spa`, `comap_canonicalMap_mem_rationalOpen_inter_spa`, `restrictionMapHom_canonicalMap_generic`, `comap_comp`, `restrictionMapHom`, `presheafValue`, `pointValue`, `rationalOpen`, `Y`, `Ainf`, `ringPlus`, `Spa`
- **Used by**: `stalkShrink_Y`
- **Visibility**: public
- **Lines**: 44–138 (statement 44–55, proof 56–138 — **83-line proof**)
- **Notes**: longest proof in the file; no `sorry`, no `set_option`

### `instance (anonymous) : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F))`
- **Type**: `instance : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F))`
- **What**: Instance form of "`(A_inf, A_inf)` is an affinoid (Huber) pair": the plus subring of `A_inf` is a ring of integral elements.
- **How**: Direct restatement of the project theorem `isAffinoidRing_Ainf`.
- **Hypotheses**: `p` prime, `F` perfectoid of char `p`.
- **Uses from project**: `isAffinoidRing_Ainf`, `Ainf`, `ringPlus`
- **Used by**: implicitly by every later declaration whose typeclass context needs `A_inf` to be an affinoid ring (`stalkShrink_Y`, `IsSheafyOn (A := Ainf p F)` in `isSheafyOn_window`/`isSheafyOn_runChart`/`isSheafyOn_Y`)
- **Visibility**: public (anonymous instance)
- **Lines**: 140–143 (term, 1 line)
- **Notes**: declared *after* `rationalShrink_Y`, which therefore re-derives the same fact with a local `haveI`

### `instance (anonymous) : T2Space (Ainf p F)`
- **Type**: `instance : T2Space (Ainf p F)`
- **What**: `A_inf` with its `(p, [ϖ])`-adic topology is Hausdorff.
- **How**: Instantiates the project theorem `t2Space_Ainf` at the canonical pseudo-uniformizer `IsTateRing.pseudoUniformizer (A := F)`, making the statement ϖ-free at instance level.
- **Hypotheses**: `F` perfectoid (hence Tate, so a pseudo-uniformizer exists).
- **Uses from project**: `t2Space_Ainf`, `Ainf`, `IsTateRing.pseudoUniformizer`
- **Used by**: implicitly wherever `Spa`/sheafiness statements over `A_inf` require separation (`stalkShrink_Y`, the three `isSheafyOn_*` theorems)
- **Visibility**: public (anonymous instance)
- **Lines**: 145–147 (term, 1 line)
- **Notes**: none

### `instance (anonymous) : @CompleteSpace (Ainf p F) (IsTopologicalAddGroup.rightUniformSpace (Ainf p F))`
- **Type**: `noncomputable instance : @CompleteSpace (Ainf p F) (IsTopologicalAddGroup.rightUniformSpace (Ainf p F))`
- **What**: `A_inf` is complete for the right uniformity — the completeness input every `IsSheafy`-style statement demands.
- **How**: Instantiates `completeSpace_right_Ainf` (itself derived from `(p,[ϖ])`-adic completeness) at the canonical pseudo-uniformizer.
- **Hypotheses**: `F` perfectoid of char `p`; `p` prime.
- **Uses from project**: `completeSpace_right_Ainf`, `Ainf`, `IsTateRing.pseudoUniformizer`
- **Used by**: implicitly by `IsSheafyOn (A := Ainf p F)` in `isSheafyOn_window`, `isSheafyOn_runChart`, `isSheafyOn_Y`, and by `stalkShrink_Y`
- **Visibility**: public (anonymous instance)
- **Lines**: 149–153 (term, 2 lines)
- **Notes**: uses the explicit `@CompleteSpace … rightUniformSpace` spelling, matching the `IsSheafy` class signature

### `theorem stalkShrink_Y`
- **Type**: `(v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (hvY : (v : Spv (Ainf p F)) ∈ Y p F ϖ) : StalkShrink v`
- **What**: **The stalk shrink claim at 𝒴-points**: every germ at a 𝒴-point whose stalk valuation is nonzero is already a unit in the stalk.
- **How**: Represent the germ as `germ U f` (`Presheaf.exists_germ_eq`); nonvanishing of the stalk value transfers to `openValue U hvU f ≠ 0` (else `germ_zero` would contradict `hx`). Choose a **𝒴-interior** valid rational `E ⊆ U ∩ 𝒴` at `v` by the general-Huber rational basis `exists_isRational_spaOpen_subset_huber` applied to the open set `U ∩ val ⁻¹' 𝒴` (`isOpen_Y`); `comap_limitEvalHom_pointValue` identifies `openValue` with the point value of the evaluation `limitEvalHom i f`, so `rationalShrink_Y` applies and returns a smaller 𝒴-interior rational `D'` on which the evaluation is a unit. Transport back through the ring equivalence `limitEval hD'` (`(limitEval hD').symm_apply_apply`) to see `limitRestrict hW'U f` is a unit in the limit sections, then conclude with `germ_limitRestrict` + `isUnit_germ_of_isUnit`.
- **Hypotheses**: `v ∈ Spa(A_inf, A_inf)` lying in 𝒴 (openness of 𝒴 is what allows the rational refinement to stay 𝒴-interior).
- **Uses from project**: `rationalShrink_Y`, `StalkShrink`, `spaRingPresheaf`, `openValue`, `germ_zero`, `exists_isRational_spaOpen_subset_huber`, `isOpen_Y`, `SpaTop`, `mem_spaOpen`, `spaOpen`, `RationalIndex`, `RationalIndex.self`, `RationalIndex.mono`, `RationalIndex.subset`, `comap_limitEvalHom_pointValue`, `comap_vle`, `pointValue`, `limitEvalHom`, `limitEval`, `limitRestrict`, `spaOpens`, `spaOpen_subset_of_rationalOpen_subset`, `germ_limitRestrict`, `isUnit_germ_of_isUnit`, `restrictionMapHom`, `Y`, `Ainf`, `ringPlus`, `Spa`
- **Used by**: `isLocalRing_stalk_Y`, `maximalIdeal_stalk_Y`
- **Visibility**: public
- **Lines**: 155–216 (statement 158–161, proof 162–216 — **55-line proof**)
- **Notes**: proof >30 lines; contains an explanatory comment ("choose a Y-interior rational index inside `U`")

### `theorem isLocalRing_stalk_Y`
- **Type**: `(v : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) (hvY : (v : Spv (Ainf p F)) ∈ Y p F ϖ) : IsLocalRing (ToType ((spaRingPresheaf (Ainf p F)).stalk v))`
- **What**: **Wedhorn 8.14 at 𝒴-points, unconditional**: the stalk of the ambient structure presheaf at any point of 𝒴 is a local ring.
- **How**: One-line application of the packaged `isLocalRing_stalk_of_shrink` (nonunits = elements of zero stalk value, which are closed under addition by `Spv.vle_add`) to the shrink claim `stalkShrink_Y`.
- **Hypotheses**: `v` a `Spa`-point lying in 𝒴.
- **Uses from project**: `stalkShrink_Y`, `isLocalRing_stalk_of_shrink`, `spaRingPresheaf`, `Y`, `Ainf`, `ringPlus`, `Spa`
- **Used by**: `isLocalRing_yStalk`, `yVPreObj`
- **Visibility**: public
- **Lines**: 218–224 (term, 1 line)
- **Notes**: 1 external consumer (`FarguesFontaine/CurveObject.lean`)

### `theorem maximalIdeal_stalk_Y`
- **Type**: `(v : ↥(Spa …)) (hvY : (v : Spv (Ainf p F)) ∈ Y p F ϖ) : @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk_Y p F ϖ v hvY) = (stalkValue v).supp`
- **What**: **Wedhorn 8.14, maximal-ideal half**: the maximal ideal of the 𝒴-point stalk is exactly the support of the stalk valuation — the `val_supp` datum needed to build a `VPreObj`.
- **How**: Direct application of the packaged `maximalIdeal_stalk_eq_supp` (which identifies nonunits with the support under the shrink claim) to `stalkShrink_Y`.
- **Hypotheses**: `v` a `Spa`-point in 𝒴; the local-ring structure is the one produced by `isLocalRing_stalk_Y`.
- **Uses from project**: `stalkShrink_Y`, `maximalIdeal_stalk_eq_supp`, `isLocalRing_stalk_Y`, `stalkValue`, `Y`, `Ainf`, `ringPlus`, `Spa`
- **Used by**: `yVPreObj`
- **Visibility**: public
- **Lines**: 226–233 (term, 1 line)
- **Notes**: 1 external consumer (`FarguesFontaine/CurveObject.lean`)

### `def ySpaSet`
- **Type**: `ySpaSet (p) (F) (ϖ) : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))`
- **What**: The trace of 𝒴 inside the `Spa`-subspace: the preimage of `Y p F ϖ ⊆ Spv A_inf` under the subtype coercion.
- **How**: `Subtype.val ⁻¹' Y p F ϖ` — 𝒴 is defined as a subset of `Spv`, so working with it as a subspace of `Spa` requires this preimage.
- **Hypotheses**: `F` perfectoid of char `p`; `ϖ` a pseudo-uniformizer.
- **Uses from project**: `Y`, `Ainf`, `ringPlus`, `Spa`
- **Used by**: `yTop`, `ySpaPoint_mem_Y`
- **Visibility**: public
- **Lines**: 235–237 (definition, 1 line)
- **Notes**: 9 external references

### `def yTop`
- **Type**: `yTop (p) (F) (ϖ) : TopCat`
- **What**: **The carrier of 𝒴 as an object of `TopCat`** — the subspace `ySpaSet` of `Spa(A_inf, A_inf)` with the subspace topology.
- **How**: `TopCat.of ↥(ySpaSet p F ϖ)`, i.e. bundle the coercion-to-sort of the subset as a topological space.
- **Hypotheses**: as ambient.
- **Uses from project**: `ySpaSet`
- **Used by**: `yIncl`, `yRingStalkIso`, `ySpaPoint`, `ySpaPoint_mem_Y`, `yRingStalkEquiv`, `isLocalRing_yStalk` (as the type of the point argument)
- **Visibility**: public
- **Lines**: 239–240 (definition, 1 line)
- **Notes**: 207 external references — the most-consumed declaration of the file

### `def yIncl`
- **Type**: `yIncl (p) (F) (ϖ) : yTop p F ϖ ⟶ SpaTop (Ainf p F)`
- **What**: The inclusion morphism of topological spaces `𝒴 ↪ Spa(A_inf, A_inf)`.
- **How**: `TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩` — the subtype coercion, continuous for the subspace topology.
- **Hypotheses**: as ambient.
- **Uses from project**: `yTop`, `SpaTop`, `Ainf`
- **Used by**: `yIncl_isOpenEmbedding`, `ySpaPoint`, `yRingStalkIso` (in its type)
- **Visibility**: public
- **Lines**: 242–244 (definition, 1 line)
- **Notes**: none

### `theorem yIncl_isOpenEmbedding`
- **Type**: `Topology.IsOpenEmbedding (yIncl p F ϖ)`
- **What**: The inclusion `𝒴 ↪ Spa` is an open embedding — i.e. 𝒴 is an **open** subspace, which is what licenses restricting the structure presheaf to it.
- **How**: `isOpen_Y` (openness of the 𝒴-trace, proved in `YSpace.lean` from `Y = Spa ∩ basicOpen (p[ϖ])`) fed to mathlib's `IsOpen.isOpenEmbedding_subtypeVal`.
- **Hypotheses**: openness of 𝒴 in `Spa`, i.e. that 𝒴 is the non-vanishing locus of `p·[ϖ]`.
- **Uses from project**: `isOpen_Y`, `yIncl`
- **Used by**: `yPresheafedSpace`, `yRingStalkIso`
- **Visibility**: public
- **Lines**: 246–249 (term, 1 line)
- **Notes**: 8 external references

### `def yAmbientPresheafedSpace`
- **Type**: `yAmbientPresheafedSpace (p) (F) : TopRingPresheafedSpace`
- **What**: **The ambient `Spa(A_inf, A_inf)` as a presheafed space of complete topological rings** — the general-Huber form of `spaPresheafedSpace`, available because the M8 (`HasLocLiftPowerBounded`) package holds for `A_inf`.
- **How**: Structure literal: carrier `SpaTop (Ainf p F)`, presheaf `structurePresheaf (Ainf p F)` (the bundled `CompleteTopCommRingCat`-valued structure presheaf).
- **Hypotheses**: the `HasLocLiftPowerBounded (Ainf p F)` instance of line 36 (needed for `structurePresheaf` to exist over the non-Tate `A_inf`).
- **Uses from project**: `TopRingPresheafedSpace`, `SpaTop`, `structurePresheaf`, `Ainf`
- **Used by**: `yPresheafedSpace`, `yAmbientRingSpace`, `yRingStalkIso` (in its type)
- **Visibility**: public
- **Lines**: 251–255 (definition, 3 lines)
- **Notes**: does not mention `ϖ` — genuinely uniformizer-free; 28 external references

### `def yPresheafedSpace`
- **Type**: `yPresheafedSpace (p) (F) (ϖ) : TopRingPresheafedSpace`
- **What**: **The 𝒴-presheafed space**: the ambient structure presheaf restricted along the open inclusion `𝒴 ↪ Spa`. This is the underlying presheafed space of the object 𝒴 of 𝒱^pre.
- **How**: mathlib's `PresheafedSpace.restrict` at the open embedding `yIncl_isOpenEmbedding` — pushforward of the presheaf along the open immersion.
- **Hypotheses**: 𝒴 open in `Spa` (`yIncl_isOpenEmbedding`).
- **Uses from project**: `yAmbientPresheafedSpace`, `yIncl_isOpenEmbedding`, `TopRingPresheafedSpace`
- **Used by**: `yRingStalkIso`, `yRingStalkEquiv`, `isLocalRing_yStalk` (all in their types), `yVPreObj`
- **Visibility**: public
- **Lines**: 257–260 (definition, 1 line)
- **Notes**: 74 external references

### `def yAmbientRingSpace`
- **Type**: `yAmbientRingSpace (p) (F) : AlgebraicGeometry.PresheafedSpace CommRingCat`
- **What**: The ambient space with its **underlying ring presheaf** (topology forgotten) as a `CommRingCat`-valued presheafed space — the vehicle for comparing stalks, since mathlib's `restrictStalkIso` lives at that level.
- **How**: Structure literal: same carrier `SpaTop (Ainf p F)`, presheaf `(yAmbientPresheafedSpace p F).ringPresheaf`.
- **Hypotheses**: as for `yAmbientPresheafedSpace`.
- **Uses from project**: `yAmbientPresheafedSpace`, `TopRingPresheafedSpace.ringPresheaf`, `SpaTop`, `Ainf`
- **Used by**: `yRingStalkIso`
- **Visibility**: public
- **Lines**: 262–266 (definition, 3 lines)
- **Notes**: 2 external references

### `def yRingStalkIso`
- **Type**: `yRingStalkIso (p) (F) (ϖ) (x : yTop p F ϖ) : (yPresheafedSpace p F ϖ).ringStalk x ≅ (yAmbientPresheafedSpace p F).ringStalk ((yIncl p F ϖ) x)`
- **What**: **Restricted ring stalks are ambient ring stalks**: the stalk of the restricted presheaf at a 𝒴-point is canonically isomorphic (in `CommRingCat`) to the ambient stalk at the image point.
- **How**: mathlib's `AlgebraicGeometry.PresheafedSpace.restrictStalkIso` at `yAmbientRingSpace` and the open embedding `yIncl_isOpenEmbedding`; the docstring notes the two restricted *ring* presheaves agree by associativity of functor composition (forget ∘ restrict = restrict ∘ forget), which is what makes the types line up.
- **Hypotheses**: `yIncl` an open embedding.
- **Uses from project**: `yAmbientRingSpace`, `yIncl_isOpenEmbedding`, `yPresheafedSpace`, `yAmbientPresheafedSpace`, `yIncl`, `yTop`, `TopRingPresheafedSpace.ringStalk`
- **Used by**: `yRingStalkEquiv`
- **Visibility**: public
- **Lines**: 268–275 (term, 2 lines)
- **Notes**: 7 external references

### `def ySpaPoint`
- **Type**: `ySpaPoint (p) (F) (ϖ) (x : yTop p F ϖ) : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))`
- **What**: The ambient `Spa`-point underlying a point of the 𝒴-carrier.
- **How**: `show … from (ConcreteCategory.hom (yIncl p F ϖ)) x` — deliberately spelled as the **image under the inclusion morphism** (rather than as `x.1`) so that the ambient and restricted stalk types agree definitionally, exactly as `VRestrict.restrictPoint` does in the generic setting.
- **Hypotheses**: as ambient.
- **Uses from project**: `yIncl`, `yTop`, `Spa`, `Ainf`, `ringPlus`
- **Used by**: `ySpaPoint_mem_Y`, `yRingStalkEquiv` (in its type), `isLocalRing_yStalk`, `yVPreObj`
- **Visibility**: public
- **Lines**: 277–282 (definition, 2 lines)
- **Notes**: the "spelled as the inclusion image" trick is load-bearing; 58 external references

### `theorem ySpaPoint_mem_Y`
- **Type**: `(x : yTop p F ϖ) : ((ySpaPoint p F ϖ x : ↥(Spa (Ainf p F) (ringPlus (Ainf p F)))) : Spv (Ainf p F)) ∈ Y p F ϖ`
- **What**: The ambient point of any 𝒴-carrier point really lies in 𝒴.
- **How**: The membership is the defining property `.2` of the subtype element `x : ↥(ySpaSet p F ϖ)`, since `ySpaSet = Subtype.val ⁻¹' Y`.
- **Hypotheses**: none beyond `x` being a point of `yTop`.
- **Uses from project**: `ySpaPoint`, `ySpaSet`, `yTop`, `Y`, `Spa`, `Ainf`, `ringPlus`
- **Used by**: `isLocalRing_yStalk`, `yVPreObj`
- **Visibility**: public
- **Lines**: 284–288 (term, 1 line)
- **Notes**: 4 external references

### `def yRingStalkEquiv`
- **Type**: `yRingStalkEquiv (p) (F) (ϖ) (x : yTop p F ϖ) : ToType ((yPresheafedSpace p F ϖ).ringStalk x) ≃+* ToType ((spaRingPresheaf (Ainf p F)).stalk (ySpaPoint p F ϖ x))`
- **What**: The stalk comparison of `yRingStalkIso` as a bare **ring equivalence** between the 𝒴-stalk and the ambient `spaRingPresheaf` stalk at the corresponding point.
- **How**: `(yRingStalkIso p F ϖ x).commRingCatIsoToRingEquiv` — turn the `CommRingCat`-isomorphism into a `RingEquiv`; the ambient side is definitionally `spaRingPresheaf`'s stalk at `ySpaPoint x` thanks to the `ySpaPoint` spelling.
- **Hypotheses**: as for `yRingStalkIso`.
- **Uses from project**: `yRingStalkIso`, `yPresheafedSpace`, `spaRingPresheaf`, `ySpaPoint`, `yTop`, `Ainf`
- **Used by**: `isLocalRing_yStalk`, `yVPreObj`
- **Visibility**: public
- **Lines**: 290–294 (term, 1 line)
- **Notes**: 15 external references

### `theorem isLocalRing_yStalk`
- **Type**: `(x : yTop p F ϖ) : IsLocalRing (ToType ((yPresheafedSpace p F ϖ).ringStalk x))`
- **What**: **The stalks of the 𝒴-presheafed space are local rings.**
- **How**: Install `isLocalRing_stalk_Y` at the ambient point (legitimate by `ySpaPoint_mem_Y`), then transport along the inverse ring equivalence with mathlib's `RingEquiv.isLocalRing` applied to `(yRingStalkEquiv p F ϖ x).symm`.
- **Hypotheses**: the 𝒴-membership of the ambient point (so Wedhorn 8.14 applies there).
- **Uses from project**: `isLocalRing_stalk_Y`, `ySpaPoint`, `ySpaPoint_mem_Y`, `yRingStalkEquiv`, `yPresheafedSpace`, `spaRingPresheaf`, `yTop`, `Ainf`
- **Used by**: `yVPreObj`
- **Visibility**: public
- **Lines**: 296–303 (proof 5 lines)
- **Notes**: 4 external references

### `def yVPreObj`
- **Type**: `yVPreObj (p) (F) (ϖ) : VPreObj`
- **What**: **𝒴 as an object of Wedhorn's category `𝒱^pre` (Definition 8.5)** — the central definition of the file: the restricted structure presheaf on the open subset 𝒴, together with locality of all stalks and a valuation on each stalk whose support is the maximal ideal.
- **How**: Structure literal over `yPresheafedSpace`: `isLocalRing_stalk := isLocalRing_yStalk`; `val x := comap (yRingStalkEquiv x) (stalkValue (ySpaPoint x))` (pull the ambient stalk valuation back along the stalk comparison); `val_supp` by rewriting with `supp_comap` (support of a pullback = preimage of the support), replacing the ambient support by the ambient maximal ideal via `maximalIdeal_stalk_Y`, and finishing with `IsLocalRing.maximalIdeal_comap` for the *local* ring hom `yRingStalkEquiv` — locality of an isomorphism being mathlib's `isLocalHom_equiv`.
- **Hypotheses**: 𝒴 open in `Spa` and Wedhorn 8.14 available at every 𝒴-point (`isLocalRing_stalk_Y`, `maximalIdeal_stalk_Y`).
- **Uses from project**: `VPreObj`, `yPresheafedSpace`, `isLocalRing_yStalk`, `yRingStalkEquiv`, `stalkValue`, `ySpaPoint`, `ySpaPoint_mem_Y`, `isLocalRing_stalk_Y`, `maximalIdeal_stalk_Y`, `supp_comap`, `comap`, `spaRingPresheaf`, `Ainf`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 305–324 (definition + `val_supp` proof of 11 lines)
- **Notes**: 57 external references across `YSheaf.lean`, `CurveObject.lean`, `CurveAdicSpace.lean`, `CurveChartVIso.lean`, `CurveVMorphism.lean` — the file's headline export. The block `yTop … yVPreObj` closely mirrors the generic `VRestrict.lean` API (`restrictSpace`, `restrictRingStalkIso`, `restrictRingStalkEquiv`, `isLocalRing_restrictStalk`, `VPreObj.restrictOpen`) — a candidate for dedup

### `theorem bigWindow_eq_rationalOpen_windowUnif`
- **Type**: `(n : ℤ) : bigWindow p F ϖ n = rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 p 1).T (chartData p F (windowUnif p F ϖ n) 1 1 p 1).s`
- **What**: **Each Big window is a rational open** — namely the rational open of the `(1,1,p,1)`-chart datum in the window uniformizer, uniformly in `n : ℤ`.
- **How**: `match` on the `Int.ofNat` / `Int.negSucc` constructors, matching the two branches of `windowUnif` (Frobenius root for `n ≥ 0`, `p^{|n|}`-power for `n < 0`); each branch rewrites with the corresponding half `bigWindow_eq_rationalOpen_ofNat` / `bigWindow_eq_rationalOpen_neg` (with `one_lt_p`), after which the chart datum reduces by `rfl`.
- **Hypotheses**: `1 < p` (supplied by `one_lt_p`).
- **Uses from project**: `bigWindow`, `rationalOpen`, `chartData`, `windowUnif`, `bigWindow_eq_rationalOpen_ofNat`, `bigWindow_eq_rationalOpen_neg`, `one_lt_p`
- **Used by**: `isUnit_canonicalMap_p_teichPi_window`, `exists_runChart_superset`
- **Visibility**: public
- **Lines**: 326–339 (proof 8 lines)
- **Notes**: 3 external references

### `theorem isUnit_canonicalMap_p_teichPi_window`
- **Type**: `(n : ℤ) : IsUnit ((chartData p F (windowUnif p F ϖ n) 1 1 p 1).canonicalMap ((p : Ainf p F) * teichPi p F ϖ))`
- **What**: **`p·[ϖ]` maps to a unit of every window chart ring** — the fact that makes the window chart a Tate ring and supplies the span certificates.
- **How**: The complete-pair Nullstellensatz criterion `isUnit_iff_forall_not_vle_zero_of_completePair` at `presheafValue_concretePair`: it suffices that no `Spa`-point `w` of the chart ring kills `p[ϖ]`. Any such `w` pulls back along `canonicalMap` into the chart's rational open (`comap_canonicalMap_mem_rationalOpen`), which is the Big window `n` by `bigWindow_eq_rationalOpen_windowUnif`, hence lies in 𝒴 by the covering `Y_eq_iUnion_bigWindow`; by the definition of 𝒴 the pulled-back valuation does not kill `p[ϖ]`, and `comap_vle` transfers this back to `w`.
- **Hypotheses**: `1 < p` (via `one_lt_p`), `A_inf` affinoid; the chart ring Huber + adically complete at its concrete pair.
- **Uses from project**: `isAffinoidRing_Ainf`, `presheafValue_isHuberRing_huber`, `presheafValue_concretePair`, `presheafValue_isAdicComplete`, `isUnit_iff_forall_not_vle_zero_of_completePair`, `comap_canonicalMap_mem_rationalOpen`, `canonicalMap_continuous`, `bigWindow_eq_rationalOpen_windowUnif`, `bigWindow`, `Y_eq_iUnion_bigWindow`, `one_lt_p`, `comap_vle`, `Y`, `chartData`, `windowUnif`, `teichPi`, `Ainf`, `presheafValue`
- **Used by**: `span_image_windowChart_eq_top`
- **Visibility**: public
- **Lines**: 341–372 (proof 25 lines)
- **Notes**: the docstring calls this "routed through the Spa-point criterion like YB1"

### `theorem span_image_windowChart_eq_top`
- **Type**: `(n : ℤ) [DecidableEq (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1))] (E : RationalLocData (Ainf p F)) (hErat : E.IsRational) : Ideal.span ((E.T.image (chartData …).canonicalMap : Finset _) : Set _) = ⊤`
- **What**: **The image-span certificate at window charts**: for *every* valid rational datum `E` over `A_inf`, the image of its numerator tray `E.T` in the window chart ring generates the unit ideal — the hypothesis the relative-descent (keystone) machinery needs.
- **How**: Validity of `E` means `span E.T` is open, so adicity of `I_inf = (p,[ϖ])` (`isAdic_iff` applied to `isAdic_Iinf`) gives `N` with `I_inf^N ⊆ span E.T`; since `p·[ϖ] ∈ I_inf` (`Ideal.mul_mem_right` on `p ∈ span {p,[ϖ]}`), `(p[ϖ])^N ∈ span E.T`. Writing that membership as a finite combination (`Submodule.mem_span_finset`) and pushing forward with `map_sum` / `Ideal.mul_mem_left` places `(canonicalMap (p[ϖ]))^N` in the image span; it is a unit by `isUnit_canonicalMap_p_teichPi_window`, so `Ideal.eq_top_of_isUnit_mem` finishes.
- **Hypotheses**: `E.IsRational` (openness of `span E.T`) — the only hypothesis on `E`; `p·[ϖ]` invertible in the chart ring.
- **Uses from project**: `isUnit_canonicalMap_p_teichPi_window`, `isAdic_Iinf`, `Iinf`, `teichPi`, `chartData`, `windowUnif`, `presheafValue`, `RationalLocData.IsRational`, `Ainf`
- **Used by**: `windowKeystone`, `isSheafyOn_window`
- **Visibility**: public
- **Lines**: 374–409 (proof 24 lines)
- **Notes**: the `DecidableEq` instance argument is supplied later by the local instance at line 413 (or by `classical`)

### `local instance (anonymous) : DecidableEq (Ainf p F)`
- **Type**: `noncomputable local instance : DecidableEq (Ainf p F)`
- **What**: Classical decidable equality on `A_inf`, so that `Finset.image` and the rational-basis lemmas (`exists_isRational_spaOpen_subset_huber [DecidableEq A]`) elaborate without a `classical` in every statement.
- **How**: `Classical.decEq _`.
- **Hypotheses**: none (classical logic).
- **Uses from project**: `Ainf`
- **Used by**: implicitly, in the statements/elaboration of `windowKeystone` and the `isSheafyOn_*` theorems below it
- **Visibility**: file-local (`local instance`), scoped to the remainder of the section
- **Lines**: 411 (1 line)
- **Notes**: mirrors the same local instance in `ChartData.lean`

### `local instance (anonymous) (n : ℤ) : DecidableEq (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1))`
- **Type**: `noncomputable local instance (n : ℤ) : DecidableEq (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1))`
- **What**: Classical decidable equality on each **window chart ring**, needed to form `E.T.image canonicalMap` and hence `imgDatumO` / the span certificates.
- **How**: `Classical.decEq _`.
- **Hypotheses**: none (classical logic).
- **Uses from project**: `presheafValue`, `chartData`, `windowUnif`
- **Used by**: `windowKeystone` (its `imgDatumO` argument), and the `span_image_windowChart_eq_top` applications inside `isSheafyOn_window`
- **Visibility**: file-local (`local instance`)
- **Lines**: 413–415 (1 line)
- **Notes**: only covers the `(…,1,1,p,1)` window charts; the run charts `(…,1,1,p^{k+1},1)` get theirs from `classical` inside the proofs

### `def windowKeystone`
- **Type**: `windowKeystone (n : ℤ) (E : RationalLocData (Ainf p F)) (hErat : E.IsRational) (hEwin : rationalOpen E.T E.s ⊆ rationalOpen (chartData … ).T (chartData … ).s) : presheafValue E ≃+* presheafValue (imgDatumO (chartData …) E (span_image_windowChart_eq_top p F ϖ n E hErat))`
- **What**: **The window keystone** (Wedhorn Lemma 8.1 / Prop 8.2(2)): the ambient structure-presheaf value on a valid rational `E` inside a Big window is canonically the **window chart's own** structure-presheaf value on the image datum.
- **How**: Instantiates the noetherian-free relative-descent keystone `keystoneO` at `D₀ =` the window chart datum, with the open-span certificate provided by `span_image_windowChart_eq_top`.
- **Hypotheses**: `E` valid rational; `rationalOpen E ⊆` the window chart's rational open; the image-span certificate (automatic here).
- **Uses from project**: `keystoneO`, `imgDatumO`, `span_image_windowChart_eq_top`, `chartData`, `windowUnif`, `presheafValue`, `rationalOpen`, `RationalLocData.IsRational`, `Ainf`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 417–429 (term, 2 lines)
- **Notes**: **0 references anywhere in the project** — genuinely dead code (the sheafiness route goes through `isEmbedding_productRestrictionSub_of_imgCovering` / `exists_glue_of_imgCovering` instead, which apply `keystoneO` internally)

### `structure ValuationSpectrum.IsSheafyOn`
- **Type**: `structure IsSheafyOn (S : Set (Spv A)) [T2Space A] [NonarchimedeanRing A] [CompleteSpace A (right uniformity)] [IsRingOfIntegralElements (A⁺)] : Prop` with fields `embedding` and `gluing`
- **What**: **The subset-relative sheaf condition**: the two `IsSheafy` fields (the product restriction map is a topological embedding; compatible families glue), but demanded **only** for valid rational coverings whose base rational open lies inside the given subset `S ⊆ Spv A`.
- **How**: A `Prop`-valued structure copying the two `IsSheafy` fields verbatim and adding the side condition `rationalOpen C.base.T C.base.s ⊆ S` to each. This is the device that lets a *locally* Tate space like 𝒴 have a sheaf condition even though the ambient `A_inf` is not Tate.
- **Hypotheses**: `A` a Huber ring with a `PlusSubring`, Hausdorff, nonarchimedean, right-complete, with `A⁺` a ring of integral elements — exactly the `IsSheafy` context.
- **Uses from project**: `Spv`, `RationalCoveringData`, `RationalCoveringData.IsRational`, `rationalOpen`, `productRestrictionSub`, `presheafValue`, `restrictionMap`, `RationalLocData`, `ringPlus`, `IsRingOfIntegralElements`
- **Used by**: `isSheafyOn_window`, `isSheafyOn_runChart`, `isSheafyOn_Y` (whose proof uses the fields `.embedding` and `.gluing`)
- **Visibility**: public, namespace `ValuationSpectrum`
- **Lines**: 433–459 (definition, 18 lines of fields)
- **Notes**: 10 external references (`RestrictedLimitSheaf.lean`); an obvious candidate for relocation out of `YStalks.lean` into the generic `ValuationSpectrum` files

### `theorem ValuationSpectrum.isSheafy_congr_plusSubring`
- **Type**: `{A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [T2Space A] [NonarchimedeanRing A] [hc : CompleteSpace A (right)] (inst₁ inst₂ : PlusSubring A) (h : inst₁ = inst₂) (hint₁ …) (hint₂ …) (hs : @IsSheafy A _ _ _ inst₁ _ _ _ hc hint₁) : @IsSheafy A _ _ _ inst₂ _ _ _ hc hint₂`
- **What**: **`IsSheafy` transports across an equality of `PlusSubring` instances** — the bridge from the chart's transported `B^{I,+}`-plus structure to the canonical `completedPlusSubring`-based one.
- **How**: `subst h` then `exact hs`: `PlusSubring` is the only *data*-valued instance in the `IsSheafy` signature (all the others are `Prop`-classes and transport by proof irrelevance), so substituting the equality suffices — including for the `IsRingOfIntegralElements` argument, which is a `Prop`.
- **Hypotheses**: the two plus-subring instances are literally equal; the ambient Huber/T2/nonarchimedean/completeness data is shared.
- **Uses from project**: `IsSheafy`, `PlusSubring`, `ringPlus`, `IsRingOfIntegralElements`
- **Used by**: `isSheafy_canonical_window`, `isSheafy_canonical_runChart`
- **Visibility**: public, namespace `ValuationSpectrum` (own `universe u` block)
- **Lines**: 461–481 (proof 2 lines)
- **Notes**: like `IsSheafyOn`, this is generic infrastructure sitting in a Fargues–Fontaine file

### `theorem window_hexact2`
- **Type**: `(n : ℤ) : (rhoRight p F (windowUnif p F ϖ n) p 1) ^ p = perfectoidValuation p F ((PseudoUniformizer.toOF F (windowUnif p F ϖ n) : OF F) : F) ^ 1`
- **What**: **The window-chart exactness datum**, packaged: the right-hand radius `ρ₂` of the `(a,b) = (p,1)` window chart satisfies `ρ₂^p = |ϖ_n|^1` exactly.
- **How**: One application of `rhoRight_pow_exact` at `(a, b) = (p, 1)`, whose side condition `0 < a` is `Nat.Prime.pos`.
- **Hypotheses**: `p` prime (so `0 < p`).
- **Uses from project**: `rhoRight`, `rhoRight_pow_exact`, `windowUnif`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `isSheafy_canonical_window`
- **Visibility**: public
- **Lines**: 490–496 (proof 2 lines)
- **Notes**: 4 external references

### `theorem chartPlus_instance_eq_canonical`
- **Type**: `{ρ₁ ρ₂ : NNReal} {hρ₁0 …} (a : ℕ) (ha : 0 < a) (hexact1 : perfectoidValuation p F (ϖ : F) = ρ₁) (hexact2 : ρ₂ ^ a = perfectoidValuation p F (ϖ : F) ^ 1) : chartPlus p F ϖ … a 1 ha one_pos ha hexact1 hexact2 = RationalLocData.presheafValuePlusSubring (chartData p F ϖ 1 1 a 1)`
- **What**: **Instance-level plus reconciliation**: the transported (`B^I`-ball) `PlusSubring` instance of an `(a,1)`-chart *equals*, as an instance, the canonical `completedPlusSubring`-based one.
- **How**: `congrArg ValuationSpectrum.PlusSubring.mk` applied to the subring-level equality `chartPlus_eq_canonical` (r5c reconciliation) — since `PlusSubring` is a one-field structure, equality of the carrier subrings upgrades to equality of instances.
- **Hypotheses**: `0 < a`; the two exactness conditions `hexact1`, `hexact2` relating the chart radii to the perfectoid valuation of `ϖ`; the radii strictly between 0 and 1.
- **Uses from project**: `chartPlus`, `chartPlus_eq_canonical`, `RationalLocData.presheafValuePlusSubring`, `chartData`, `PlusSubring`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `isSheafy_canonical_window`, `isSheafy_canonical_runChart`
- **Visibility**: public
- **Lines**: 498–513 (term, 3 lines)
- **Notes**: all the `ρ`-positivity/`<1` arguments are *implicit* (`{hρ₁0 …}`), so callers pass them by unification

### `theorem isSheafy_canonical_window`
- **Type**: `(n : ℤ) : letI … ; ValuationSpectrum.IsSheafy (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 p 1))` (stated with `letI`-installed Huber and right-completeness instances)
- **What**: **YB6c-3c′ — the window chart ring is sheafy at the *canonical* instances**: `IsSheafy` for the window chart ring with the canonical `completedPlusSubring`-based plus subring, its own Tate–Huber structure, and the canonical ring-of-integral-elements instance — the exact form that the single-`D₀` relative-descent transports consume.
- **How**: Obtain sheafiness in the *transported* plus structure from `isSheafy_presheafChart` at `(a,b) = (p,1)` (feeding it `vpi_pos`, `perfectoidValuation_toOF_lt_one`, `rhoRight_pos`, `rhoRight_lt_one` and the exactness datum `window_hexact2`), then move it across the plus-instance equality `chartPlus_instance_eq_canonical` using `isSheafy_congr_plusSubring`.
- **Hypotheses**: `1 < p` (`one_lt_p`); the chart-radius exactness `window_hexact2`; the chart being a `(p,1)`-chart in the window uniformizer.
- **Uses from project**: `isSheafy_presheafChart`, `isSheafy_congr_plusSubring`, `chartPlus_instance_eq_canonical`, `window_hexact2`, `one_lt_p`, `vpi_pos`, `perfectoidValuation_toOF_lt_one`, `rhoRight_pos`, `rhoRight_lt_one`, `isTateRing_bigWindowChart`, `completeSpace_right_presheafValue`, `IsSheafy`, `chartData`, `windowUnif`, `presheafValue`
- **Used by**: `isSheafyOn_window`
- **Visibility**: public
- **Lines**: 515–542 (proof 11 lines)
- **Notes**: statement uses two `letI`s to fix which Huber / completeness instances the conclusion is about; 1 external reference (`CurveAdicPresentation.lean`)

### `theorem isSheafyOn_window`
- **Type**: `(n : ℤ) : ValuationSpectrum.IsSheafyOn (A := Ainf p F) (rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 p 1).T (chartData …).s)`
- **What**: **YB6c-3c′ assembled — the single-window sheaf condition over the ambient `A_inf`**: every valid rational covering whose base lies inside a Big window satisfies both sheaf axioms.
- **How**: Install the chart's Tate/Huber/completeness instances plus `isSheafy_canonical_window`, then discharge the two `IsSheafyOn` fields by the single-`D₀` relative-descent transports `isEmbedding_productRestrictionSub_of_imgCovering` and `exists_glue_of_imgCovering` at `D₀ =` the window chart datum, whose "certificate for every valid rational" hypothesis is exactly `span_image_windowChart_eq_top`.
- **Hypotheses**: the chart ring is Tate (`isTateRing_bigWindowChart`), right-complete, and sheafy at the canonical instances; the image-span certificate holds for every valid rational datum.
- **Uses from project**: `IsSheafyOn`, `isTateRing_bigWindowChart`, `completeSpace_right_presheafValue`, `isSheafy_canonical_window`, `isEmbedding_productRestrictionSub_of_imgCovering`, `exists_glue_of_imgCovering`, `span_image_windowChart_eq_top`, `chartData`, `windowUnif`, `presheafValue`, `rationalOpen`, `Ainf`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 544–577 (proof 25 lines)
- **Notes**: **0 external references** — superseded by `isSheafyOn_runChart`, which is the same statement at `a = p^{k+1}`; dead code

### `def runWindow`
- **Type**: `runWindow (p) (F) (ϖ) (n : ℤ) (k : ℕ) : Set (Spv (Ainf p F))`
- **What**: **The run window** `{v ∈ 𝒴 : p^n ≤ κ(v) ≤ p^{n+k+1}}` — the union of the `k+1` adjacent Big windows starting at `n`, i.e. a "thick" window that can swallow any quasi-compact 𝒴-interior subset.
- **How**: Set-builder: points of `Y p F ϖ` satisfying `KGE (p^n)` and `KLE (p^{n+k+1})` (the denominator-cleared forms of `κ(v) ≥ p^n`, `κ(v) ≤ p^{n+k+1}`).
- **Hypotheses**: as ambient; `n : ℤ`, `k : ℕ`.
- **Uses from project**: `Y`, `KGE`, `KLE`, `Ainf`, `Spv`
- **Used by**: `runWindow_eq_rationalOpen_ofNat`, `runWindow_eq_rationalOpen_neg`, `runWindow_eq_rationalOpen`, `runWindow_subset_Y`, `bigWindow_subset_runWindow`
- **Visibility**: public
- **Lines**: 579–583 (definition, 2 lines)
- **Notes**: 0 external references (used only inside this file)

### `theorem runWindow_eq_rationalOpen_ofNat`
- **Type**: `(n k : ℕ) (hp : 1 < p) : runWindow p F ϖ (n : ℤ) k = rationalOpen (chartT p F (PseudoUniformizer.frobRoot p F ϖ n) (p ^ (k + 1)) 1) (chartS p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1)`
- **What**: **The run window is a rational open (nonnegative side)**: for `n ≥ 0` it is the rational open of the `(p^{k+1}, 1)`-chart in the `p^n`-th Frobenius root uniformizer — the generalisation of `bigWindow_eq_rationalOpen_ofNat` from `a = p` to `a = p^{k+1}`.
- **How**: Change uniformizer to `ϖ' = frobRoot ϖ n`, using `teichPi_frobRoot_pow` (`[ϖ']^{p^n} = [ϖ]`) and `Y_eq_of_teichPi_pow` (𝒴 is unchanged). Then `mem_rationalOpen_chartData_iff` converts membership in the chart's rational open into `v ∈ 𝒴 ∧ v([ϖ']) ≤ v(1) ∧ v(p^{p^{k+1}}) ≤ v([ϖ'])`-style raw inequalities, and `KGE_iff` / `KLE_iff` (at the fraction presentations `p^n = p^n/1` and `p^{n+k+1} = p^{n+k+1}/1`) convert the run-window conditions into the same shape; `vle_pow_iff` moves between `[ϖ]`- and `[ϖ']`-powers, and `pow_add` bookkeeping (`p^{k+1}·p^n = p^{n+k+1}`) matches the two exponents.
- **Hypotheses**: `1 < p`; `n, k : ℕ` (nonnegative index).
- **Uses from project**: `runWindow`, `rationalOpen`, `chartT`, `chartS`, `PseudoUniformizer.frobRoot`, `teichPi`, `teichPi_frobRoot_pow`, `Y`, `Y_eq_of_teichPi_pow`, `mem_rationalOpen_chartData_iff`, `KGE_iff`, `KLE_iff`, `vle_pow_iff`, `Ainf`
- **Used by**: `runWindow_eq_rationalOpen`
- **Visibility**: public
- **Lines**: 585–649 (proof **61 lines**)
- **Notes**: proof >30 lines; `hp : 1 < p` is passed but only used through the positivity casts

### `theorem runWindow_eq_rationalOpen_neg`
- **Type**: `(m k : ℕ) (hp : 1 < p) : runWindow p F ϖ (-(m : ℤ)) k = rationalOpen (chartT p F (PseudoUniformizer.pPow F ϖ (p ^ m) …) (p ^ (k + 1)) 1) (chartS p F (PseudoUniformizer.pPow F ϖ (p ^ m) …) 1 1)`
- **What**: **The run window is a rational open (negative side)**: for index `-m` it is the rational open of the `(p^{k+1},1)`-chart in the `p^m`-th *power* uniformizer.
- **How**: Same skeleton as the nonnegative case with `ϖ' = pPow ϖ (p^m)`: `teichPi_pPow` gives `[ϖ'] = [ϖ]^{p^m}` and `Y_eq_of_teichPi_pow` again identifies the 𝒴's; `mem_rationalOpen_chartData_iff` unfolds the chart membership, and `KGE_iff`/`KLE_iff` are applied at the fraction presentations `p^{-m} = 1/p^m` and `p^{-m+k+1} = p^{k+1}/p^m` (obtained by `zpow_neg`, `zpow_sub₀`), after which both sides match on the nose.
- **Hypotheses**: `1 < p`; `m, k : ℕ`.
- **Uses from project**: `runWindow`, `rationalOpen`, `chartT`, `chartS`, `PseudoUniformizer.pPow`, `teichPi`, `teichPi_pPow`, `Y`, `Y_eq_of_teichPi_pow`, `mem_rationalOpen_chartData_iff`, `KGE_iff`, `KLE_iff`, `Ainf`
- **Used by**: `runWindow_eq_rationalOpen`
- **Visibility**: public
- **Lines**: 651–707 (proof **54 lines**)
- **Notes**: proof >30 lines; unlike the `ofNat` case, no `vle_pow_iff` is needed (the powers already sit on the correct side)

### `theorem runWindow_eq_rationalOpen`
- **Type**: `(n : ℤ) (k : ℕ) : runWindow p F ϖ n k = rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).T (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).s`
- **What**: **The run window is the rational open of the `(p^{k+1},1)`-window-chart datum, uniformly in `n : ℤ`** — the run-chart analogue of `bigWindow_eq_rationalOpen_windowUnif`.
- **How**: `match` on `Int.ofNat` / `Int.negSucc`, matching the two branches of `windowUnif`, and rewrite by `runWindow_eq_rationalOpen_ofNat` resp. `runWindow_eq_rationalOpen_neg` (with `one_lt_p`); the chart datum then reduces to `chartT`/`chartS` by `rfl`.
- **Hypotheses**: `1 < p` (via `one_lt_p`).
- **Uses from project**: `runWindow`, `runWindow_eq_rationalOpen_ofNat`, `runWindow_eq_rationalOpen_neg`, `rationalOpen`, `chartData`, `windowUnif`, `one_lt_p`
- **Used by**: `isUnit_canonicalMap_p_teichPi_runChart`, `exists_runChart_superset`
- **Visibility**: public
- **Lines**: 709–724 (proof 9 lines)
- **Notes**: none

### `theorem runWindow_subset_Y`
- **Type**: `(n : ℤ) (k : ℕ) : runWindow p F ϖ n k ⊆ Y p F ϖ`
- **What**: Run windows lie inside 𝒴.
- **How**: Projection `fun _ hv => hv.1` — membership in `runWindow` is by definition a conjunction whose first component is membership in `Y`.
- **Hypotheses**: none.
- **Uses from project**: `runWindow`, `Y`
- **Used by**: `isUnit_canonicalMap_p_teichPi_runChart`
- **Visibility**: public
- **Lines**: 726–729 (term, 1 line)
- **Notes**: none

### `theorem bigWindow_subset_runWindow`
- **Type**: `(n : ℤ) (k : ℕ) {j : ℤ} (hj1 : n ≤ j) (hj2 : j ≤ n + k) : bigWindow p F ϖ j ⊆ runWindow p F ϖ n k`
- **What**: **Each Big window of the run lies in the run window**: for `n ≤ j ≤ n + k`, `bigWindow j ⊆ runWindow n k`.
- **How**: Unpack a point of `bigWindow j` as `⟨hY, κ ≥ p^j, κ ≤ p^{j+1}⟩` and weaken both bounds with the monotonicity lemmas `KGE_mono` (from `p^n ≤ p^j`) and `KLE_mono` (from `p^{j+1} ≤ p^{n+k+1}`), the numeric comparisons being `zpow_le_zpow_right₀` for base `p > 1` plus `omega`.
- **Hypotheses**: `n ≤ j ≤ n + k`; `1 < p` (obtained by casting `Nat.Prime.one_lt`).
- **Uses from project**: `bigWindow`, `runWindow`, `KGE_mono`, `KLE_mono`, `Y`
- **Used by**: `exists_runChart_superset`
- **Visibility**: public
- **Lines**: 731–743 (proof 9 lines)
- **Notes**: none

### `theorem isUnit_canonicalMap_p_teichPi_runChart`
- **Type**: `(n : ℤ) (k : ℕ) : IsUnit ((chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).canonicalMap ((p : Ainf p F) * teichPi p F ϖ))`
- **What**: **`p·[ϖ]` maps to a unit of every run chart ring** — the run-chart analogue of `isUnit_canonicalMap_p_teichPi_window`.
- **How**: Identical route: `isUnit_iff_forall_not_vle_zero_of_completePair` at `presheafValue_concretePair` reduces to showing no `Spa`-point of the run chart ring kills `p[ϖ]`; such a point pulls back into the chart's rational open (`comap_canonicalMap_mem_rationalOpen`), which is the run window by `runWindow_eq_rationalOpen`, hence lies in 𝒴 by `runWindow_subset_Y`, where `p[ϖ]` is nonzero by definition of 𝒴; `comap_vle` transports the contradiction back.
- **Hypotheses**: `A_inf` affinoid; run chart ring Huber and adically complete at its concrete pair.
- **Uses from project**: `isAffinoidRing_Ainf`, `presheafValue_isHuberRing_huber`, `presheafValue_concretePair`, `presheafValue_isAdicComplete`, `isUnit_iff_forall_not_vle_zero_of_completePair`, `comap_canonicalMap_mem_rationalOpen`, `canonicalMap_continuous`, `runWindow_subset_Y`, `runWindow_eq_rationalOpen`, `comap_vle`, `Y`, `chartData`, `windowUnif`, `teichPi`, `presheafValue`, `Ainf`
- **Used by**: `span_image_runChart_eq_top`
- **Visibility**: public
- **Lines**: 745–770 (proof 21 lines)
- **Notes**: near-verbatim copy of `isUnit_canonicalMap_p_teichPi_window` with `p ↦ p^{k+1}` — dedup candidate

### `theorem span_image_runChart_eq_top`
- **Type**: `(n : ℤ) (k : ℕ) [DecidableEq (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))] (E : RationalLocData (Ainf p F)) (hErat : E.IsRational) : Ideal.span ((E.T.image (chartData …).canonicalMap : Finset _) : Set _) = ⊤`
- **What**: **The image-span certificate at run charts**: every valid rational datum's numerator tray spans the unit ideal after mapping into a run chart ring.
- **How**: As in the window case — adicity of `I_inf` (`isAdic_Iinf` via `isAdic_iff`) and openness of `span E.T` give `N` with `(p[ϖ])^N ∈ span E.T`; expanding that as a finite `Submodule.mem_span_finset` combination and pushing through `canonicalMap` (`map_sum`, `Ideal.mul_mem_left`) puts a unit power (`isUnit_canonicalMap_p_teichPi_runChart`) inside the image span, so `Ideal.eq_top_of_isUnit_mem` applies.
- **Hypotheses**: `E.IsRational`; `p·[ϖ]` a unit in the run chart ring.
- **Uses from project**: `isUnit_canonicalMap_p_teichPi_runChart`, `isAdic_Iinf`, `Iinf`, `teichPi`, `chartData`, `windowUnif`, `presheafValue`, `RationalLocData.IsRational`, `Ainf`
- **Used by**: `isSheafyOn_runChart`
- **Visibility**: public
- **Lines**: 772–812 (proof 28 lines)
- **Notes**: near-verbatim copy of `span_image_windowChart_eq_top` — dedup candidate

### `theorem run_hexact2`
- **Type**: `(n : ℤ) (k : ℕ) : (rhoRight p F (windowUnif p F ϖ n) (p ^ (k + 1)) 1) ^ (p ^ (k + 1)) = perfectoidValuation p F ((PseudoUniformizer.toOF F (windowUnif p F ϖ n) : OF F) : F) ^ 1`
- **What**: **The run-chart exactness datum**, packaged: `ρ₂^{p^{k+1}} = |ϖ_n|^1` for the `(p^{k+1},1)`-chart.
- **How**: `rhoRight_pow_exact` at `(a,b) = (p^{k+1}, 1)`, whose positivity side condition is `pow_pos (Nat.Prime.pos …)`.
- **Hypotheses**: `p` prime (so `0 < p^{k+1}`).
- **Uses from project**: `rhoRight`, `rhoRight_pow_exact`, `windowUnif`, `perfectoidValuation`, `PseudoUniformizer.toOF`, `OF`
- **Used by**: `isTateRing_runChart`, `isSheafy_canonical_runChart`
- **Visibility**: public
- **Lines**: 814–820 (proof 2 lines)
- **Notes**: none

### `theorem isTateRing_runChart`
- **Type**: `(n : ℤ) (k : ℕ) : IsTateRing (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))`
- **What**: **The run chart ring is Tate** — the analogue of `isTateRing_bigWindowChart` at `(a,b) = (p^{k+1}, 1)`.
- **How**: Apply the general chart-Tateness theorem `isTateRing_presheafChart` with the radius data `vpi_pos`, `perfectoidValuation_toOF_lt_one`, `rhoRight_pos`, `rhoRight_lt_one` at `a = p^{k+1}, b = 1`, and the exactness input rewritten from `run_hexact2` (killing the `^1` with `pow_one`).
- **Hypotheses**: `1 < p`, `0 < p^{k+1}`; the chart radii strictly inside `(0,1)` and exact.
- **Uses from project**: `isTateRing_presheafChart`, `run_hexact2`, `one_lt_p`, `vpi_pos`, `perfectoidValuation_toOF_lt_one`, `rhoRight_pos`, `rhoRight_lt_one`, `chartData`, `windowUnif`, `presheafValue`
- **Used by**: `isSheafy_canonical_runChart`, `isSheafyOn_runChart`
- **Visibility**: public
- **Lines**: 822–836 (proof 10 lines)
- **Notes**: none

### `theorem isSheafy_canonical_runChart`
- **Type**: `(n : ℤ) (k : ℕ) : letI … ; ValuationSpectrum.IsSheafy (presheafValue (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1))`
- **What**: **The run chart ring is sheafy at the canonical instances** — the run-chart form of `isSheafy_canonical_window`, i.e. `IsSheafy` with the canonical `completedPlusSubring`-based plus structure.
- **How**: `isSheafy_presheafChart` at `(a,b) = (p^{k+1},1)` (fed the same radius package plus `run_hexact2`), then transported across the plus-instance equality `chartPlus_instance_eq_canonical` by `isSheafy_congr_plusSubring`.
- **Hypotheses**: `1 < p`, `0 < p^{k+1}`, chart exactness `run_hexact2`; Huber structure from `isTateRing_runChart` and right-completeness from `completeSpace_right_presheafValue`.
- **Uses from project**: `isSheafy_presheafChart`, `isSheafy_congr_plusSubring`, `chartPlus_instance_eq_canonical`, `run_hexact2`, `isTateRing_runChart`, `completeSpace_right_presheafValue`, `one_lt_p`, `vpi_pos`, `perfectoidValuation_toOF_lt_one`, `rhoRight_pos`, `rhoRight_lt_one`, `IsSheafy`, `chartData`, `windowUnif`, `presheafValue`
- **Used by**: `isSheafyOn_runChart`
- **Visibility**: public
- **Lines**: 838–864 (proof 13 lines)
- **Notes**: none

### `theorem isSheafyOn_runChart`
- **Type**: `(n : ℤ) (k : ℕ) : ValuationSpectrum.IsSheafyOn (A := Ainf p F) (rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).T (chartData …).s)`
- **What**: **The run-window sheaf condition over the ambient `A_inf`**: both sheaf axioms hold for every valid rational covering whose base lies inside a run chart's rational open.
- **How**: Install the run chart's Tate (`isTateRing_runChart`), Huber, right-completeness and sheafiness (`isSheafy_canonical_runChart`) instances, then discharge the two fields with the single-`D₀` relative-descent transports `isEmbedding_productRestrictionSub_of_imgCovering` and `exists_glue_of_imgCovering`, whose per-datum certificates are `span_image_runChart_eq_top`.
- **Hypotheses**: run chart Tate + right-complete + sheafy at canonical instances; image-span certificate for every valid rational datum.
- **Uses from project**: `IsSheafyOn`, `isTateRing_runChart`, `completeSpace_right_presheafValue`, `isSheafy_canonical_runChart`, `isEmbedding_productRestrictionSub_of_imgCovering`, `exists_glue_of_imgCovering`, `span_image_runChart_eq_top`, `chartData`, `windowUnif`, `presheafValue`, `rationalOpen`, `Ainf`
- **Used by**: `isSheafyOn_Y`
- **Visibility**: public
- **Lines**: 866–896 (proof 25 lines)
- **Notes**: structurally identical to `isSheafyOn_window`, which it subsumes

### `private theorem ainf_pair_spec'`
- **Type**: `∃ P : PairOfDefinition (Ainf p F), ∃ g₁ g₂ : P.A₀, P.I = Ideal.span {g₁, g₂} ∧ (∀ x : P.A₀, (x : Ainf p F) ∈ (ringPlus (Ainf p F) : Subring (Ainf p F))) ∧ Iinf p F (IsTateRing.pseudoUniformizer (A := F)) = Ideal.span {(g₁ : Ainf p F), (g₂ : Ainf p F)}`
- **What**: **The two-generator pair-of-definition spec for `A_inf`**: `A_inf` has a pair of definition whose ideal of definition is generated by the two elements `p` and `[ϖ]`, both lying in `A_inf⁺`, and matching `I_inf` on the nose. This is the exact input shape of the quasi-compactness theorem `isCompact_subtype_rationalOpen₂`.
- **How**: Take `P := pairOfDefinition_ofAdic (Iinf p F ϖ₀)` (available since `I_inf` is finitely generated: `Submodule.fg_span (Set.toFinite _)`), with generators `p` and `teichPi p F ϖ₀`. The ideal identity is `idealToTop (I_inf) = Ideal.map (Subring.topEquiv).symm (span {p, [ϖ]})` computed by `Ideal.map_span` + `Set.image_insert_eq`/`Set.image_singleton`; membership in `A_inf⁺` is `trivial` because the plus subring of `A_inf` is the whole ring.
- **Hypotheses**: `p` prime, `F` perfectoid; `I_inf` is `(p,[ϖ])` and adic.
- **Uses from project**: `pairOfDefinition_ofAdic`, `Iinf`, `teichPi`, `idealToTop`, `ringPlus`, `PairOfDefinition`, `Ainf`, `IsTateRing.pseudoUniformizer`
- **Used by**: `isCompact_subtype_rationalOpen_ainf`
- **Visibility**: **private**
- **Lines**: 898–915 (proof 12 lines)
- **Notes**: the primed name suggests an earlier unprimed variant elsewhere; `fun _ => trivial` encodes `A_inf⁺ = A_inf`

### `theorem isCompact_subtype_rationalOpen_ainf`
- **Type**: `(E : RationalLocData (Ainf p F)) (hErat : E.IsRational) : IsCompact (Subtype.val ⁻¹' rationalOpen E.T E.s : Set ↥(Spa (Ainf p F) (ringPlus (Ainf p F))))`
- **What**: **Valid rational subsets of `Spa(A_inf, A_inf)` are quasi-compact** (Wedhorn 7.35(2), specialised to the two-generator ideal `(p, [ϖ])`).
- **How**: Feed `isCompact_subtype_rationalOpen₂` the two-generator pair from `ainf_pair_spec'`; its remaining hypothesis is `I_inf ≤ √(span E.T)`, which follows from adicity: `isAdic_iff.mp (isAdic_Iinf …)` plus openness of `span E.T` (`hErat.mem_nhds`) yields `N` with `I_inf^N ⊆ span E.T`, so every `x ∈ I_inf` has `x^N ∈ span E.T`.
- **Hypotheses**: `E.IsRational` (openness of the tray span); `I_inf` adic and two-generated.
- **Uses from project**: `ainf_pair_spec'`, `isCompact_subtype_rationalOpen₂`, `isAdic_Iinf`, `Iinf`, `rationalOpen`, `RationalLocData.IsRational`, `Spa`, `Ainf`, `ringPlus`, `IsTateRing.pseudoUniformizer`
- **Used by**: `exists_runChart_superset`
- **Visibility**: public
- **Lines**: 917–932 (proof 9 lines)
- **Notes**: 1 external reference (`YSheaf.lean`)

### `theorem exists_runChart_superset`
- **Type**: `(E : RationalLocData (Ainf p F)) (hErat : E.IsRational) (hEY : rationalOpen E.T E.s ⊆ Y p F ϖ) : ∃ (n : ℤ) (k : ℕ), rationalOpen E.T E.s ⊆ rationalOpen (chartData p F (windowUnif p F ϖ n) 1 1 (p ^ (k + 1)) 1).T (chartData …).s`
- **What**: **Every valid 𝒴-interior rational open lies inside a single run chart** — the compactness step that turns the "𝒴 is only *locally* Tate" problem into a one-chart problem.
- **How**: The trace of the rational open in `Spa` is quasi-compact (`isCompact_subtype_rationalOpen_ainf`), and the Big windows form an open cover of it (each Big window is a rational open by `bigWindow_eq_rationalOpen_windowUnif` hence open by `rationalOpen_isOpen`; they cover 𝒴 by `Y_eq_iUnion_bigWindow`, and the set is 𝒴-interior by `hEY`). Extract a finite subcover indexed by `J : Finset ℤ`, set `n₀ = min'`, `N = max'` of `insert 0 J`, and take `k = (N - n₀).toNat`; each point lies in some `bigWindow j` with `n₀ ≤ j ≤ N`, hence in `runWindow n₀ k` by `bigWindow_subset_runWindow`, which is the run chart's rational open by `runWindow_eq_rationalOpen`.
- **Hypotheses**: `E` valid rational and 𝒴-interior; quasi-compactness of rational opens in `Spa(A_inf, A_inf)`; `1 < p`.
- **Uses from project**: `isCompact_subtype_rationalOpen_ainf`, `bigWindow`, `bigWindow_eq_rationalOpen_windowUnif`, `rationalOpen_isOpen`, `Y_eq_iUnion_bigWindow`, `one_lt_p`, `runWindow_eq_rationalOpen`, `bigWindow_subset_runWindow`, `rationalOpen_subset_spa`, `rationalOpen`, `Y`, `chartData`, `windowUnif`, `Spa`, `Ainf`, `ringPlus`, `RationalLocData.IsRational`
- **Used by**: `isSheafyOn_Y`
- **Visibility**: public
- **Lines**: 934–977 (proof **36 lines**)
- **Notes**: proof >30 lines; `insert 0 J` is used to guarantee nonemptiness of the index finset so `min'`/`max'` exist

### `theorem isSheafyOn_Y`
- **Type**: `ValuationSpectrum.IsSheafyOn (A := Ainf p F) (Y p F ϖ)`
- **What**: **YB6c-3d — the 𝒴-interior sheaf condition over the ambient `A_inf`**: every valid rational covering whose base lies inside 𝒴 satisfies both sheaf axioms. This is the sheafiness input for building the structure *sheaf* of 𝒴.
- **How**: For each field, quasi-compactness places the covering's base inside a single run chart (`exists_runChart_superset` applied to `C.base` with `hC.base`), and the run-chart sheaf condition `isSheafyOn_runChart` — which holds because the run chart ring is Tate and sheafy — applies verbatim to that covering.
- **Hypotheses**: the covering is valid rational and 𝒴-interior; `A_inf` affinoid/T2/complete (the ambient instances of lines 142–153).
- **Uses from project**: `IsSheafyOn`, `exists_runChart_superset`, `isSheafyOn_runChart`, `RationalCoveringData.IsRational.base`, `Y`, `Ainf`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 979–991 (proof 7 lines)
- **Notes**: 2 external references (`YSheaf.lean`) — the second headline export of the file

---

### File Summary

- **Total declarations: 49** (12 defs, 30 lemmas/theorems, 6 instances — 4 anonymous global + 2 file-local `DecidableEq` — and 1 structure `IsSheafyOn`)
- **Key API (used by 3+ others in file)**:
  - `yTop` (6 in-file consumers; 207 project-wide references)
  - `runWindow` (5)
  - `ySpaPoint` (4), `yPresheafedSpace` (4)
  - `yAmbientPresheafedSpace` (3), `yIncl` (3), `IsSheafyOn` (3)
  - (also load-bearing though only 2 in-file consumers: `stalkShrink_Y`, `isLocalRing_stalk_Y`, `yRingStalkEquiv`, `span_image_windowChart_eq_top`, `run_hexact2`, `isTateRing_runChart`)
- **Unused declarations**:
  - *unused in file but exported*: `yVPreObj` (57 external refs — the headline object), `isSheafyOn_Y` (2 external refs)
  - *unused anywhere in the project (dead code)*: `windowKeystone` (0 refs), `isSheafyOn_window` (0 refs — subsumed by `isSheafyOn_runChart`)
  - *used only through typeclass inference*: the four anonymous instances (lines 36, 142, 146, 150) and the two `local instance`s (lines 411, 413)
- **Declarations with sorry**: none
- **Declarations with set_option**: none per-declaration; one file-level `set_option linter.overlappingInstances false` (line 23). **No `maxHeartbeats` bumps anywhere.**
- **Proofs >30 lines**:
  - `rationalShrink_Y` — 83 lines (56–138)
  - `runWindow_eq_rationalOpen_ofNat` — 61 lines (589–649)
  - `stalkShrink_Y` — 55 lines (162–216)
  - `runWindow_eq_rationalOpen_neg` — 54 lines (660–707)
  - `exists_runChart_superset` — 36 lines (942–977)

**Cross-cutting observations (for cleanup / dedup):**
1. The `yTop … yVPreObj` block (lines 236–324) is a specialisation of the generic API in `VRestrict.lean` (`restrictSpace`, `restrictRingAmbient`, `restrictRingStalkIso`, `restrictRingStalkEquiv`, `isLocalRing_restrictStalk`, `VPreObj.restrictOpen`) — the two are line-for-line parallel, including the "spell the point as the inclusion image" trick (`ySpaPoint` ≡ `restrictPoint`).
2. The window/run pairs are systematic duplicates: `isUnit_canonicalMap_p_teichPi_window` ↔ `_runChart`, `span_image_windowChart_eq_top` ↔ `span_image_runChart_eq_top`, `isSheafy_canonical_window` ↔ `_runChart`, `isSheafyOn_window` ↔ `isSheafyOn_runChart`, `window_hexact2` ↔ `run_hexact2` — each pair differs only by `p ↦ p^{k+1}`. Since the run versions subsume the window versions (`k = 0` gives `a = p`), the window copies could be derived rather than re-proved.
3. `ValuationSpectrum.IsSheafyOn` and `ValuationSpectrum.isSheafy_congr_plusSubring` are generic (`A` an arbitrary Huber ring) and sit in a Fargues–Fontaine file; they belong upstream with the rest of the `IsSheafy` API.
