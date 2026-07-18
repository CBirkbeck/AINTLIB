# Inventory — `projects/ModularCurves/ModularCurves/EllipticCurve/AdditionSpecPoints.lean`

Phase-1 /overview inventory (y1). 2,033 lines, 68 declarations (24 `theorem`, 42 `lemma`, 2 `noncomputable def`), all public, all in `namespace ModularCurves`. Single import: `ModularCurves.EllipticCurve.GroupLawConstruction`. This is the **C6 dictionary layer**: it proves `mulModelHom_specPoints` (line 2021) — on field points the glued two-law multiplication `mulModelHom` computes mathlib's `Point.add` through the dictionary `projModelPointsEquiv` — by descending a field point of `E ×_R E` through the Bosma–Lenstra regularity opens to an affine law piece, reading coordinates out through the chart dictionary, identifying the law triples with mathlib's `add`, and transporting the ULift universal-atlas case along base change. Sole importer: `GroupLawAxioms.lean` (consumes `mulModelHom_specPoints` and `mulModelHom_universalWeierstrassLocU`).

Section map: top-level (C6-a/b) 20–71 · Descent 73–157 · Readout 160–215 · StrengthenedDescent 217–344 · TensorLegs 346–417 · PieceProjections 419–492 · TripleIdentification 494–517 · ChartNaturality 519–1288 (⊃ ChartPointTriple 627–1286 ⊃ DictionaryOfPiece 885–1284) · AtlasPush 1290–1363 · AtlasFormula 1365–1892 (⊃ DictionaryNaturality 1780–1890) · OfMap 1907–2031.

---

### `specPoint_factors_iSup` — theorem
- **What**: [C6-a′] A field-valued point `g : Spec K ⟶ (⨆ i, U i).toScheme` of an iSup of opens factors through some member: `∃ i h, h ≫ X.homOfLE (le_iSup U i) = g`.
- **How**: `Spec K` has a unique point; its image lies in the sup (`Scheme.Opens.range_ι`), so `TopologicalSpace.Opens.mem_iSup` picks a member; `IsOpenImmersion.lift` on `X.homOfLE` gives the factor (range check via `Set.range_unique` + `Scheme.opensRange_homOfLE`), fac by `IsOpenImmersion.lift_fac`.
- **Hypotheses**: `X : Scheme`, `U : ι → X.Opens`, `K` field, `g` as above.
- **Uses (project)**: none — pure mathlib scheme theory.
- **Used by (in file)**: `specPoint_addOnZ_family`, `specPoint_addOnZOnImage_factors`, `specPoint_addOnY_family`, `specPoint_addOnYOnImage_factors`, `specPoint_addOnZOnImage_factors'`, `specPoint_addOnYOnImage_factors'` (6).
- **Visibility**: public. **Lines**: 20–39 (proof 13).
- **Notes**: no project dependencies — ForMathlib/upstream candidate.

### `specPoint_factors_blOpenZ_or_blOpenY` — theorem
- **What**: [C6-a] A field point of `E ×_R E` (`pullback (projModelπ W) (projModelπ W)`) factors through `blOpenZ W` or `blOpenY W`.
- **How**: unique point lies in `blOpenZ ⊔ blOpenY` by the covering theorem `blOpen_cover`; `TopologicalSpace.Opens.mem_sup` splits; `IsOpenImmersion.lift`/`lift_fac` against each `Opens.ι` with `Set.range_unique`.
- **Hypotheses**: `W : WeierstrassCurve R` `[W.IsElliptic]`, `K` field `[Algebra R K]`.
- **Uses (project)**: `blOpen_cover`, `blOpenZ`, `blOpenY`, `mulModelHom`-side opens (all `ModularCurves`, GroupLawConstruction.lean); `projModelπ` (WeierstrassModel.lean).
- **Used by (in file)**: `mulModelHom_specPoints_atlas` (1).
- **Visibility**: public. **Lines**: 40–55 (proof 11).

### `specPoint_mulModelHom_of_blOpenZ` — theorem
- **What**: [C6-b, Z] Through a `blOpenZ` factorisation `hh : h ≫ (blOpenZ W).ι = g`, the multiplication evaluates as the Z-law: `g ≫ mulModelHom W = h ≫ addOnZ W`.
- **How**: rewrite `← hh`, assoc, then the restriction identity `blOpenZ_ι_mulModelHom` (ModularCurves/IsElliptic form). 2-line proof.
- **Hypotheses**: `W` elliptic; `K : CommRing`.
- **Uses (project)**: `mulModelHom`, `addOnZ`, `blOpenZ`, `blOpenZ_ι_mulModelHom` (GroupLawConstruction.lean); `projModelπ`.
- **Used by (in file)**: none.
- **Visibility**: public. **Lines**: 57–63 (proof 2).
- **Notes**: UNUSED in file and no cross-file consumers — the atlas proof inlines the WCP-level `blOpenZ_ι_mulModelHom` instead. Dead-code candidate.

### `specPoint_mulModelHom_of_blOpenY` — theorem
- **What**: [C6-b, Y] Mirror: `g ≫ mulModelHom W = h ≫ addOnY W` through a `blOpenY` factorisation.
- **How**: `blOpenY_ι_mulModelHom` (ModularCurves form). 2-line proof.
- **Hypotheses / Uses / Visibility**: as Z-version with `addOnY`, `blOpenY`, `blOpenY_ι_mulModelHom`.
- **Used by (in file)**: none.
- **Lines**: 65–71 (proof 2). **Notes**: UNUSED (dead-code candidate, mirror of the above).

### `specPoint_addOnZ_family` — theorem
- **What**: [C6-d1a, Z] Family-level descent: a field point `h` of `WCP.blOpenZ W` factors through some member of the 2×2 family `blOpenZFamily W p`, with evaluation compatibility `h ≫ WCP.addOnZ W hΔ = h₁ ≫ addOnZFamily W hΔ p`.
- **How**: `specPoint_factors_iSup` on the family; transport the evaluation along the restriction identity `homOfLE_le_addOnZ` via a term-mode `congrArg`/`Category.assoc` chain.
- **Hypotheses**: `[IsDomain R] [IsJacobsonRing R]`, `hΔ : IsUnit W.Δ`, `K` field.
- **Uses (project)**: `specPoint_factors_iSup` (this file); `WCP.blOpenZ`, `blOpenZFamily`, `WCP.addOnZ`, `addOnZFamily`, `homOfLE_le_addOnZ` (AdditionChartGlobal.lean); `projModelπ`.
- **Used by (in file)**: `mulModelHom_specPoints_atlas` (1).
- **Visibility**: public. **Lines**: 79–88 (proof 3, term-heavy).

### `specPoint_addOnZOnImage_factors` — theorem
- **What**: [C6-d1b, Z] Within-chart descent: a field point of `blOpenZImage W i j` evaluates through some affine law-1 piece — `h ≫ addOnZOnImage W hΔ i j = Spec.map ψ ≫ addOnZPieceMor W i j k hΔ` for a ring map `ψ : Localization.Away (lawOneTriple W i j k) →+* K`.
- **How**: move to the chart-product side through `Scheme.Hom.isoImage (pieceι W i j)`; `specPoint_factors_iSup` over `blOpenZPieceFamily`; `ψ := Spec.preimage` of the composite through `chartPieceIso`/`specBasicOpenIsoAway`; collapse with `ι_addOnZOnSup` and `Spec.map_preimage`.
- **Hypotheses**: `[IsDomain R] [IsJacobsonRing R] [IsDomain (biChartRing W i j)]`, `hΔ`, `K` field.
- **Uses (project)**: `specPoint_factors_iSup`; `blOpenZImage`, `addOnZOnImage`, `addOnZOnSup`, `addOnZOnFamily`, `ι_addOnZOnSup`, `blOpenZPieceFamily`, `addOnZPieceMor`, `pieceι`, `chartPieceIso`, `lawOneTriple`, `biChartRing`, `specBasicOpen`, `specBasicOpenIsoAway`.
- **Used by (in file)**: none.
- **Visibility**: public. **Lines**: 92–116 (proof 19).
- **Notes**: UNUSED — strictly subsumed by `specPoint_addOnZOnImage_factors'` (proof duplicated there verbatim). Dedup candidate: derive from the primed version or delete.

### `specPoint_addOnY_family` — theorem
- **What**: [C6-d1a, Y] Mirror of `specPoint_addOnZ_family` for `WCP.blOpenY`/`addOnY`/`blOpenYFamily`/`addOnYFamily`.
- **How**: `specPoint_factors_iSup` + `homOfLE_le_addOnY`.
- **Hypotheses / Visibility**: as Z-version.
- **Uses (project)**: `specPoint_factors_iSup`; `WCP.blOpenY`, `blOpenYFamily`, `WCP.addOnY`, `addOnYFamily`, `homOfLE_le_addOnY`; `projModelπ`.
- **Used by (in file)**: `mulModelHom_specPoints_atlas` (1). **Lines**: 118–127 (proof 3).

### `specPoint_addOnYOnImage_factors` — theorem
- **What**: [C6-d1b, Y] Mirror within-chart descent onto law-2 pieces (`lawTwoTriple`, `addOnYPieceMor`).
- **How**: as Z-version with `ι_addOnYOnSup`, `blOpenYPieceFamily`, `addOnYOnFamily`.
- **Uses (project)**: Y-mirrors of the Z list (`blOpenYImage`, `addOnYOnImage`, `addOnYOnSup`, `addOnYOnFamily`, `ι_addOnYOnSup`, `blOpenYPieceFamily`, `addOnYPieceMor`, `lawTwoTriple`) + `specPoint_factors_iSup`, `pieceι`, `chartPieceIso`, `specBasicOpen(IsoAway)`.
- **Used by (in file)**: none.
- **Visibility**: public. **Lines**: 131–155 (proof 19).
- **Notes**: UNUSED — subsumed by `specPoint_addOnYOnImage_factors'`. Dedup candidate.

### `addOnZPieceHom_coord` — lemma
- **What**: [C6-d2, Z] Coordinate readout: `(ψ ∘ addOnZPieceHom W i j k hΔ)` sends the chart coordinate `chartCoordEquiv W k (mk (X m))` to `ψ(algebraMap (lawOneTriple W i j m) · invSelf (lawOneTriple W i j k))`, uniformly in `k`.
- **How**: `unfold addOnZPieceHom chartAwayHomOfTriple`; round-trip the coordinate through `(chartCoordAlgEquiv W k).symm_apply_apply`; finish with `chartHomOfTriple_coord`.
- **Hypotheses**: `[IsDomain R] [IsJacobsonRing R] [IsDomain (biChartRing W i j)]`, `hΔ`, `K` field `[Algebra R K]`.
- **Uses (project)**: `addOnZPieceHom` (AdditionChartAway.lean), `chartAwayHomOfTriple`, `chartHomOfTriple`, `chartHomOfTriple_coord` (AdditionChartHom.lean), `chartCoordEquiv`, `chartCoordAlgEquiv`, `awayTriple`, `awayTriple_mul_invSelf`, `equation_awayTriple`, `equation_lawOneTriple_of_isDomain`, `lawOneTriple`, `biChartRing`.
- **Used by (in file)**: none.
- **Visibility**: public. **Lines**: 167–189 (proof 13).
- **Notes**: UNUSED — the atlas docstring cites it as the plan, but `dictionary_sum_of_pieceZ` re-derives the readout via `chartAwayHomOfTriple_isLocalizationElem` instead. Dead-code candidate. `unfold`-based proof.

### `addOnYPieceHom_coord` — lemma
- **What**: [C6-d2, Y] Mirror readout for `addOnYPieceHom`/`lawTwoTriple`.
- **How / Hypotheses**: identical shape (`chartHomOfTriple_coord` + `equation_lawTwoTriple_of_isDomain`).
- **Uses (project)**: Y-mirrors (`addOnYPieceHom`, `lawTwoTriple`, `equation_lawTwoTriple_of_isDomain`) + shared chart-hom layer.
- **Used by (in file)**: none.
- **Visibility**: public. **Lines**: 191–213 (proof 13). **Notes**: UNUSED (mirror of the above).

### `blOpenZImage_ι_eq` — lemma
- **What**: Standalone collapse: `(blOpenZImage W i j).ι = isoImage.inv ≫ (⨆ k, blOpenZPieceFamily W i j k).ι ≫ pieceι W i j`.
- **How**: term proof: `Iso.inv_hom_id_assoc` + `Scheme.Hom.isoImage_hom_ι`.
- **Hypotheses**: section vars (`IsDomain R`, `IsJacobsonRing R`, `IsDomain (biChartRing W i j)`), `k : Fin 3` (unused binder!).
- **Uses (project)**: `blOpenZImage`, `blOpenZPieceFamily`, `pieceι`.
- **Used by (in file)**: `specPoint_addOnZOnImage_factors'` (1).
- **Visibility**: public. **Lines**: 224–231 (term proof).
- **Notes**: binder `(k : Fin 3)` is not used in the statement — spurious argument, cleanup candidate.

### `mR_isoAway_pieceAwayZι` — lemma
- **What**: Standalone collapse: the σ-chain `morphismRestrict (chartPieceIso).hom (specBasicOpen …) ≫ specBasicOpenIsoAway.inv ≫ pieceAwayZι W i j k` equals `(blOpenZPieceFamily W i j k).ι ≫ pieceι W i j`.
- **How**: unfold `pieceAwayZι`; `morphismRestrict_ι` + iso cancellation (`Iso.inv_hom_id_assoc`, `Iso.hom_inv_id_assoc`); `rfl`.
- **Uses (project)**: `pieceAwayZι` (AdditionChartGlobal.lean), `chartPieceIso`, `specBasicOpen`, `specBasicOpenIsoAway`, `lawOneTriple`, `blOpenZPieceFamily`, `pieceι`, `biChartRing`.
- **Used by (in file)**: `specPoint_addOnZOnImage_factors'` (1).
- **Visibility**: public. **Lines**: 233–244 (proof 5).

### `specPoint_addOnZOnImage_factors'` — theorem
- **What**: [C6-d3, Z] STRENGTHENED within-chart descent: the factoring `ψ` satisfies both the evaluation equation (as in the unprimed version) AND the immersion equation `Spec.map ψ ≫ pieceAwayZι W i j k = h ≫ (blOpenZImage W i j).ι`.
- **How**: same `specPoint_factors_iSup` + `Spec.preimage` construction as the unprimed lemma (first bullet literally repeats it, key step `ι_addOnZOnSup`); second bullet chains `blOpenZImage_ι_eq`, `Scheme.homOfLE_ι` and `mR_isoAway_pieceAwayZι` through long term-mode `congrArg` towers.
- **Hypotheses**: `[IsDomain R] [IsJacobsonRing R] [IsDomain (biChartRing W i j)]`, `hΔ`, `K` field.
- **Uses (project)**: `specPoint_factors_iSup`, `blOpenZImage_ι_eq`, `mR_isoAway_pieceAwayZι` (this file); `blOpenZPieceFamily`, `pieceι`, `chartPieceIso`, `specBasicOpen(IsoAway)`, `addOnZOnImage`, `addOnZOnSup`, `addOnZOnFamily`, `ι_addOnZOnSup`, `addOnZPieceMor`, `pieceAwayZι`, `lawOneTriple`, `biChartRing`.
- **Used by (in file)**: `mulModelHom_specPoints_atlas` (4 call sites).
- **Visibility**: public. **Lines**: 246–282 (proof 30 — borderline).
- **Notes**: proof duplicates `specPoint_addOnZOnImage_factors` wholesale; decompose/dedup candidate.

### `blOpenYImage_ι_eq` — lemma
- **What / How**: Y-mirror of `blOpenZImage_ι_eq` (`blOpenYImage`, `blOpenYPieceFamily`).
- **Used by (in file)**: `specPoint_addOnYOnImage_factors'` (1).
- **Visibility**: public. **Lines**: 284–291. **Notes**: same spurious `(k : Fin 3)` binder.

### `mR_isoAway_pieceAwayι` — lemma
- **What / How**: Y-mirror of `mR_isoAway_pieceAwayZι` (`pieceAwayι`, `lawTwoTriple`, `blOpenYPieceFamily`).
- **Used by (in file)**: `specPoint_addOnYOnImage_factors'` (1).
- **Visibility**: public. **Lines**: 293–304 (proof 5).

### `specPoint_addOnYOnImage_factors'` — theorem
- **What**: [C6-d3, Y] Mirror strengthened descent onto law-2 pieces, with immersion equation through `pieceAwayι`.
- **How**: as Z-primed with `ι_addOnYOnSup`, `blOpenYImage_ι_eq`, `mR_isoAway_pieceAwayι`.
- **Uses (project)**: Y-mirrors + `specPoint_factors_iSup`, `addOnYPieceMor`, `pieceAwayι`, `lawTwoTriple`.
- **Used by (in file)**: `mulModelHom_specPoints_atlas` (4 call sites).
- **Visibility**: public. **Lines**: 306–342 (proof 30 — borderline).

### `tensorLeftLeg_chartCoord` — lemma
- **What**: [C6-d4a, left] The left tensor leg `biChartRingAwayTensorEquiv.symm ∘ includeLeftRingHom` carries `chartCoordEquiv W i (mk (X m))` to `biChartPointFst W i j m`.
- **How**: unfold `biChartRingAwayTensorEquiv` into `biChartRingTensorEquiv ∘ congr(chartCoordAlgEquiv ⊗ chartCoordAlgEquiv)`; compute the tmul via `Algebra.TensorProduct.congr_symm_apply`/`map_tmul`; identify with the `rename Sum.inl` generator by `biChartRingTensorEquiv_mk_rename_inl`; conclude with `AlgEquiv.symm_apply_apply`, `rename_X`, `dif_neg m.2`.
- **Hypotheses**: `W : WeierstrassCurve R`, `i j : Fin 3`, `m : {l // l ≠ i}` (no domain hyps).
- **Uses (project)**: `biChartRingAwayTensorEquiv` (AdditionChartSpec.lean), `biChartRingTensorEquiv`, `biChartRingTensorEquiv_mk_rename_inl` (AdditionChartTensor.lean), `chartCoordEquiv`, `chartCoordAlgEquiv`, `chartAway`, `affineChartRing`, `biChartPointFst`.
- **Used by (in file)**: `dictionary_fst_of_pieceZ`, `dictionary_fst_of_pieceY` (2).
- **Visibility**: public. **Lines**: 352–381 (proof 22).

### `tensorRightLeg_chartCoord` — lemma
- **What**: [C6-d4a, right] Mirror: right leg (`includeRight`) carries `chartCoordEquiv W j (mk (X m))` to `biChartPointSnd W i j m`.
- **How**: as left leg with `biChartRingTensorEquiv_mk_rename_inr`, `biChartPointSnd`.
- **Uses (project)**: right-mirrors of the left-leg list.
- **Used by (in file)**: `dictionary_snd_of_pieceZ`, `dictionary_snd_of_pieceY` (2).
- **Visibility**: public. **Lines**: 383–415 (proof 25).

### `specMap_pieceAwayZι_fst` — lemma
- **What**: [C6-d4b, Z-fst] `Spec.map ψ ≫ pieceAwayZι W i j k ≫ pullback.fst = Spec.map (ψ ∘ algebraMap ∘ leftTensorLeg) ≫ chartι W i` — the first projection of a piece point is a chart point of the composite ring map.
- **How**: `pieceAwayZι_eq` + `pieceι_fst` + `chartPieceIso_inv_fst`, then collapse `Spec.map_comp`/`CommRingCat.ofHom_comp`.
- **Hypotheses**: `K : CommRing`, `ψ : Localization.Away (lawOneTriple W i j k) →+* K`.
- **Uses (project)**: `pieceAwayZι`, `pieceAwayZι_eq`, `pieceι_fst` (AdditionChartTransition.lean), `chartPieceIso_inv_fst` (AdditionChartSpec.lean), `chartι`, `biChartRingAwayTensorEquiv`, `chartAway`, `lawOneTriple`, `biChartRing`, `projModelπ`.
- **Used by (in file)**: `dictionary_fst_of_pieceZ` (1).
- **Visibility**: public. **Lines**: 425–440 (proof 5).

### `specMap_pieceAwayZι_snd` — lemma
- **What**: [C6-d4b, Z-snd] Mirror with `pullback.snd`, right tensor leg, `chartι W j`.
- **How**: `pieceι_snd` + `chartPieceIso_inv_snd`.
- **Used by (in file)**: `dictionary_snd_of_pieceZ` (1).
- **Visibility**: public. **Lines**: 441–456 (proof 5).

### `specMap_pieceAwayι_fst` — lemma
- **What**: [C6-d4b, Y-fst] Law-2 mirror of `specMap_pieceAwayZι_fst` (`pieceAwayι`, `lawTwoTriple`).
- **How**: `pieceAwayι_eq` + `pieceι_fst` + `chartPieceIso_inv_fst`.
- **Used by (in file)**: `dictionary_fst_of_pieceY` (1).
- **Visibility**: public. **Lines**: 458–473 (proof 5).

### `specMap_pieceAwayι_snd` — lemma
- **What**: [C6-d4b, Y-snd] Law-2/snd mirror.
- **Used by (in file)**: `dictionary_snd_of_pieceY` (1).
- **Visibility**: public. **Lines**: 475–490 (proof 5).
- **Notes**: the four `specMap_pieceAway*` lemmas are a 2×2 mirror family with identical 5-line proofs — parametrisation candidate.

### `ringHom_lawOneTriple` — lemma
- **What**: [C6-d5, law 1] A ring map `χ` out of `biChartRing W i j` carries the law-1 triple to mathlib's `addXYZ` of the χ-images of the tautological points: `χ ∘ lawOneTriple = (….map χ).addXYZ (χ ∘ biChartPointFst) (χ ∘ biChartPointSnd)`.
- **How**: rewrite `lawOneTriple` (definitionally `addXYZ` of the tautological points) and apply mathlib's `map_addXYZ` (naturality of the addition formula).
- **Hypotheses**: `K : CommRing`, `χ : biChartRing W i j →+* K`.
- **Uses (project)**: `lawOneTriple`, `biChartRing`, `biChartPointFst`, `biChartPointSnd` (AdditionChartRing.lean). Mathlib: `WCP.map_addXYZ`.
- **Used by (in file)**: `descended_lawOne_eq_add` (2 call sites) (1).
- **Visibility**: public. **Lines**: 500–507 (proof 2).

### `ringHom_lawTwoTriple` — lemma
- **What**: [C6-d5, law 2] Mirror: `χ ∘ lawTwoTriple = (….map χ).dblAddXYZ …`.
- **How**: project `map_dblAddXYZ` (AdditionLawOnCurve.lean).
- **Uses (project)**: `lawTwoTriple`, `biChartPointFst/Snd`, `map_dblAddXYZ`, `dblAddXYZ` (AdditionLaw.lean).
- **Used by (in file)**: `descended_lawTwo_smul_add` (1).
- **Visibility**: public. **Lines**: 509–515 (proof 2).

### `Proj_awayι_congr` — theorem
- **What**: [C6-c′0] `eqToHom` quarantine: `Proj.awayι 𝒜 f hf hm = eqToHom (…) ≫ Proj.awayι 𝒜 g hg hm` when `f = g` (transport of the affine chart immersion across a generator equality).
- **How**: `subst h`; `eqToHom_refl` + `Category.id_comp`.
- **Hypotheses**: graded ring `𝒜`, `0 < m`, `h : f = g`, memberships.
- **Uses (project)**: none — pure mathlib (`Proj.awayι`).
- **Used by (in file)**: `chartι_map_comp_projModelBaseChange` (1).
- **Visibility**: public. **Lines**: 525–532 (proof 2).
- **Notes**: ForMathlib/upstream candidate.

### `bcChartAwayMap` — noncomputable def
- **What**: The graded `Away`-map of the base change at the `i`-th chart generator: `HomLoc.Away (quotientGrading (projIdeal W₀)) (mk (X i)) →+* HomLoc.Away (… (W₀.map f)) (bc-image of the generator)`.
- **How**: `HomogeneousLocalization.Away.map` (mathlib) applied to `baseChangeGradedHom f W₀`.
- **Hypotheses**: `f : U →+* R`, `W₀ : WeierstrassCurve U`, `i : Fin 3`.
- **Uses (project)**: `baseChangeGradedHom`, `quotientGrading`, `quotientGradingHom`, `projIdeal` (WeierstrassModel.lean / ForMathlib/GradedQuotient.lean).
- **Used by (in file)**: `awayι_image_comp_projModelBaseChange`, `chartι_map_comp_projModelBaseChange`, `bcChartAwayMap_isLocalizationElem`, `specMap_chartι_comp_baseChange`, `dictionary_baseChange` (5). **KEY API**.
- **Visibility**: public. **Lines**: 536–543.

### `awayι_image_comp_projModelBaseChange` — theorem
- **What**: [C6-c′1] The literal chart-restriction of the base change: `Proj.awayι (bc-image gen) ≫ projModelBaseChange f W₀ = Spec.map (bcChartAwayMap f W₀ i) ≫ chartι W₀ i`.
- **How**: term-mode instantiation of mathlib's `Proj.awayι_comp_map` at `baseChangeGradedHom` with `baseChangeGradedHom_irrelevant_le`.
- **Uses (project)**: `projModelBaseChange`, `baseChangeGradedHom`, `baseChangeGradedHom_irrelevant_le`, `mk_X_mem_quotientGrading_one` (WeierstrassModel.lean), `chartι`, `bcChartAwayMap`, `quotientGrading(-Hom)`, `projIdeal`.
- **Used by (in file)**: `chartι_map_comp_projModelBaseChange` (1).
- **Visibility**: public. **Lines**: 545–554 (term proof).

### `baseChangeGradedHom_chartGen` — lemma
- **What**: The chart generator's image under the base change is the mapped chart generator: `baseChangeGradedHom f W₀ (mk (X i)) = mk (X i)` in the target grading.
- **How**: `HomogeneousIdeal.quotientGradingMap_mk` (project ForMathlib) + `MvPolynomial.map_X`.
- **Uses (project)**: `baseChangeGradedHom`, `mvMapGraded`, `projIdeal`, `projIdeal_le_comap`, `quotientGradingHom(_apply)`, `quotientGradingMap(_mk)` (ForMathlib/GradedQuotient.lean).
- **Used by (in file)**: `chartι_map_comp_projModelBaseChange`, `specMap_chartι_comp_baseChange` (eqToHom obligations), `dictionary_baseChange` (3). **KEY API**.
- **Visibility**: public. **Lines**: 558–569 (proof 8).

### `chartι_map_comp_projModelBaseChange` — theorem
- **What**: [C6-c′2] The mapped chart immersion through the base change, `eqToHom`-quarantined: `chartι (W₀.map f) i ≫ projModelBaseChange f W₀ = eqToHom … ≫ Spec.map (bcChartAwayMap f W₀ i) ≫ chartι W₀ i`.
- **How**: swap the generator with `Proj_awayι_congr` (at `baseChangeGradedHom_chartGen.symm`), then `awayι_image_comp_projModelBaseChange`.
- **Uses (project)**: `Proj_awayι_congr`, `baseChangeGradedHom_chartGen`, `awayι_image_comp_projModelBaseChange`, `bcChartAwayMap` (this file); `chartι`, `projModelBaseChange`, `mk_X_mem_quotientGrading_one`.
- **Used by (in file)**: `specMap_chartι_comp_baseChange` (1).
- **Visibility**: public. **Lines**: 571–584 (proof 9).

### `bcChartAwayMap_isLocalizationElem` — lemma
- **What**: [C6-e4a] `bcChartAwayMap` carries the localization coordinates `isLocalizationElem (X i) (X m)` to the image coordinates.
- **How**: `HomogeneousLocalization.Away.map_mk` (mathlib) + `pow_one` + `rfl`.
- **Uses (project)**: `bcChartAwayMap`, `mk_X_mem_quotientGrading_one`, `baseChangeGradedHom`. Mathlib: `HomLoc.Away.isLocalizationElem`, `Away.map_mk`.
- **Used by (in file)**: `dictionary_baseChange` (1).
- **Visibility**: public. **Lines**: 587–599 (proof 6).

### `specMap_chartι_comp_baseChange` — theorem
- **What**: [C6-e4, scheme level] A W-side chart point pushed through the base change is the atlas-side chart point of the composed ring map: `(Spec.map φ ≫ chartι (W₀.map f) i) ≫ projModelBaseChange = Spec.map ((φ ∘ eqToHom e) ∘ bcChartAwayMap) ≫ chartι W₀ i`.
- **How**: `chartι_map_comp_projModelBaseChange`, then `Spec.map_eqToHom` collapses the scheme-level transport into a ring-map composite (inline `rw … from` cast).
- **Hypotheses**: `φ : chartAway (W₀.map f) i →+* K`, an object equality `e` of the two `CommRingCat.of` presentations.
- **Uses (project)**: `chartι_map_comp_projModelBaseChange`, `bcChartAwayMap` (this file); `chartAway`, `chartι`, `projModelBaseChange`, `quotientGrading(-Hom)`, `projIdeal`, `baseChangeGradedHom`.
- **Used by (in file)**: `dictionary_baseChange` (1).
- **Visibility**: public. **Lines**: 602–624 (proof 10).

### `chartPointTriple` — noncomputable def
- **What**: The φ-triple of a chart point: `m ↦ φ (isLocalizationElem (X k) (X m))` — the dictionary-side homogeneous coordinates of `Spec.map φ ≫ chartι W k`.
- **How**: direct definition from mathlib's `HomogeneousLocalization.Away.isLocalizationElem`.
- **Hypotheses**: `φ : chartAway W k →+* K`, `K : CommRing`.
- **Uses (project)**: `chartAway`, `mk_X_mem_quotientGrading_one`.
- **Used by (in file)**: `chartPointTriple_self`, `chartPointTriple_self_eq_one`, `chartPointTriple_eq_comp`, `equation_chartPointTriple`, `eq_chartAwayHomOfTriple_chartPointTriple`, `dictionary_eq_toAffine`, `dictionary_fst/snd_of_pieceZ`, `dictionary_fst/snd_of_pieceY`, `dictionary_sum_of_pieceZ/Y`, `dictionary_baseChange` (13). **KEY API — the file's central gadget**.
- **Visibility**: public. **Lines**: 633–637.

### `chartPointTriple_self` — lemma
- **What**: Unfolding lemma at the chart index: `chartPointTriple W k φ k = φ (isLocalizationElem k k)`.
- **How**: `rfl`.
- **Used by (in file)**: none (`chartPointTriple_self_eq_one` unfolds the def directly).
- **Visibility**: public. **Lines**: 639–642.
- **Notes**: UNUSED in file, no cross-file consumers — dead-code candidate.

### `chartPointTriple_self_eq_one` — lemma
- **What**: The k-th coordinate of the φ-triple is 1.
- **How**: `isLocalizationElem k k = 1` by `HomogeneousLocalization.val_injective` + `Localization.mk_self` (explicit `Submonoid.powers` witness); then `map_one`.
- **Uses (project)**: `chartPointTriple`, `mk_X_mem_quotientGrading_one`, `quotientGradingHom`, `projIdeal`, `chartAway`.
- **Used by (in file)**: `chartPointTriple_eq_comp`, `dictionary_eq_toAffine`, `dictionary_fst_of_pieceZ`, `dictionary_snd_of_pieceZ`, `dictionary_fst_of_pieceY`, `dictionary_snd_of_pieceY`, `dictionary_sum_of_pieceZ`, `dictionary_sum_of_pieceY` (8). **KEY API**.
- **Visibility**: public. **Lines**: 644–657 (proof 10).

### `chartPointTriple_eq_comp` — lemma
- **What**: The φ-triple is the affine chart point pushed through the coordinate equivalence: `chartPointTriple W k φ = (φ ∘ chartCoordAlgEquiv W k) ∘ affineChartPoint W k`.
- **How**: `funext`; `by_cases m = k` — diagonal via `chartPointTriple_self_eq_one` + `dif_pos`; off-diagonal via `chartCoordEquiv_mk_X` + `dif_neg`.
- **Uses (project)**: `chartPointTriple(_self_eq_one)`, `affineChartPoint` (AdditionChartRing.lean), `chartCoordAlgEquiv`, `chartCoordEquiv_mk_X`.
- **Used by (in file)**: `equation_chartPointTriple` (1).
- **Visibility**: public. **Lines**: 660–678 (proof 14).

### `equation_chartPointTriple` — lemma
- **What**: The φ-triple satisfies the projective Weierstrass equation over `K` (the chart relation is killed in `chartAway`).
- **How**: push `equation_affineChartPoint` through the ring map (`Equation.map`); identify the target curve via `WeierstrassCurve.map_map` + `(chartCoordAlgEquiv).toAlgHom.comp_algebraMap` + the R-compatibility `hφ`.
- **Hypotheses**: `[Algebra R K]`, `hφ : φ.comp (algebraMap R (chartAway W k)) = algebraMap R K`.
- **Uses (project)**: `chartPointTriple_eq_comp`, `equation_affineChartPoint` (AdditionChartRing.lean), `affineChartRing`, `chartCoordAlgEquiv`, `chartAway`.
- **Used by (in file)**: `dictionary_eq_toAffine` (1).
- **Visibility**: public. **Lines**: 680–699 (proof 15).

### `chartAwayHom_ext` — lemma
- **What**: [k1] Extensionality: two ring maps out of `chartAway W k` agree if they agree after `algebraMap R` and on the localization coordinates `isLocalizationElem k m` (m ≠ k).
- **How**: cancel the surjective `chartCoordAlgEquiv` (`RingHom.cancel_right`), then `Ideal.Quotient.ringHom_ext` + `MvPolynomial.ringHom_ext`; `C`-case via `chartCoordEquiv_mk_C` + `chartAway_algebraMap_apply`; `X`-case via `chartCoordEquiv_mk_X`.
- **Hypotheses**: `χ₁ χ₂ : chartAway W k →+* K`, base + coordinate agreement.
- **Uses (project)**: `chartAway`, `chartCoordAlgEquiv`, `chartCoordEquiv(_mk_C/_mk_X)`, `chartAway_algebraMap_apply` (AdditionChartSpec.lean), `mk_X_mem_quotientGrading_one`.
- **Used by (in file)**: `eq_chartAwayHomOfTriple_chartPointTriple` (1).
- **Visibility**: public. **Lines**: 702–731 (proof 20).

### `chartAwayHomOfTriple_isLocalizationElem` — lemma
- **What**: Generic coordinate action of a chart-triple morphism: `chartAwayHomOfTriple W k t u hu ht (isLocalizationElem k m) = t m * u`.
- **How**: pull the coordinate back through `chartCoordEquiv_mk_X`; `unfold chartAwayHomOfTriple`; round-trip via `symm_apply_apply`; `chartHomOfTriple_coord`.
- **Hypotheses**: `t : Fin 3 → K`, unit witness `hu : t k * u = 1`, `ht : Equation t`, `[Algebra R K]`.
- **Uses (project)**: `chartAwayHomOfTriple`, `chartHomOfTriple(_coord)` (AdditionChartHom.lean), `chartCoordEquiv(_mk_X)`, `chartCoordAlgEquiv`, `mk_X_mem_quotientGrading_one`.
- **Used by (in file)**: `eq_chartAwayHomOfTriple_chartPointTriple`, `dictionary_eq_toAffine`, `dictionary_sum_of_pieceZ`, `dictionary_sum_of_pieceY` (4). **KEY API**.
- **Visibility**: public. **Lines**: 733–748 (proof 12).

### `eq_chartAwayHomOfTriple_chartPointTriple` — lemma
- **What**: [k2] An R-compatible ring map out of `chartAway W k` IS the chart morphism of its own coordinate triple (with unit 1): `φ = (chartAwayHomOfTriple W k (chartPointTriple W k φ) 1 hu hT).toRingHom`.
- **How**: `chartAwayHom_ext`; base leg by `comp_algebraMap`; coordinate leg by `chartAwayHomOfTriple_isLocalizationElem` + `mul_one`.
- **Uses (project)**: `chartAwayHom_ext`, `chartAwayHomOfTriple_isLocalizationElem`, `chartPointTriple`, `chartAwayHomOfTriple`, `mk_X_mem_quotientGrading_one`.
- **Used by (in file)**: `dictionary_eq_toAffine` (2 call sites) (1).
- **Visibility**: public. **Lines**: 750–767 (proof 10).

### `dictionary_eq_toAffine` — theorem  ★ mid-layer keystone
- **What**: **[e5c-key]** The dictionary reads any chart point as `toAffine` of its coordinate triple: if `Spec.map φ ≫ chartι W k = g.1` (φ R-compatible) then `projModelPointsEquiv W K g = Point.toAffine (W.map (algebraMap R K)).toProjective (chartPointTriple W k φ)`.
- **How**: case split on the Z-coordinate `chartPointTriple W k φ 2`. Zero ⇒ infinity branch: `toAffine_of_Z_eq_zero` (mathlib) + `inZChart_iff_of_specMap` to rule out `InZChart`, then `projModelPointsEquivEll_infinity`. Nonzero ⇒ affine branch: nonsingularity via `nonsingular_of_equation_of_ne_zero` (project) from `equation_chartPointTriple`; re-present the point in chart 2 via `chartι_comp_specMap_chartAwayHom_eq` (transition lemma) + `eq_chartAwayHomOfTriple_chartPointTriple`; read out through `chartHomEquiv_eq_of_specMap` and `chartSolutionsEquiv`; conclude by `projModelPointsEquiv_some` + `toAffine_of_Z_ne_zero`/`nonsingular_of_Z_ne_zero` (mathlib), coordinates as `div_eq_mul_inv` of the triple.
- **Hypotheses**: `W` elliptic, `K` field `[DecidableEq K] [Algebra R K]`, `hφ` R-compat, `g : SpecPoints …`, `hg`.
- **Uses (project)**: `projModelPointsEquiv` (PointsDictionary.lean), `projModelPointsEquivEll(_infinity)`, `InZChart`, `inZChart_iff_of_specMap`, `chartHomEquiv(_eq_of_specMap)`, `chartSolutionsEquiv`, `specPoint`-layer (WeierstrassModel.lean), `projModelPointsEquiv_some`, `chartι_comp_specMap_chartAwayHom_eq` (AdditionChartProj.lean), `equation_chartPointTriple`, `chartPointTriple(_self_eq_one)`, `eq_chartAwayHomOfTriple_chartPointTriple`, `chartAwayHomOfTriple(_isLocalizationElem)`, `chartCoordEquiv_mk_X`, `gradeZeroRingEquiv`, `quotientGrading(-Hom)`, `projIdeal`, `mk_X_mem_quotientGrading_one`, `nonsingular_of_equation_of_ne_zero` (AdditionLawOnCurve.lean), `SpecPoints`, `chartι`, `chartAway`.
- **Used by (in file)**: `dictionary_fst_of_pieceZ`, `dictionary_snd_of_pieceZ`, `dictionary_fst_of_pieceY`, `dictionary_snd_of_pieceY`, `dictionary_sum_of_pieceZ`, `dictionary_sum_of_pieceY`, `dictionary_baseChange` (7). **KEY API**.
- **Visibility**: public. **Lines**: 770–870 (**proof 91**).
- **Notes**: PROOF > 30 LINES (91) — prime `/decompose-proof` candidate (natural helpers: infinity branch; the `hfac2` chart-2 re-presentation block; the `hcoord` readout block).

### `chartHom_compat_of_specPoint` — lemma
- **What**: Ring-level compatibility extraction: a chart point that is π-compatible (`(Spec.map φ ≫ chartι W k) ≫ projModelπ W = Spec.map (algebraMap R K)`) has an R-compatible ring map.
- **How**: `chartι_projModelπ` collapses the composite to `Spec.map` of a ring composite; `Spec.map_inj` (Spec-faithfulness) extracts the equation.
- **Uses (project)**: `chartι_projModelπ` (AdditionChartSpec.lean), `chartι`, `chartAway`, `projModelπ`.
- **Used by (in file)**: `dictionary_fst_of_pieceZ`, `dictionary_snd_of_pieceZ`, `dictionary_fst_of_pieceY`, `dictionary_snd_of_pieceY`, `dictionary_sum_of_pieceZ`, `dictionary_sum_of_pieceY`, `dictionary_baseChange` (2 sites) (7). **KEY API**.
- **Visibility**: public. **Lines**: 873–882 (proof 3).

### `dictionary_fst_of_pieceZ` — lemma
- **What**: [e5c-P] Through a law-1 piece presentation of the pair-point (`hgp : pullback.lift P.1 Q.1 w = Spec.map ψ ≫ pieceAwayZι W i j k`), P's dictionary value is `toAffine` of the first tautological image `(ψ∘algebraMap) ∘ biChartPointFst W i j`.
- **How**: set `φP` := composite through the left tensor leg; `hP1` from `pullback.lift_fst` + `specMap_pieceAwayZι_fst`; R-compat via `chartHom_compat_of_specPoint`; apply `dictionary_eq_toAffine`; identify the triple coordinatewise (`dif_pos` diagonal, `tensorLeftLeg_chartCoord` off-diagonal).
- **Hypotheses**: `W` elliptic, `K` field `[DecidableEq K] [Algebra R K]`, `P Q : SpecPoints`, `w`, `ψ`, `hgp`.
- **Uses (project)**: `specMap_pieceAwayZι_fst`, `chartHom_compat_of_specPoint`, `dictionary_eq_toAffine`, `chartPointTriple_self_eq_one`, `tensorLeftLeg_chartCoord` (this file); `SpecPoints`, `projModel(π)`, `projModelPointsEquiv`, `pieceAwayZι`, `biChartPointFst`, `biChartRing(AwayTensorEquiv)`, `chartAway`, `chartι`, `chartCoordEquiv_mk_X`, `lawOneTriple`, `mk_X_mem_quotientGrading_one`.
- **Used by (in file)**: `specPoints_arm_Z` (1).
- **Visibility**: public. **Lines**: 891–934 (**proof 32**).
- **Notes**: PROOF > 30 LINES; one of a 4-fold mirror family (fst/snd × Z/Y) — parametrisation could halve it.

### `dictionary_snd_of_pieceZ` — lemma
- **What**: [e5c-Q] Mirror for Q: dictionary value = `toAffine` of the second tautological image via the right tensor leg.
- **How**: as fst with `pullback.lift_snd`, `specMap_pieceAwayZι_snd`, `tensorRightLeg_chartCoord`, `biChartPointSnd`.
- **Uses (project)**: snd-mirrors + `chartHom_compat_of_specPoint`, `dictionary_eq_toAffine`, `chartPointTriple_self_eq_one`.
- **Used by (in file)**: `specPoints_arm_Z` (1).
- **Visibility**: public. **Lines**: 935–979 (**proof 33**). **Notes**: PROOF > 30 LINES.

### `dictionary_fst_of_pieceY` — lemma
- **What**: [e5c-P, Y] Law-2 mirror of `dictionary_fst_of_pieceZ` (`pieceAwayι`, `lawTwoTriple`).
- **How**: `specMap_pieceAwayι_fst` + `tensorLeftLeg_chartCoord`.
- **Used by (in file)**: `specPoints_arm_Y` (1).
- **Visibility**: public. **Lines**: 981–1024 (**proof 32**). **Notes**: PROOF > 30 LINES.

### `dictionary_snd_of_pieceY` — lemma
- **What**: [e5c-Q, Y] Law-2/snd mirror.
- **How**: `specMap_pieceAwayι_snd` + `tensorRightLeg_chartCoord`.
- **Used by (in file)**: `specPoints_arm_Y` (1).
- **Visibility**: public. **Lines**: 1025–1069 (**proof 33**). **Notes**: PROOF > 30 LINES.

### `dictionary_sum_of_pieceZ` — lemma
- **What**: [e5c-S, Z] The sum-point's dictionary value: if `s.1 = Spec.map ψ ≫ addOnZPieceMor W i j k hΔ` then `dict s = toAffine ((ψ∘algebraMap) ∘ lawOneTriple W i j)`.
- **How**: `φS := ψ ∘ (addOnZPieceHom …).toRingHom`; collapse `Spec.map_comp` to present `s` as a chart-k point; `dictionary_eq_toAffine`; show the φS-triple is the `ψ(invSelf)`-scalar multiple of `χ ∘ lawOneTriple` (diagonal via `awayTriple_mul_invSelf`, off-diagonal via `chartAwayHomOfTriple_isLocalizationElem` + `awayTriple`); strip the unit with mathlib's `Point.toAffine_smul`.
- **Hypotheses**: `W` elliptic, `[IsDomain R] [IsJacobsonRing R]` (× 2 — duplicated binder), `hΔ`, `[IsDomain (biChartRing W i j)]`, `K` field `[DecidableEq K] [Algebra R K]`.
- **Uses (project)**: `dictionary_eq_toAffine`, `chartHom_compat_of_specPoint`, `chartPointTriple(_self_eq_one)`, `chartAwayHomOfTriple_isLocalizationElem` (this file); `addOnZPieceMor` (AdditionChartMor.lean), `addOnZPieceHom` (AdditionChartAway.lean), `awayTriple(_mul_invSelf)`, `lawOneTriple`, `biChartRing`, `chartι`, `chartAway`, `SpecPoints`, `projModelPointsEquiv`.
- **Used by (in file)**: `specPoints_arm_Z` (1).
- **Visibility**: public. **Lines**: 1073–1138 (**proof 54**).
- **Notes**: PROOF > 30 LINES; `[IsJacobsonRing R]` appears twice in the binder list (lines 1075/1076) — redundant hypothesis, cleanup.

### `dictionary_sum_of_pieceY` — lemma
- **What**: [e5c-S, Y] Law-2 mirror: `dict s = toAffine ((ψ∘algebraMap) ∘ lawTwoTriple W i j)` through `addOnYPieceMor`/`addOnYPieceHom`.
- **How**: identical skeleton with law-2 constants; `Point.toAffine_smul`.
- **Uses (project)**: Y-mirrors (`addOnYPieceMor`, `addOnYPieceHom`, `lawTwoTriple`) + shared layer as Z-version.
- **Used by (in file)**: `specPoints_arm_Y` (1).
- **Visibility**: public. **Lines**: 1139–1204 (**proof 54**).
- **Notes**: PROOF > 30 LINES; duplicated `[IsJacobsonRing R]` binder (1141/1142).

### `chi_compat_of_pieceZ` — lemma
- **What**: [χ-compat, Z] The pair-ring evaluation `χ = ψ ∘ algebraMap` is R-compatible, extracted from P's π-condition through the committed piece π-compatibility.
- **How**: `pullback.lift_fst` + `pieceAwayZι_fst_projModelπ` collapse to `Spec.map`; `Spec.map_inj`; re-associate via `IsScalarTower.algebraMap_eq`.
- **Hypotheses**: `K` field `[Algebra R K]`, `P Q`, `w`, `ψ`, `hgp`.
- **Uses (project)**: `pieceAwayZι_fst_projModelπ` (AdditionChartGlobal.lean), `pieceAwayZι`, `lawOneTriple`, `biChartRing`, `SpecPoints`, `projModel(π)`.
- **Used by (in file)**: `specPoints_arm_Z` (1).
- **Visibility**: public. **Lines**: 1207–1226 (proof 9).

### `chi_compat_of_pieceY` — lemma
- **What / How**: [χ-compat, Y] Mirror via `pieceAwayι_fst_projModelπ`.
- **Used by (in file)**: `specPoints_arm_Y` (1).
- **Visibility**: public. **Lines**: 1227–1246 (proof 9).

### `nonsingular_chi_fst` — lemma
- **What**: The χ-image of the first tautological pair point is nonsingular over `K` (its i-th coordinate is 1, hence the triple is nonzero).
- **How**: `equation_biChartPointFst.map χ` + `WeierstrassCurve.map_map`/`hχ` to land on the K-curve; `nonsingular_of_equation_of_ne_zero` (project); nonvanishing from `dif_pos` + `map_one`.
- **Hypotheses**: `W` elliptic, `K` field, `χ` R-compatible.
- **Uses (project)**: `equation_biChartPointFst` (AdditionChartRing.lean), `biChartPointFst`, `biChartRing`, `nonsingular_of_equation_of_ne_zero` (AdditionLawOnCurve.lean).
- **Used by (in file)**: `specPoints_arm_Z`, `specPoints_arm_Y` (2).
- **Visibility**: public. **Lines**: 1248–1264 (proof 13).

### `nonsingular_chi_snd` — lemma
- **What / How**: Mirror for the second point (`equation_biChartPointSnd`, coordinate 1 at index j).
- **Used by (in file)**: `specPoints_arm_Z`, `specPoints_arm_Y` (2).
- **Visibility**: public. **Lines**: 1266–1282 (proof 13).

### `lift_mulModelHom_comp_baseChangeOf` — theorem
- **What**: [C6-e1] The multiplication point pushed to the atlas: `(lift P Q ≫ mulModelHom W) ≫ projModelBaseChangeOf … = (lift P Q ≫ pullbackMapBaseChangeOf …) ≫ WCP.mulModelHom universalWeierstrassLocU …`.
- **How**: unfold `mulModelHom` (the GLC base-change definition) + `mulModelHomBC_baseChange`.
- **Hypotheses**: `W` elliptic, `K` field `[Algebra R K]`, `P Q`, `w`.
- **Uses (project)**: `mulModelHom` (GroupLawConstruction.lean), `mulModelHomBC_baseChange`, `projModelBaseChangeOf`, `pullbackMapBaseChangeOf`, `classifyRingHomU`, `universalWeierstrassLocU(_map_classifyRingHomU)` (AdditionBaseChange.lean), `WCP.mulModelHom`, `SpecPoints`, `projModel(π)`.
- **Used by (in file)**: none.
- **Visibility**: public. **Lines**: 1297–1312 (proof 3).
- **Notes**: UNUSED in file, no cross-file consumers — `mulModelHom_specPoints_of_map` re-derives this at the f-form via `mulModelHom_map_eq_BC` instead. Dead-code candidate.

### `lift_pullbackMap_fst` — theorem
- **What**: [C6-e2, fst] The pushed pair's first projection is P pushed to the atlas.
- **How**: unfold `pullbackMapBaseChangeOf`; `simp [pullback.lift_fst(_assoc)]`.
- **Uses (project)**: `pullbackMapBaseChangeOf`, `projModelBaseChangeOf`, `classifyRingHomU`, `universalWeierstrassLocU(_map_classifyRingHomU)`, `projModelπ`, `SpecPoints`.
- **Used by (in file)**: `lift_pullbackMap_eq_lift` (1).
- **Visibility**: public. **Lines**: 1314–1325 (proof 2).

### `lift_pullbackMap_snd` — theorem
- **What / How**: [C6-e2, snd] Mirror.
- **Used by (in file)**: `lift_pullbackMap_eq_lift` (1).
- **Visibility**: public. **Lines**: 1327–1338 (proof 2).

### `lift_pullbackMap_eq_lift` — theorem
- **What**: [C6-e3] The pushed pair-point IS the atlas-side lift of the pushed points.
- **How**: `pullback.hom_ext` + `lift_pullbackMap_fst/snd` + `pullback.lift_fst/snd`.
- **Used by (in file)**: none.
- **Visibility**: public. **Lines**: 1341–1361 (proof 3).
- **Notes**: UNUSED in file, no cross-file consumers — `mulModelHom_specPoints_of_map` inlines the same `hom_ext` argument (1971–1977). Dead cluster with `lift_pullbackMap_fst/snd` (whose only user is this).

### `descended_lawOne_eq_add` — lemma
- **What**: [C6-e5a, Z] Over the atlas, with the k-th law-1 coordinate a χ-unit, the images of the tautological points are NOT projectively equivalent, so the law-1 triple IS mathlib's `add`: `χ ∘ lawOneTriple = (….map χ).add (χ∘Fst) (χ∘Snd)`.
- **How**: `ringHom_lawOneTriple` + mathlib `add_of_not_equiv`; a putative equivalence `P ≈ Q` would kill `addXYZ` (project `addXYZ_smul_left` + `addXYZ_self'`), contradicting `hunit.ne_zero` at coordinate k.
- **Hypotheses**: `K` field `[DecidableEq K]`, `χ : biChartRing universalWeierstrassLocU i j →+* K`, `hunit`.
- **Uses (project)**: `ringHom_lawOneTriple` (this file); `lawOneTriple`, `biChartRing`, `biChartPointFst/Snd`, `universalWeierstrassLocU`, `WeierstrassAtlasRingU`, `addXYZ_smul_left`, `addXYZ_self'` (AdditionLawOnCurve.lean). Mathlib: `WCP.add_of_not_equiv`.
- **Used by (in file)**: `specPoints_arm_Z` (1).
- **Visibility**: public. **Lines**: 1371–1396 (proof 15).
- **Notes**: stated only at `universalWeierstrassLocU.{u}` — generality note for /generalise.

### `descended_lawTwo_smul_add` — lemma
- **What**: [C6-e5b, Y] The law-2 triple is `add` up to a nonzero scalar: `∃ c ≠ 0, χ ∘ lawTwoTriple = c • (….map χ).add (χ∘Fst) (χ∘Snd)` (on the diagonal `u² • dblXYZ`; off it the certified 2×2 minors give proportionality to `addXYZ`).
- **How**: `by_cases P ≈ Q`. Equiv branch: `dblAddXYZ_smul_left` + `dblAddXYZ_self` (project) + `add_of_equiv` + `dblXYZ_smul` (mathlib), `c := (c₀⁻¹)²`, `field_simp`. Non-equiv branch: three `linear_combination` computations against the certified minor identities `addX_mul_dblAddY`, `addX_mul_dblAddZ`, `addY_mul_dblAddZ` (AdditionLaw.lean), then `exists_eq_smul_of_cross_eq_zero` (AdditionLawField.lean) with nonvanishing of the sum from `nonsingular_add` (mathlib) + `nonsingular_of_equation_of_ne_zero`.
- **Hypotheses**: `[IsDomain (biChartRing universalWeierstrassLocU i j)]`, `K` field `[DecidableEq K]`, `hunit`.
- **Uses (project)**: `ringHom_lawTwoTriple` (this file); `lawTwoTriple`, `dblAddXYZ(_x/_y/_z)`, `dblAddXYZ_smul_left`, `dblAddXYZ_self`, `addX_mul_dblAddY`, `addX_mul_dblAddZ`, `addY_mul_dblAddZ`, `exists_eq_smul_of_cross_eq_zero`, `nonsingular_of_equation_of_ne_zero`, `equation_biChartPointFst/Snd`, `biChartPointFst/Snd`, `biChartRing`, `universalWeierstrassLocU`, `WeierstrassAtlasRingU`. Mathlib: `add_of_equiv/not_equiv`, `dblXYZ_smul`, `nonsingular_add`, `addXYZ`.
- **Used by (in file)**: `specPoints_arm_Y` (1).
- **Visibility**: public. **Lines**: 1399–1486 (**proof 75**).
- **Notes**: PROOF > 30 LINES (75) — decompose candidate (the three minor blocks h01/h02/h12 are natural helpers; lines 1466/1472 exceed 100 chars). Atlas-pinned.

### `specPoints_arm_Z` — lemma
- **What**: [e5c ARM, Z] Complete per-piece assembly at the atlas: from the pair presentation `hgp` and the sum evaluation `hev` (through `addOnZPieceMor`), `dict s = dict P + dict Q`.
- **How**: `chi_compat_of_pieceZ` gives `hχ`; the localized law-entry is a unit via `awayTriple_mul_invSelf` (both orientations discharged by a `first | … | …` combinator); `descended_lawOne_eq_add` rewrites the triple to `add`; `dictionary_sum_of_pieceZ` + mathlib `Point.toAffine_add` (with `nonsingular_chi_fst/snd`) + `dictionary_fst/snd_of_pieceZ` close the square.
- **Hypotheses**: `K` field `[DecidableEq K] [Algebra WeierstrassAtlasRingU K]`, `[IsDomain (biChartRing … i j)]`, `P Q w k ψ hgp s hev`.
- **Uses (project)**: `chi_compat_of_pieceZ`, `descended_lawOne_eq_add`, `dictionary_sum_of_pieceZ`, `dictionary_fst_of_pieceZ`, `dictionary_snd_of_pieceZ`, `nonsingular_chi_fst/snd` (this file); `awayTriple_mul_invSelf`, `addOnZPieceMor`, `pieceAwayZι`, `lawOneTriple`, `universalWeierstrassLocU(.isUnit_Δ)`, `WeierstrassAtlasRingU`, `projModelPointsEquiv`, `SpecPoints`.
- **Used by (in file)**: `mulModelHom_specPoints_atlas` (4 call sites).
- **Visibility**: public. **Lines**: 1490–1552 (**proof 45**).
- **Notes**: PROOF > 30 LINES (45).

### `specPoints_arm_Y` — lemma
- **What**: [e5c ARM, Y] Mirror assembly via `descended_lawTwo_smul_add`, stripping the scalar with `Point.toAffine_smul` before `toAffine_add`.
- **How**: as arm-Z plus the `∃ c` handling (`isUnit_iff_ne_zero`).
- **Uses (project)**: Y-mirrors (`chi_compat_of_pieceY`, `descended_lawTwo_smul_add`, `dictionary_sum_of_pieceY`, `dictionary_fst/snd_of_pieceY`, `addOnYPieceMor`, `pieceAwayι`, `lawTwoTriple`) + `nonsingular_chi_fst/snd`, `awayTriple_mul_invSelf`.
- **Used by (in file)**: `mulModelHom_specPoints_atlas` (4 call sites).
- **Visibility**: public. **Lines**: 1553–1615 (**proof 45**).
- **Notes**: PROOF > 30 LINES (45).

### `mulModelHom_specPoints_atlas` — theorem  ★ atlas keystone
- **What**: **[C6-e5c]** THE ATLAS SPEC: over the ULift universal atlas, the glued two-law multiplication computes the dictionary group law — `dict ⟨lift P Q ≫ WCP.mulModelHom universalWeierstrassLocU …⟩ = dict P + dict Q`.
- **How**: case split by `specPoint_factors_blOpenZ_or_blOpenY`; per case, family descent (`specPoint_addOnZ_family` / `specPoint_addOnY_family`) then `fin_cases p` over the 2×2 family; per member, strengthened descent (`specPoint_addOn{Z,Y}OnImage_factors'`), collapse the evaluation with `WCP.blOpen{Z,Y}_ι_mulModelHom` + `Scheme.homOfLE_ι`, and hand off to `specPoints_arm_Z/Y`. Eight structurally identical arms (2 laws × 4 members) differing only in indices (1 1 / 1 2 / 2 1 / 2 2).
- **Hypotheses**: `K` field `[DecidableEq K] [Algebra WeierstrassAtlasRingU K]`, `P Q`, `w`.
- **Uses (project)**: `specPoint_factors_blOpenZ_or_blOpenY`, `specPoint_addOnZ_family`, `specPoint_addOnY_family`, `specPoint_addOnZOnImage_factors'`, `specPoint_addOnYOnImage_factors'`, `specPoints_arm_Z`, `specPoints_arm_Y` (this file); `WCP.mulModelHom(_projModelπ)`, `WCP.blOpenZ_ι_mulModelHom`, `WCP.blOpenY_ι_mulModelHom` (AdditionChartGlobal.lean), `pieceAwayZι`, `pieceAwayι`, `universalWeierstrassLocU(.isUnit_Δ)`, `projModelPointsEquiv`, `SpecPoints`, `projModel(π)`.
- **Used by (in file)**: `mulModelHom_specPoints_of_map` (1).
- **Visibility**: public. **Lines**: 1618–1776 (**proof 139**).
- **Notes**: PROOF > 30 LINES (139) — the file's biggest `/decompose-proof` target: an index-generic arm helper would collapse the 8 near-verbatim copies to 2.

### `eqToHom_hom_isLocalizationElem` — lemma
- **What**: [e4b] The `eqToHom`-cast of an `Away`-ring along a generator equality carries `isLocalizationElem` (memberships are proof-irrelevant).
- **How**: `subst h; rfl`.
- **Hypotheses**: graded ring `𝒜`, `h : s = t`, grade-1 memberships.
- **Uses (project)**: none — pure mathlib (`CommRingCat`, `HomLoc.Away.isLocalizationElem`).
- **Used by (in file)**: `dictionary_baseChange` (1).
- **Visibility**: public. **Lines**: 1786–1796 (proof 2).
- **Notes**: ForMathlib/upstream candidate.

### `isLocalizationElem_congr_right` — lemma
- **What**: [e4c] `isLocalizationElem` transported along an equality of the numerator generator.
- **How**: `subst h; rfl`.
- **Uses (project)**: none — pure mathlib.
- **Used by (in file)**: `dictionary_baseChange` (1).
- **Visibility**: public. **Lines**: 1800–1807 (proof 2). **Notes**: ForMathlib candidate.

### `dictionary_baseChange` — lemma  ★ D-NAT
- **What**: **[D-NAT] Dictionary naturality along base change**: for `x` a K-point of the base-changed model, `projModelPointsEquiv (W₀.map f) K x = projModelPointsEquiv W₀ K ⟨x.1 ≫ projModelBaseChange f W₀, …⟩`, with `Algebra U K := ((algebraMap R K).comp f).toAlgebra` (statement-level `letI`).
- **How**: `by_cases InZChart (W₀.map f) x`. Chart branch: present `x` as `Spec.map φ ≫ chartι … 2` via `Spec.preimage`; apply `dictionary_eq_toAffine` on BOTH sides (push via `specMap_chartι_comp_baseChange`); identify the two triples with `bcChartAwayMap_isLocalizationElem` + `eqToHom_hom_isLocalizationElem` + `isLocalizationElem_congr_right` + `baseChangeGradedHom_chartGen`. Infinity branch: `specPoint_eq_zero_of_not_inZ`, `projModelZero_baseChange`, `projModelPointsEquiv_zero` on both sides.
- **Hypotheses**: `[W₀.IsElliptic]` AND `[(W₀.map f).IsElliptic]`, `K` field `[DecidableEq K] [Algebra R K]`.
- **Uses (project)**: `dictionary_eq_toAffine`, `chartHom_compat_of_specPoint`, `specMap_chartι_comp_baseChange`, `bcChartAwayMap(_isLocalizationElem)`, `baseChangeGradedHom_chartGen`, `eqToHom_hom_isLocalizationElem`, `isLocalizationElem_congr_right`, `chartPointTriple` (this file); `InZChart`, `specPoint_eq_zero_of_not_inZ`, `projModelPointsEquiv(_zero)`, `projModelBaseChange(_π)`, `projModelZero(_baseChange/_projModelπ)`, `chartι`, `chartAway`, `mk_X_mem_quotientGrading_one`, `SpecPoints`.
- **Used by (in file)**: `mulModelHom_specPoints_of_map` (3 rewrite sites) (1).
- **Visibility**: public. **Lines**: 1809–1888 (**proof 64**).
- **Notes**: PROOF > 30 LINES (64) — decompose candidate (two clean branches).

### `mulModelHom_universalWeierstrassLocU` — theorem  ★ atlas bridge
- **What**: **[C6-U] THE ATLAS BRIDGE**: over the ULift universal atlas, GLC's base-change multiplication IS the glued two-law multiplication: `mulModelHom universalWeierstrassLocU = WCP.mulModelHom universalWeierstrassLocU universalWeierstrassLocU.isUnit_Δ`.
- **How**: unfold `mulModelHom`; `mulModelHomBC_congr` at `classifyRingHomU_universalWeierstrassLocU` (classify collapses to `RingHom.id`); finish by `mulModelHomBC_id`.
- **Uses (project)**: `mulModelHom` (GroupLawConstruction.lean), `mulModelHomBC_congr`, `mulModelHomBC_id`, `classifyRingHomU(_universalWeierstrassLocU)`, `universalWeierstrassLocU(_map_classifyRingHomU)` (AdditionBaseChange.lean), `WCP.mulModelHom`.
- **Used by (in file)**: none. Cross-file: `GroupLawAxioms.lean` (≥3 sites: 625, 867, 1168).
- **Visibility**: public. **Lines**: 1894–1905 (proof 6).
- **Notes**: exported API — unused in file but load-bearing downstream.

### `mulModelHom_map_eq_BC` — lemma
- **What**: The multiplication at a mapped curve is the f-form base-change lift: `mulModelHom (universalWeierstrassLocU.map f) = mulModelHomBC f universalWeierstrassLocU … rfl` (classify collapses).
- **How**: `mulModelHomBC_congr` with `classifyRingHomU_map` + `classifyRingHomU_universalWeierstrassLocU` + `RingHom.comp_id`.
- **Hypotheses**: `[(universalWeierstrassLocU.map f).IsElliptic]`.
- **Uses (project)**: `mulModelHom`, `mulModelHomBC(_congr)`, `classifyRingHomU_map`, `classifyRingHomU_universalWeierstrassLocU`, `universalWeierstrassLocU`, `WeierstrassAtlasRingU`.
- **Used by (in file)**: `mulModelHom_specPoints_of_map` (1).
- **Visibility**: public. **Lines**: 1911–1921 (proof 5).

### `mulModelHom_specPoints_of_map` — theorem
- **What**: The c6 spec at a mapped curve `universalWeierstrassLocU.map f`: `dict ⟨lift P Q ≫ mulModelHom (….map f)⟩ = dict P + dict Q`, transported from the atlas by D-NAT + the f-form push.
- **How**: rewrite all three dictionary values with `dictionary_baseChange`; `hw'` compat square via `projModelBaseChange_π`; `hBC` from `projModelBaseChangeOf_rfl` + `mulModelHomBC_baseChange`; `hpush` via `mulModelHom_map_eq_BC` + inline `pullback.hom_ext`; conclude with `mulModelHom_specPoints_atlas` at the pushed pair (`Subtype.ext`).
- **Hypotheses**: `[(….map f).IsElliptic]`, `K` field `[DecidableEq K] [Algebra R K]`; `letI Algebra WeierstrassAtlasRingU K` set inside.
- **Uses (project)**: `dictionary_baseChange`, `mulModelHom_map_eq_BC`, `mulModelHom_specPoints_atlas` (this file); `mulModelHom(_π)` (GroupLawConstruction.lean), `mulModelHomBC(_baseChange)`, `projModelBaseChangeOf(_rfl)`, `pullbackMapBaseChangeOf`, `projModelBaseChange(_π)`, `WCP.mulModelHom`, `universalWeierstrassLocU`, `WeierstrassAtlasRingU`, `projModelPointsEquiv`, `SpecPoints`.
- **Used by (in file)**: `mulModelHom_specPoints_of_eq` (1).
- **Visibility**: public. **Lines**: 1923–1997 (**proof 62**).
- **Notes**: PROOF > 30 LINES (62); the three near-identical π-compat side-goals (1984–1997) are a small helper candidate.

### `mulModelHom_specPoints_of_eq` — theorem
- **What**: The c6 spec against an equality witness `h : universalWeierstrassLocU.map f = W` — the `subst`-friendly form (f and W independent, tied only by h), so instantiation yields the spec for EVERY elliptic W with no dependent-rewrite pain.
- **How**: `subst h; exact mulModelHom_specPoints_of_map f K P Q w`.
- **Uses (project)**: `mulModelHom_specPoints_of_map` (this file); `mulModelHom(_π)`, `WeierstrassAtlasRingU`, `projModelPointsEquiv`, `SpecPoints`, `projModel(π)`.
- **Used by (in file)**: `mulModelHom_specPoints` (1).
- **Visibility**: public. **Lines**: 1999–2013 (proof 2).

### `mulModelHom_specPoints` — theorem  ★★ THE SPEC (file keystone)
- **What**: **(T-W7.0c·c6, [C6] COMPLETE)** On field points, `mulModelHom` is mathlib's `Point.add` through the dictionary, for every pair over every ring: `projModelPointsEquiv W K ⟨lift P Q ≫ mulModelHom W, …⟩ = dict P + dict Q`. Source: Bosma–Lenstra Thm 2 + mathlib `Affine.Point.add`.
- **How**: term-mode instantiation of `mulModelHom_specPoints_of_eq` at `f := classifyRingHomU W`, `h := universalWeierstrassLocU_map_classifyRingHomU W`.
- **Hypotheses**: `W : WeierstrassCurve R` `[W.IsElliptic]`, `K` field `[DecidableEq K] [Algebra R K]`, `P Q : SpecPoints`.
- **Uses (project)**: `mulModelHom_specPoints_of_eq` (this file); `classifyRingHomU`, `universalWeierstrassLocU_map_classifyRingHomU` (AdditionBaseChange.lean), `mulModelHom(_π)`, `projModelPointsEquiv`, `SpecPoints`.
- **Used by (in file)**: none. Cross-file: `GroupLawAxioms.lean` — the keystone consumed by every group axiom (≥9 sites: 179, 181, 246, 247, 260, 261, 425, 504, 557).
- **Visibility**: public. **Lines**: 2015–2029 (term proof 2).
- **Notes**: the file's raison d'être; exported API.

---

### File Summary

- **Totals**: 68 declarations — 24 `theorem`, 42 `lemma`, 2 `noncomputable def` (`bcChartAwayMap`, `chartPointTriple`). 2,033 lines. All inside `namespace ModularCurves`; single import `GroupLawConstruction`; sole importer `GroupLawAxioms.lean`. No `instance`s, no attributes on declarations; `attribute [local instance] MvPolynomial.gradedAlgebra` appears 4× (lines 523, 631, 889, 1784).
- **Key API (3+ in-file users)**:
  - `chartPointTriple` (def) — 13 users (the file's central gadget)
  - `chartPointTriple_self_eq_one` — 8
  - `dictionary_eq_toAffine` — 7 (mid-layer keystone)
  - `chartHom_compat_of_specPoint` — 7
  - `specPoint_factors_iSup` — 6
  - `bcChartAwayMap` (def) — 5
  - `chartAwayHomOfTriple_isLocalizationElem` — 4
  - `baseChangeGradedHom_chartGen` — 3
- **Unused-in-file** (11): `specPoint_mulModelHom_of_blOpenZ`, `specPoint_mulModelHom_of_blOpenY`, `specPoint_addOnZOnImage_factors`, `specPoint_addOnYOnImage_factors` (both subsumed by their primed versions), `addOnZPieceHom_coord`, `addOnYPieceHom_coord`, `chartPointTriple_self`, `lift_mulModelHom_comp_baseChangeOf`, `lift_pullbackMap_eq_lift`, `mulModelHom_universalWeierstrassLocU`, `mulModelHom_specPoints`. Of these, the last two ARE consumed cross-file by `GroupLawAxioms.lean` (exported API); the other **9 have zero consumers anywhere** — dead-code/dedup candidates (plus `lift_pullbackMap_fst/snd`, whose only user is the dead `lift_pullbackMap_eq_lift`).
- **CODE-sorry**: **ZERO** (verified: `grep -E '\bsorry\b|\badmit\b'` → no hits).
- **set_option**: **ZERO** (verified).
- **Proofs > 30 lines** (13 — all `/decompose-proof` candidates, proof-body line counts):
  1. `mulModelHom_specPoints_atlas` — 139 (8 near-verbatim arms; biggest win)
  2. `dictionary_eq_toAffine` — 91
  3. `descended_lawTwo_smul_add` — 75
  4. `dictionary_baseChange` — 64
  5. `mulModelHom_specPoints_of_map` — 62
  6. `dictionary_sum_of_pieceZ` — 54
  7. `dictionary_sum_of_pieceY` — 54
  8. `specPoints_arm_Z` — 45
  9. `specPoints_arm_Y` — 45
  10. `dictionary_snd_of_pieceZ` — 33
  11. `dictionary_snd_of_pieceY` — 33
  12. `dictionary_fst_of_pieceZ` — 32
  13. `dictionary_fst_of_pieceY` — 32
  (Borderline at exactly 30: `specPoint_addOnZOnImage_factors'`, `specPoint_addOnYOnImage_factors'`.)
- **Private/public**: 0 private / 68 public.
- **Other observations**: pervasive Z/Y (law-1/law-2) and fst/snd mirror duplication (~14 mirror pairs — parametrisation opportunity); `blOpenZImage_ι_eq`/`blOpenYImage_ι_eq` carry a spurious unused `(k : Fin 3)` binder; `[IsJacobsonRing R]` duplicated in the binders of `dictionary_sum_of_pieceZ/Y`; duplicate `variable (i j …)` re-declaration at lines 90/129; 3 declarations are project-independent mathlib material (`specPoint_factors_iSup`, `Proj_awayι_congr`, `eqToHom_hom_isLocalizationElem`/`isLocalizationElem_congr_right` — ForMathlib candidates); atlas-layer lemmas (`descended_*`, `specPoints_arm_*`, `*_atlas`) are pinned to `universalWeierstrassLocU.{u}`.
