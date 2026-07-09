import ModularCurves.EllipticCurve.AdditionChartOpen
import ModularCurves.EllipticCurve.AdditionChartTransition
import ModularCurves.ForMathlib.AwayLiftAlgHom

/-!
# The two Bosma–Lenstra laws on `E ×_R E` (T-W7.0c-c5β, c4.3 assembly)

The per-chart-product laws (`addOnYOnSup`, `addOnZOnSup`, f91b91ec) are assembled into morphisms on
opens of `E ×_R E` itself.

**Why four chart-products, not nine.** `E` is covered by its `Y`- and `Z`-charts alone: a point with
`y = z = 0` would be `[1:0:0]`, and the Weierstrass equation forces `x = 0` there, so no such point
lies on the curve. Accordingly the covering chart-products of `E ×_R E` are the four
`(i,j) ∈ {1,2}²`, and those are exactly the pairs whose chart-product ring is known to be a domain
(`instIsDomainBiChartRing{YY,YZ,ZY,ZZ}`, d38f52b9 + 7c9ddc07) — which is what
`equation_lawTwoTriple_of_isDomain` needs. The family is therefore indexed by `Fin 2 × Fin 2`, and
each branch is spelled with a *literal* index so the domain instances fire.

Each piece is transported into `E ×_R E` along `pieceι` (an open immersion) using
`Scheme.Hom.isoImage`. The `iSup` form `⨆ k, blOpenYPieceFamily` is used throughout rather than
`blOpenYPiece`: the two are equal (`iSup_blOpenYPieceFamily`), but `addOnYOnSup` already lives on the
former, and a `▸` transport across that equality would be gratuitous.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- `D(1) = ⊤`. -/
lemma specBasicOpen_one (A : CommRingCat) : specBasicOpen A 1 = ⊤ :=
  PrimeSpectrum.basicOpen_one

section Opens

/-- The `(i,j)` chart-product's law-2 regularity open, pushed into `E ×_R E`. -/
noncomputable def blOpenYImage (i j : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  pieceι W i j ''ᵁ (⨆ k, blOpenYPieceFamily W i j k)

/-- The `(i,j)` chart-product's law-1 regularity open, pushed into `E ×_R E`. -/
noncomputable def blOpenZImage (i j : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  pieceι W i j ''ᵁ (⨆ k, blOpenZPieceFamily W i j k)

/-- The four covering chart-products, `{Y,Z}²`. The indices are literals so that the
`IsDomain (biChartRing W i j)` instances apply in each branch. -/
noncomputable def blOpenYFamily : Fin 2 × Fin 2 → (pullback (projModelπ W) (projModelπ W)).Opens
  | (0, 0) => blOpenYImage W 1 1
  | (0, 1) => blOpenYImage W 1 2
  | (1, 0) => blOpenYImage W 2 1
  | (1, 1) => blOpenYImage W 2 2

/-- The law-1 analogue of `blOpenYFamily`. -/
noncomputable def blOpenZFamily : Fin 2 × Fin 2 → (pullback (projModelπ W) (projModelπ W)).Opens
  | (0, 0) => blOpenZImage W 1 1
  | (0, 1) => blOpenZImage W 1 2
  | (1, 0) => blOpenZImage W 2 1
  | (1, 1) => blOpenZImage W 2 2

/-- **(T-W7.0c·c1-Y, the open)** The regularity open of the second Bosma–Lenstra law on `E ×_R E`. -/
noncomputable def blOpenY : (pullback (projModelπ W) (projModelπ W)).Opens :=
  ⨆ p, blOpenYFamily W p

/-- **(T-W7.0c·c1-Z, the open)** The regularity open of the first Bosma–Lenstra law (mathlib's
`addXYZ`) on `E ×_R E`. -/
noncomputable def blOpenZ : (pullback (projModelπ W) (projModelπ W)).Opens :=
  ⨆ p, blOpenZFamily W p

/-- `blOpenYImage` is the union of the images of its regularity pieces (`image_iSup`). -/
lemma blOpenYImage_eq_iSup (i j : Fin 3) :
    blOpenYImage W i j = ⨆ k, pieceι W i j ''ᵁ blOpenYPieceFamily W i j k := by
  rw [blOpenYImage, Scheme.Hom.image_iSup]

/-- The law-1 analogue of `blOpenYImage_eq_iSup`. -/
lemma blOpenZImage_eq_iSup (i j : Fin 3) :
    blOpenZImage W i j = ⨆ k, pieceι W i j ''ᵁ blOpenZPieceFamily W i j k := by
  rw [blOpenZImage, Scheme.Hom.image_iSup]

/-- The overlap of two law-2 regularity images is covered by the `(k,k')` piece-image overlaps
(`image_iSup` on each factor + `iSup_inf_iSup`). -/
lemma blOpenYImage_inf_eq_iSup (i j i' j' : Fin 3) :
    blOpenYImage W i j ⊓ blOpenYImage W i' j' =
      ⨆ p : Fin 3 × Fin 3, (pieceι W i j ''ᵁ blOpenYPieceFamily W i j p.1) ⊓
        (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' p.2) := by
  rw [blOpenYImage_eq_iSup, blOpenYImage_eq_iSup, iSup_inf_iSup]

/-- The law-1 analogue of `blOpenYImage_inf_eq_iSup`. -/
lemma blOpenZImage_inf_eq_iSup (i j i' j' : Fin 3) :
    blOpenZImage W i j ⊓ blOpenZImage W i' j' =
      ⨆ p : Fin 3 × Fin 3, (pieceι W i j ''ᵁ blOpenZPieceFamily W i j p.1) ⊓
        (pieceι W i' j' ''ᵁ blOpenZPieceFamily W i' j' p.2) := by
  rw [blOpenZImage_eq_iSup, blOpenZImage_eq_iSup, iSup_inf_iSup]

/-- The cover of `blOpenY` by the four chart-products' regularity opens. -/
noncomputable def blOpenYCover : (blOpenY W).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (blOpenYFamily W)

/-- The cover of `blOpenZ` by the four chart-products' regularity opens. -/
noncomputable def blOpenZCover : (blOpenZ W).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover (blOpenZFamily W)

end Opens

section Morphisms

variable [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ)

/-- The law-2 morphism on the image of the `(i,j)` chart-product's regularity open. -/
noncomputable def addOnYOnImage (i j : Fin 3) [IsDomain (biChartRing W i j)] :
    (blOpenYImage W i j).toScheme ⟶ projModel W :=
  (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenYPieceFamily W i j k)).inv ≫
    addOnYOnSup W i j hΔ

/-- The law-1 morphism on the image of the `(i,j)` chart-product's regularity open. -/
noncomputable def addOnZOnImage (i j : Fin 3) [IsDomain (biChartRing W i j)] :
    (blOpenZImage W i j).toScheme ⟶ projModel W :=
  (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenZPieceFamily W i j k)).inv ≫
    addOnZOnSup W i j hΔ

/-- The law-2 morphisms on the four covering chart-products. -/
noncomputable def addOnYFamily : ∀ p : Fin 2 × Fin 2, (blOpenYFamily W p).toScheme ⟶ projModel W
  | (0, 0) => addOnYOnImage W hΔ 1 1
  | (0, 1) => addOnYOnImage W hΔ 1 2
  | (1, 0) => addOnYOnImage W hΔ 2 1
  | (1, 1) => addOnYOnImage W hΔ 2 2

/-- The law-1 morphisms on the four covering chart-products. -/
noncomputable def addOnZFamily : ∀ p : Fin 2 × Fin 2, (blOpenZFamily W p).toScheme ⟶ projModel W
  | (0, 0) => addOnZOnImage W hΔ 1 1
  | (0, 1) => addOnZOnImage W hΔ 1 2
  | (1, 0) => addOnZOnImage W hΔ 2 1
  | (1, 1) => addOnZOnImage W hΔ 2 2

omit [IsDomain R] in
/-- **(bridge, law 2)** On the `k`-th image piece, `addOnYOnImage` is `addOnYOnFamily k` read through
`pieceι.isoImage` — the general `homOfLE_isoImage_inv_iSup` (ForMathlib) at `pieceι`, plus the
interface `ι_addOnYOnSup`. -/
lemma addOnYOnImage_piece (i j : Fin 3) [IsDomain (biChartRing W i j)] (k : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k)) ≫
        addOnYOnImage W hΔ i j =
      (Scheme.Hom.isoImage (pieceι W i j) (blOpenYPieceFamily W i j k)).inv ≫
        addOnYOnFamily W i j k hΔ := by
  rw [addOnYOnImage]
  refine (homOfLE_isoImage_inv_iSup (pieceι W i j) (blOpenYPieceFamily W i j) k
    (addOnYOnSup W i j hΔ)).trans ?_
  exact congrArg (_ ≫ ·) (ι_addOnYOnSup W i j hΔ k)

omit [IsDomain R] in
/-- **(bridge, law 1)** -/
lemma addOnZOnImage_piece (i j : Fin 3) [IsDomain (biChartRing W i j)] (k : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k)) ≫
        addOnZOnImage W hΔ i j =
      (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
        addOnZOnFamily W i j k hΔ := by
  rw [addOnZOnImage]
  refine (homOfLE_isoImage_inv_iSup (pieceι W i j) (blOpenZPieceFamily W i j) k
    (addOnZOnSup W i j hΔ)).trans ?_
  exact congrArg (_ ≫ ·) (ι_addOnZOnSup W i j hΔ k)

omit [IsDomain R] in
/-- **([C4-HF-ASSEMBLY] L1)** On any open `P` inside the k-th image piece,
`homOfLE ≫ addOnYOnImage ij` factors as `σ ≫ addOnYPieceMor ij k`, where the prefactor `σ` is the
`isoImage / morphismRestrict / specBasicOpenIsoAway.inv` chain landing in `Spec(Away(lawTwoTriple ij k))`.
This is the entry point that turns the image-level morphism into the `pieceMorOfTriple` form the crux
consumes. Uses only `addOnYOnImage_piece`'s own `isoImage`, so there is no second-copy cancellation. -/
lemma homOfLE_addOnYOnImage_eq (i j : Fin 3) [IsDomain (biChartRing W i j)] (hΔ : IsUnit W.Δ)
    (k : Fin 3) (P : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hP : P ≤ pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (hP.trans ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k))) ≫
        addOnYOnImage W hΔ i j =
      ((pullback (projModelπ W) (projModelπ W)).homOfLE hP ≫
        (Scheme.Hom.isoImage (pieceι W i j) (blOpenYPieceFamily W i j k)).inv ≫
        morphismRestrict (chartPieceIso W i j).hom
          (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
        (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
          (lawTwoTriple W i j k)).inv) ≫ addOnYPieceMor W i j k hΔ := by
  rw [← Scheme.homOfLE_homOfLE _ hP
      ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k)),
    Category.assoc, addOnYOnImage_piece, addOnYOnFamily]
  simp only [Category.assoc]

omit [IsDomain R] in
/-- **([C4-HF-ASSEMBLY] L1, law 1)** -/
lemma homOfLE_addOnZOnImage_eq (i j : Fin 3) [IsDomain (biChartRing W i j)] (hΔ : IsUnit W.Δ)
    (k : Fin 3) (P : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hP : P ≤ pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (hP.trans ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))) ≫
        addOnZOnImage W hΔ i j =
      ((pullback (projModelπ W) (projModelπ W)).homOfLE hP ≫
        (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
        morphismRestrict (chartPieceIso W i j).hom
          (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
        (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
          (lawOneTriple W i j k)).inv) ≫ addOnZPieceMor W i j k hΔ := by
  rw [← Scheme.homOfLE_homOfLE _ hP
      ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k)),
    Category.assoc, addOnZOnImage_piece, addOnZOnFamily]
  simp only [Category.assoc]

end Morphisms

section Overlap

variable (i j i' j' : Fin 3)

/-- `Spec` of the localization map into the overlap ring IS the basic-open immersion `D(τ) ↪ Spec B`,
where `τ = transFst · transSnd` is the product of the two transition coordinates.

`transRing` is by definition `Localization.Away τ` over `biChartRing W i j`, and `transAlgHom` is by
definition its structure map — so this is `specBasicOpenIsoAway_hom_ι` (1a917a1e) read backwards. -/
lemma transAlgHom_toRingHom :
    CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom =
      CommRingCat.ofHom (algebraMap (CommRingCat.of (biChartRing W i j))
        (Localization.Away (transFst W i j i' * transSnd W i j j'))) :=
  rfl

lemma specMap_transAlgHom_eq :
    Spec.map (CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom) =
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
          (transFst W i j i' * transSnd W i j j')).hom ≫
        (specBasicOpen (CommRingCat.of (biChartRing W i j))
          (transFst W i j i' * transSnd W i j j')).ι := by
  rw [transAlgHom_toRingHom]
  exact (specBasicOpenIsoAway_hom_ι (CommRingCat.of (biChartRing W i j))
    (transFst W i j i' * transSnd W i j j')).symm

/-- Hence the overlap sits inside the `(i,j)` chart-product as an open subscheme. -/
instance instIsOpenImmersionSpecMapTransAlgHom :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom)) := by
  rw [specMap_transAlgHom_eq]
  infer_instance

lemma specMap_transAlgHom_opensRange :
    (Spec.map (CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom)).opensRange =
      specBasicOpen (CommRingCat.of (biChartRing W i j))
        (transFst W i j i' * transSnd W i j j') := by
  simp only [specMap_transAlgHom_eq, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι]


/-- The overlap of the `(i,j)` and `(i',j')` chart-products, as an open subscheme of `E ×_R E`.
It is the image of `Spec transRing`; the map exhibiting it is an open immersion, being
`Spec` of a localization followed by two open immersions. -/
noncomputable def transι :
    Spec (CommRingCat.of (transRing W i j i' j')) ⟶
      pullback (projModelπ W) (projModelπ W) :=
  Spec.map (CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom) ≫
    (chartPieceIso W i j).inv ≫ pieceι W i j

instance instIsOpenImmersionTransι : IsOpenImmersion (transι W i j i' j') := by
  rw [transι]
  infer_instance

/-- `pullback.fst`/`.snd` cut `range(pieceι)` into the two chart ranges (`PullbackCarrier.range_map`). -/
lemma pieceι_opensRange :
    (pieceι W i j).opensRange =
      pullback.fst (projModelπ W) (projModelπ W) ⁻¹ᵁ (chartι W i).opensRange ⊓
        pullback.snd (projModelπ W) (projModelπ W) ⁻¹ᵁ (chartι W j).opensRange := by
  apply TopologicalSpace.Opens.ext
  show Set.range (pieceι W i j).base = _
  rw [pieceι, Scheme.Pullback.range_map]
  rfl

/-- The overlap open, `range(transι)`, is `D(τ)` pushed into the `(i,j)` chart-product. -/
lemma transι_opensRange :
    (transι W i j i' j').opensRange =
      pieceι W i j ''ᵁ ((chartPieceIso W i j).hom ⁻¹ᵁ
        specBasicOpen (CommRingCat.of (biChartRing W i j))
          (transFst W i j i' * transSnd W i j j')) := by
  show (Spec.map (CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom) ≫
    (chartPieceIso W i j).inv ≫ pieceι W i j).opensRange = _
  rw [Scheme.Hom.opensRange_comp, specMap_transAlgHom_opensRange, Scheme.Hom.comp_image,
    Scheme.Hom.inv_image]

/-- **(helper A, final leaf — fst)** The left tensor inclusion carries mathlib's transition element
`isLocalizationElem X_i X_{i'}` to the repo's transition coordinate `transFst = X_{i'}/X_i`. Both
name "the ratio `X_{i'}/X_i`"; the identification is `chartCoordEquiv_mk_X` (WeierstrassModel:791,
already proven) composed with `awayTensorEquiv_symm_tmul_one` + `biChartRingTensorEquiv_mk_rename_inl`. -/
lemma awayTensorEquiv_symm_isLocalizationElem_fst (hi' : i' ≠ i) :
    (biChartRingAwayTensorEquiv W i j).symm
        (Away.isLocalizationElem (mk_X_mem_quotientGrading_one W i)
          (mk_X_mem_quotientGrading_one W i') ⊗ₜ[R] 1) =
      transFst W i j i' := by
  rw [← chartCoordEquiv_mk_X W i ⟨i', hi'⟩,
    show chartCoordEquiv W i (Ideal.Quotient.mk _ (X ⟨i', hi'⟩)) =
      chartCoordAlgEquiv W i (Ideal.Quotient.mk _ (X ⟨i', hi'⟩)) from rfl,
    awayTensorEquiv_symm_tmul_one, transFst, biChartPointFst, dif_neg hi',
    ← rename_X (R := R) (Sum.inl : {k : Fin 3 // k ≠ i} → _) ⟨i', hi'⟩,
    ← biChartRingTensorEquiv_mk_rename_inl W i j (X ⟨i', hi'⟩), AlgEquiv.symm_apply_apply]

/-- **(helper A, final leaf — snd)** The right tensor inclusion carries `isLocalizationElem X_j X_{j'}`
to `transSnd = X_{j'}/X_j`. -/
lemma awayTensorEquiv_symm_isLocalizationElem_snd (hj' : j' ≠ j) :
    (biChartRingAwayTensorEquiv W i j).symm
        ((1 : chartAway W i) ⊗ₜ[R] Away.isLocalizationElem (mk_X_mem_quotientGrading_one W j)
          (mk_X_mem_quotientGrading_one W j')) =
      transSnd W i j j' := by
  rw [← chartCoordEquiv_mk_X W j ⟨j', hj'⟩,
    show chartCoordEquiv W j (Ideal.Quotient.mk _ (X ⟨j', hj'⟩)) =
      chartCoordAlgEquiv W j (Ideal.Quotient.mk _ (X ⟨j', hj'⟩)) from rfl,
    awayTensorEquiv_symm_one_tmul, transSnd, biChartPointSnd, dif_neg hj',
    ← rename_X (R := R) (Sum.inr : {k : Fin 3 // k ≠ j} → _) ⟨j', hj'⟩,
    ← biChartRingTensorEquiv_mk_rename_inr W i j (X ⟨j', hj'⟩), AlgEquiv.symm_apply_apply]

/-- **(the overlap is symmetric)** Read through the `(i',j')` chart-product instead, the same
open subscheme is obtained — this is `specMap_transHom_pieceι` (a468579e). -/
lemma transι_eq :
    transι W i j i' j' =
      Spec.map (CommRingCat.ofHom (transHom W i j i' j').toRingHom) ≫
        (chartPieceIso W i' j').inv ≫ pieceι W i' j' :=
  (specMap_transHom_pieceι W i j i' j').symm

private lemma fst_side (hi' : i' ≠ i) :
    pieceι W i j ⁻¹ᵁ (pullback.fst (projModelπ W) (projModelπ W) ⁻¹ᵁ (chartι W i').opensRange) ≤
      (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
        (transFst W i j i') := by
  have hfst := (Iso.inv_comp_eq (chartPieceIso W i j)).mp (chartPieceIso_inv_fst W i j)
  rw [← Scheme.Hom.comp_preimage, pieceι_fst, Scheme.Hom.comp_preimage, hfst,
    Scheme.Hom.comp_preimage]
  refine Scheme.Hom.preimage_mono _ ?_
  rw [Proj.opensRange_awayι,
    Proj.awayι_preimage_basicOpen (𝒜 := (projIdeal W).quotientGrading)
      (f_deg := mk_X_mem_quotientGrading_one W i) (hm := one_pos)
      (g_deg := mk_X_mem_quotientGrading_one W i') (hm' := one_pos),
    SpecMap_preimage_basicOpen]
  apply le_of_eq; congr 1
  rw [show (CommRingCat.ofHom ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (A := chartAway W i) (B := chartAway W j)))).hom
      (Away.isLocalizationElem (mk_X_mem_quotientGrading_one W i)
        (mk_X_mem_quotientGrading_one W i')) =
      (biChartRingAwayTensorEquiv W i j).symm
        (Away.isLocalizationElem (mk_X_mem_quotientGrading_one W i)
          (mk_X_mem_quotientGrading_one W i') ⊗ₜ[R] 1) from rfl,
    awayTensorEquiv_symm_isLocalizationElem_fst W i j i' hi']

private lemma snd_side (hj' : j' ≠ j) :
    pieceι W i j ⁻¹ᵁ (pullback.snd (projModelπ W) (projModelπ W) ⁻¹ᵁ (chartι W j').opensRange) ≤
      (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
        (transSnd W i j j') := by
  have hsnd := (Iso.inv_comp_eq (chartPieceIso W i j)).mp (chartPieceIso_inv_snd W i j)
  rw [← Scheme.Hom.comp_preimage, pieceι_snd, Scheme.Hom.comp_preimage, hsnd,
    Scheme.Hom.comp_preimage]
  refine Scheme.Hom.preimage_mono _ ?_
  rw [Proj.opensRange_awayι,
    Proj.awayι_preimage_basicOpen (𝒜 := (projIdeal W).quotientGrading)
      (f_deg := mk_X_mem_quotientGrading_one W j) (hm := one_pos)
      (g_deg := mk_X_mem_quotientGrading_one W j') (hm' := one_pos),
    SpecMap_preimage_basicOpen]
  apply le_of_eq; congr 1
  rw [show (CommRingCat.ofHom ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := chartAway W i)
        (B := chartAway W j)).toRingHom)).hom
      (Away.isLocalizationElem (mk_X_mem_quotientGrading_one W j)
        (mk_X_mem_quotientGrading_one W j')) =
      (biChartRingAwayTensorEquiv W i j).symm
        ((1 : chartAway W i) ⊗ₜ[R] Away.isLocalizationElem (mk_X_mem_quotientGrading_one W j)
          (mk_X_mem_quotientGrading_one W j')) from rfl,
    awayTensorEquiv_symm_isLocalizationElem_snd W i j j' hj']

private lemma fstLe :
    pieceι W i j ⁻¹ᵁ (pullback.fst (projModelπ W) (projModelπ W) ⁻¹ᵁ (chartι W i').opensRange) ≤
      (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
        (transFst W i j i') := by
  obtain rfl | hi' := eq_or_ne i' i
  · rw [transFst, biChartPointFst, dif_pos rfl, specBasicOpen_one, Scheme.Hom.preimage_top]
    exact le_top
  · exact fst_side W i j i' hi'

private lemma sndLe :
    pieceι W i j ⁻¹ᵁ (pullback.snd (projModelπ W) (projModelπ W) ⁻¹ᵁ (chartι W j').opensRange) ≤
      (chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
        (transSnd W i j j') := by
  obtain rfl | hj' := eq_or_ne j' j
  · rw [transSnd, biChartPointSnd, dif_pos rfl, specBasicOpen_one, Scheme.Hom.preimage_top]
    exact le_top
  · exact snd_side W i j j' hj'

/-- **(helper A, A0)** The two chart-products of `E ×_R E` overlap exactly within the transition
locus: their images meet inside `range(transι)`. Every leaf proven — this is the assembly. -/
lemma pieceι_range_inf_le_transι :
    (pieceι W i j).opensRange ⊓ (pieceι W i' j').opensRange ≤
      (transι W i j i' j').opensRange := by
  rw [transι_opensRange, ← Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.image_le_image_iff, pieceι_opensRange W i' j', specBasicOpen_mul]
  simp only [Scheme.Hom.preimage_inf]
  exact inf_le_inf (fstLe W i j i') (sndLe W i j j')

lemma blOpenYImage_le_range : blOpenYImage W i j ≤ (pieceι W i j).opensRange := by
  rw [blOpenYImage, ← Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.image_mono _ le_top

lemma blOpenZImage_le_range : blOpenZImage W i j ≤ (pieceι W i j).opensRange := by
  rw [blOpenZImage, ← Scheme.Hom.image_top_eq_opensRange]
  exact Scheme.Hom.image_mono _ le_top

/-- **(helper A — law 2)** The overlap of two chart-products' law-2 regularity images lies inside
`range(transι)` — the containment `IsOpenImmersion.lift` needs to factor `hf` through the transition. -/
lemma blOpenYImage_inf_le_transι :
    blOpenYImage W i j ⊓ blOpenYImage W i' j' ≤ (transι W i j i' j').opensRange :=
  le_trans (inf_le_inf (blOpenYImage_le_range W i j) (blOpenYImage_le_range W i' j'))
    (pieceι_range_inf_le_transι W i j i' j')

/-- **(helper A — law 1)** -/
lemma blOpenZImage_inf_le_transι :
    blOpenZImage W i j ⊓ blOpenZImage W i' j' ≤ (transι W i j i' j').opensRange :=
  le_trans (inf_le_inf (blOpenZImage_le_range W i j) (blOpenZImage_le_range W i' j'))
    (pieceι_range_inf_le_transι W i j i' j')

/-- **([C4-HF-ASSEMBLY] L2a)** The preimage under `transι` (via the `(i,j)` factorization) of the
`(i,j)` k-th image piece is the basic open of `Spec transRing` where the transported piece
coordinate is invertible. -/
lemma transι_preimage_blOpenYImage_piece (k : Fin 3) :
    transι W i j i' j' ⁻¹ᵁ (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) =
      specBasicOpen (CommRingCat.of (transRing W i j i' j'))
        (transAlgHom W i j i' j' (lawTwoTriple W i j k)) := by
  show (Spec.map (CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom) ≫
    (chartPieceIso W i j).inv ≫ pieceι W i j) ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq,
    blOpenYPieceFamily,
    ← Scheme.Hom.comp_preimage (chartPieceIso W i j).inv (chartPieceIso W i j).hom,
    Iso.inv_hom_id, Scheme.Hom.id_preimage]
  exact SpecMap_preimage_basicOpen _ _

/-- **([C4-HF-ASSEMBLY] L2b)** Via the `(i',j')` factorization (`transι_eq`), the preimage of the
`(i',j')` k'-th image piece is the basic open where `transHom(lawTwoTriple i'j' k')` is invertible. -/
lemma transι_preimage_blOpenYImage_piece' (k' : Fin 3) :
    transι W i j i' j' ⁻¹ᵁ (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k') =
      specBasicOpen (CommRingCat.of (transRing W i j i' j'))
        (transHom W i j i' j' (lawTwoTriple W i' j' k')) := by
  rw [transι_eq]
  show (Spec.map (CommRingCat.ofHom (transHom W i j i' j').toRingHom) ≫
    (chartPieceIso W i' j').inv ≫ pieceι W i' j') ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq,
    blOpenYPieceFamily,
    ← Scheme.Hom.comp_preimage (chartPieceIso W i' j').inv (chartPieceIso W i' j').hom,
    Iso.inv_hom_id, Scheme.Hom.id_preimage]
  exact SpecMap_preimage_basicOpen _ _

/-- **([C4-HF-ASSEMBLY] L2c)** The preimage under `transι` of the overlap piece `A_k ⊓ B_k'` is the
single basic open of `Spec transRing` at the product of the two transported piece coordinates — the
affine identification of the overlap piece with the triple-localization locus. -/
lemma transι_preimage_piece_inf (k k' : Fin 3) :
    transι W i j i' j' ⁻¹ᵁ ((pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) ⊓
        (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k')) =
      specBasicOpen (CommRingCat.of (transRing W i j i' j'))
        (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')) := by
  rw [Scheme.Hom.preimage_inf, transι_preimage_blOpenYImage_piece,
    transι_preimage_blOpenYImage_piece', specBasicOpen_mul]

/-- **([C4-HF-ASSEMBLY] L3)** The affine immersion of the k-th image piece:
`Spec(Away(lawTwoTriple ij k)) → E ×_R E`. -/
noncomputable def pieceAwayι (k : Fin 3) :
    Spec (CommRingCat.of (Localization.Away (lawTwoTriple W i j k))) ⟶
      pullback (projModelπ W) (projModelπ W) :=
  (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).hom ≫
    (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).ι ≫
    (chartPieceIso W i j).inv ≫ pieceι W i j

/-- **([C4-HF-ASSEMBLY] L3, the σ-immersion identity)** The `isoImage/morphismRestrict/
specBasicOpenIsoAway.inv` chain out of `A_k` (the `σ` of L1), followed by `pieceAwayι`, is exactly
`A_k.ι`. So `σ` is the section identifying `A_k` with `Spec(Away(lawTwoTriple ij k))`, and
`pieceAwayι` its immersion into `E ×_R E`. Instantiates the variable-scheme
`isoImage_inv_morphismRestrict_ι`. -/
lemma isoImage_specBasicOpen_pieceAwayι (k : Fin 3) :
    ((Scheme.Hom.isoImage (pieceι W i j) (blOpenYPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
        (lawTwoTriple W i j k)).inv) ≫ pieceAwayι W i j k =
      (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k).ι := by
  rw [pieceAwayι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact isoImage_inv_morphismRestrict_ι (pieceι W i j) (chartPieceIso W i j)
    (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k))

/-- **([C4-HF-ASSEMBLY] L3b1)** `pieceAwayι` in `Spec.map` form: the localization map into
`Away(lawTwoTriple ij k)` followed by the chart-product identification and the piece immersion — the
same shape as `transι`, localizing at a single piece coordinate instead of the transition product. -/
lemma pieceAwayι_eq (k : Fin 3) :
    pieceAwayι W i j k =
      Spec.map (CommRingCat.ofHom (algebraMap (biChartRing W i j)
        (Localization.Away (lawTwoTriple W i j k)))) ≫
        (chartPieceIso W i j).inv ≫ pieceι W i j := by
  rw [pieceAwayι, ← Category.assoc, specBasicOpenIsoAway_hom_ι]

/-- The overlap piece `P := A_k ⊓ B_k'` of two law-2 regularity image pieces. -/
noncomputable abbrev overlapPiece (k k' : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) ⊓
    (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k')

/-- **([C4-HF-ASSEMBLY] L3, the affine identification)** `Spec(Away transRing g) ≅ P`, where
`g = transAlgHom(lawTwoTriple ij k) · transHom(lawTwoTriple i'j' k')`. Built from `specBasicOpenIsoAway`,
the preimage computation `transι_preimage_piece_inf` (L2c), and `transι.isoImage` (P ≤ range transι
by helper A). This is `w`: it makes the overlap piece an affine `Spec`, where every morphism out of it
is `Spec.map`. -/
noncomputable def overlapPieceIso (k k' : Fin 3) :
    Spec (CommRingCat.of (Localization.Away
        (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))) ≅
      (overlapPiece W i j i' j' k k').toScheme :=
  specBasicOpenIsoAway (CommRingCat.of (transRing W i j i' j'))
      (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k')) ≪≫
    ((Spec (CommRingCat.of (transRing W i j i' j'))).isoOfEq
      (transι_preimage_piece_inf W i j i' j' k k').symm) ≪≫
    Scheme.Hom.isoImage (transι W i j i' j') (transι W i j i' j' ⁻¹ᵁ overlapPiece W i j i' j' k k') ≪≫
    (pullback (projModelπ W) (projModelπ W)).isoOfEq (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
      exact (inf_le_inf ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k))
        ((pieceι W i' j').image_mono (le_iSup (blOpenYPieceFamily W i' j') k'))).trans
        (blOpenYImage_inf_le_transι W i j i' j'))

/-- **([C4-HF-ASSEMBLY] L3, w-transι identity)** The affine identification, composed with the piece
inclusion into `E ×_R E`, is `Spec` of the localization `transRing → S` followed by `transι`. -/
lemma overlapPieceIso_hom_ι (k k' : Fin 3) :
    (overlapPieceIso W i j i' j' k k').hom ≫ (overlapPiece W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [overlapPieceIso]
  simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc,
    Scheme.Hom.isoImage_hom_ι]
  rw [← Category.assoc, specBasicOpenIsoAway_hom_ι]

lemma isUnit_algebraMap_biChartRing_lawTwoTriple (k k' : Fin 3) :
    IsUnit ((algebraMap (biChartRing W i j)
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))
      (lawTwoTriple W i j k)) := by
  rw [IsScalarTower.algebraMap_apply (biChartRing W i j) (transRing W i j i' j')
    (Localization.Away _)]
  exact IsLocalization.Away.isUnit_of_dvd
    (transAlgHom W i j i' j' (lawTwoTriple W i j k) * transHom W i j i' j' (lawTwoTriple W i' j' k'))
    ⟨transHom W i j i' j' (lawTwoTriple W i' j' k'), rfl⟩

/-- **([C4-HF-ASSEMBLY] L3, ψ_ij)** The localization lift `Away(lawTwoTriple ij k) →ₐ[R] S` into the
triple-localization, agreeing with the tower map `biChartRing → S` on the base. -/
noncomputable def psiFst (k k' : Fin 3) :
    Localization.Away (lawTwoTriple W i j k) →ₐ[R]
      Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k')) :=
  IsLocalization.Away.liftAlgHom (IsScalarTower.toAlgHom R (biChartRing W i j) _)
    (lawTwoTriple W i j k) (isUnit_algebraMap_biChartRing_lawTwoTriple W i j i' j' k k')

@[simp]
lemma psiFst_algebraMap (k k' : Fin 3) (x : biChartRing W i j) :
    psiFst W i j i' j' k k' (algebraMap (biChartRing W i j) _ x) =
      algebraMap (biChartRing W i j) _ x :=
  IsLocalization.Away.lift_eq (lawTwoTriple W i j k)
    (isUnit_algebraMap_biChartRing_lawTwoTriple W i j i' j' k k') x

end Overlap

end WeierstrassCurve.Projective
