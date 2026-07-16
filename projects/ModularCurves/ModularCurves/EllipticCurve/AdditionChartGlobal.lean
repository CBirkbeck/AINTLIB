/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
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
`blOpenYPiece`: the two are equal (`iSup_blOpenYPieceFamily`), but `addOnYOnSup` already lives on
the
former, and a `▸` transport across that equality would be gratuitous.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

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

/-- **(T-W7.0c·c1-Y, the open)** The regularity open of the second Bosma–Lenstra law on `E ×_R E`.
-/
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

/-- **(c3, the two-law overlap image is same-index)** On a single chart-product `(i,j)`, the overlap
of
the two laws' regularity images is covered by the SAME-index pieces `pieceι ''ᵁ D(lawTwo_k ·
lawOne_k)`.
The image (`Scheme.Hom.image_inf` on `pieceι`) of the piece-level
`blOpenYPiece_inf_blOpenZPiece_eq_iSup`.
This is the geometry the same-chart `addOn_agree` reduces over. -/
lemma blOpenZImage_inf_blOpenYImage_eq_iSup (i j : Fin 3) :
    blOpenZImage W i j ⊓ blOpenYImage W i j =
      ⨆ k, pieceι W i j ''ᵁ ((chartPieceIso W i j).hom ⁻¹ᵁ
        specBasicOpen (CommRingCat.of (biChartRing W i j))
          (lawTwoTriple W i j k * lawOneTriple W i j k)) := by
  rw [blOpenZImage, blOpenYImage, iSup_blOpenZPieceFamily, iSup_blOpenYPieceFamily,
    ← Scheme.Hom.image_inf, inf_comm (blOpenZPiece W i j),
    blOpenYPiece_inf_blOpenZPiece_eq_iSup, Scheme.Hom.image_iSup]

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
/-- **(bridge, law 2)** On the `k`-th image piece, `addOnYOnImage` is `addOnYOnFamily k` read
through
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
set_option backward.isDefEq.respectTransparency.types false in
/-- **([C4-HF-ASSEMBLY] L1)** On any open `P` inside the k-th image piece,
`homOfLE ≫ addOnYOnImage ij` factors as `σ ≫ addOnYPieceMor ij k`, where the prefactor `σ` is the
`isoImage / morphismRestrict / specBasicOpenIsoAway.inv` chain landing in `Spec(Away(lawTwoTriple ij
k))`.
This is the entry point that turns the image-level morphism into the `pieceMorOfTriple` form the
crux
consumes. Uses only `addOnYOnImage_piece`'s own `isoImage`, so there is no second-copy cancellation.
-/
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
set_option backward.isDefEq.respectTransparency.types false in
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

/-- `Spec` of the localization map into the overlap ring IS the basic-open immersion `D(τ) ↪ Spec
B`,
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

/-- `pullback.fst`/`.snd` cut `range(pieceι)` into the two chart ranges
(`PullbackCarrier.range_map`). -/
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
already proven) composed with `awayTensorEquiv_symm_tmul_one` +
`biChartRingTensorEquiv_mk_rename_inl`. -/
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

/-- **(helper A, final leaf — snd)** The right tensor inclusion carries `isLocalizationElem X_j
X_{j'}`
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
`range(transι)` — the containment `IsOpenImmersion.lift` needs to factor `hf` through the
transition. -/
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
`(i',j')` k'-th image piece is the basic open where `transHom(lawTwoTriple i'j' k')` is invertible.
-/
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

set_option backward.isDefEq.respectTransparency.types false in
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
same shape as `transι`, localizing at a single piece coordinate instead of the transition product.
-/
lemma pieceAwayι_eq (k : Fin 3) :
    pieceAwayι W i j k =
      Spec.map (CommRingCat.ofHom (algebraMap (biChartRing W i j)
        (Localization.Away (lawTwoTriple W i j k)))) ≫
        (chartPieceIso W i j).inv ≫ pieceι W i j := by
  rw [pieceAwayι, ← Category.assoc, specBasicOpenIsoAway_hom_ι]

/-- **(π-compat, piece foundation)** The `k`-th law-2 regularity piece embeds into `E ×_R E` as an
`R`-scheme: `pieceAwayι ≫ fst ≫ projModelπ = Spec.map (algebraMap R (Away …))`. The left projection
(`pieceι_fst`, `chartPieceIso_inv_fst`, `chartι_projModelπ`) collapses to the piece's `R`-algebra
structure; the ring identity is `includeLeftRingHom_comp_algebraMap` + `AlgEquiv.commutes` (the
chart-product tensor equiv is `R`-linear) + the `R`-`biChartRing`-`Away` scalar tower. This matches
`addOnYPieceMor_projModelπ`, so it is the base case of the `mulModelHom_π` propagation. -/
lemma pieceAwayι_fst_projModelπ (k : Fin 3) :
    pieceAwayι W i j k ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (lawTwoTriple W i j k)))) := by
  rw [pieceAwayι_eq]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [pieceι_fst]
  slice_lhs 4 5 => rw [chartι_projModelπ]
  slice_lhs 2 3 => rw [chartPieceIso_inv_fst]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  show (algebraMap (biChartRing W i j) (Localization.Away (lawTwoTriple W i j k)))
      ((biChartRingAwayTensorEquiv W i j).symm
        (algebraMap R (TensorProduct R (chartAway W i) (chartAway W j)) r)) =
    algebraMap R (Localization.Away (lawTwoTriple W i j k)) r
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

/-- The overlap piece `P := A_k ⊓ B_k'` of two law-2 regularity image pieces. -/
noncomputable abbrev overlapPiece (k k' : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) ⊓
    (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k')

/-- **([C4-HF-ASSEMBLY] L3, the affine identification)** `Spec(Away transRing g) ≅ P`, where
`g = transAlgHom(lawTwoTriple ij k) · transHom(lawTwoTriple i'j' k')`. Built from
`specBasicOpenIsoAway`,
the preimage computation `transι_preimage_piece_inf` (L2c), and `transι.isoImage` (P ≤ range transι
by helper A). This is `w`: it makes the overlap piece an affine `Spec`, where every morphism out of
it
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
    Scheme.Hom.isoImage (transι W i j i' j')
      (transι W i j i' j' ⁻¹ᵁ overlapPiece W i j i' j' k k') ≪≫
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
    (transAlgHom W i j i' j' (lawTwoTriple W i j k) * transHom W i j i' j'
      (lawTwoTriple W i' j' k'))
    ⟨transHom W i j i' j' (lawTwoTriple W i' j' k'), rfl⟩

/-- **([C4-HF-ASSEMBLY] L3, ψ_ij)** The localization lift `Away(lawTwoTriple ij k) →ₐ[R] S` into the
triple-localization, agreeing with the tower map `biChartRing → S` on the base. -/
noncomputable def psiFst (k k' : Fin 3) :
    Localization.Away (lawTwoTriple W i j k) →ₐ[R]
      Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k')) :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R (biChartRing W i j) _)
    (lawTwoTriple W i j k) (isUnit_algebraMap_biChartRing_lawTwoTriple W i j i' j' k k')

@[simp]
lemma psiFst_algebraMap (k k' : Fin 3) (x : biChartRing W i j) :
    psiFst W i j i' j' k k' (algebraMap (biChartRing W i j) _ x) =
      algebraMap (biChartRing W i j) _ x :=
  IsLocalization.Away.lift_eq (lawTwoTriple W i j k)
    (isUnit_algebraMap_biChartRing_lawTwoTriple W i j i' j' k k') x

/-- **([C4-HF-ASSEMBLY] L3, ψ_ij ring identity)** ψ_ij restricted to `biChartRing` is the tower map
`biChartRing → S` — a whnf-safe `RingHom.ext` (the RHS is `algebraMap biChartRing S`, no
composition,
so it never forces the concrete triple-localization). -/
lemma psiFst_toRingHom_comp (k k' : Fin 3) :
    (psiFst W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i j) (Localization.Away (lawTwoTriple W i j k))) =
      algebraMap (biChartRing W i j)
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))) :=
  RingHom.ext (psiFst_algebraMap W i j i' j' k k')

/-- **([C4-HF-ASSEMBLY] L3, ψ_ij tower factorization)** ψ_ij restricted to `biChartRing`, routed
through the *middle* ring `transRing` — `= (algebraMap transRing S).comp transAlgHom`, the tower
map read as "localize `transRing`, then pull back along `transAlgHom`". The middle term of the
`.trans` is `algebraMap biChartRing S`, syntactically shared by both halves so `Eq.trans` closes
it without ever unfolding the concrete triple-localization (contrast: `rw
[algebraMap_biChartRing_eq]`
on a goal already carrying `algebraMap biChartRing S` explodes `isDefEq`). This is the form the
`Spec.map` identification consumes, keeping `algebraMap biChartRing S` out of the scheme goal. -/
lemma psiFst_toRingHom_comp' (k k' : Fin 3) :
    (psiFst W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i j) (Localization.Away (lawTwoTriple W i j k))) =
      (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))).comp
        (transAlgHom W i j i' j').toRingHom :=
  (psiFst_toRingHom_comp W i j i' j' k k').trans
    (algebraMap_biChartRing_eq W i j i' j' _)

/-- **([C4-HF-ASSEMBLY] L3, the ψ_ij–σ identification)** `Spec(ψ_ij) ≫ pieceAwayι =
Spec(transRing→S) ≫
transι`: the piece immersion `σ = pieceAwayι` precomposed with `Spec(ψ_ij)` is the
triple-localization
immersion `transι` precomposed with `Spec` of the localization `transRing → S`. Both sides reduce,
via the definitions of `pieceAwayι`/`transι` and functoriality of `Spec`, to
`Spec(ofHom ((algebraMap transRing S).comp transAlgHom)) ≫ (chartPieceIso).inv ≫ pieceι`; the shared
tail and the base identity `psiFst_toRingHom_comp'` are packaged by `spec_map_comp_congr` (the
variable-ring barrier), which keeps `isDefEq` off the concrete tower — under 5k heartbeats. -/
lemma specMap_psiFst_pieceAwayι (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiFst W i j i' j' k k').toRingHom) ≫ pieceAwayι W i j k =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [pieceAwayι_eq, transι]
  exact spec_map_comp_congr _ _ _ _ _
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, psiFst_toRingHom_comp'])

/-- **([C4-HF-ASSEMBLY] L3, w ≫ ι = Spec(ψ_ij) ≫ σ)** The two affine factorizations of the overlap
immersion agree: the affine identification `w = overlapPieceIso` (`P ≅ Spec S`) into `E ×_R E`
equals
`Spec(ψ_ij)` followed by the k-th piece immersion `σ = pieceAwayι`. Both routes share the value
`Spec(transRing → S) ≫ transι` — `w` by `overlapPieceIso_hom_ι`, the ψ_ij route by
`specMap_psiFst_pieceAwayι` — so this is their transitive glue. This is the identity L4/L5
precompose
against `w.hom` and cancel (`w` an iso). -/
lemma overlapPieceIso_hom_ι_eq_specMap_psiFst (k k' : Fin 3) :
    (overlapPieceIso W i j i' j' k k').hom ≫ (overlapPiece W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (psiFst W i j i' j' k k').toRingHom) ≫ pieceAwayι W i j k :=
  (overlapPieceIso_hom_ι W i j i' j' k k').trans
    (specMap_psiFst_pieceAwayι W i j i' j' k k').symm

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j' unit)** The second transition coordinate `transHom(lawTwoTriple
i'j' k')` maps to a unit in `S`: it is the second factor of the localization generator, hence
divides
it. The `(i',j')`-side analogue of `isUnit_algebraMap_biChartRing_lawTwoTriple`, but stated directly
over `transRing` (no `biChartRing → transRing` rewrite — the map is `transHom`, not the canonical
tower map). -/
lemma isUnit_algebraMap_transRing_transHom_lawTwoTriple (k k' : Fin 3) :
    IsUnit (((IsScalarTower.toAlgHom R (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))).comp
        (transHom W i j i' j')) (lawTwoTriple W i' j' k')) := by
  rw [AlgHom.comp_apply]
  exact IsLocalization.Away.isUnit_of_dvd
    (transAlgHom W i j i' j' (lawTwoTriple W i j k) * transHom W i j i' j'
      (lawTwoTriple W i' j' k'))
    ⟨transAlgHom W i j i' j' (lawTwoTriple W i j k), mul_comm _ _⟩

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j')** The `(i',j')`-side localization lift `Away(lawTwoTriple i'j'
k')
→ₐ[R] S`. Unlike `ψ_ij = psiFst`, its base map is built *explicitly* through the middle ring —
`(algebraMap transRing S).comp transHom` — since `transHom` (not the canonical scalar tower) carries
`biChartRing(i'j')` into `transRing`. Consequently its base identity `psiSnd_toRingHom_comp'` is
direct
(no `.trans` bridge, no composite `algebraMap biChartRing(i'j') S` instance). -/
noncomputable def psiSnd (k k' : Fin 3) :
    Localization.Away (lawTwoTriple W i' j' k') →ₐ[R]
      Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k')) :=
  IsLocalization.Away.liftAlgHom
    (f := (IsScalarTower.toAlgHom R (transRing W i j i' j') _).comp (transHom W i j i' j'))
    (lawTwoTriple W i' j' k') (isUnit_algebraMap_transRing_transHom_lawTwoTriple W i j i' j' k k')

@[simp]
lemma psiSnd_algebraMap (k k' : Fin 3) (x : biChartRing W i' j') :
    psiSnd W i j i' j' k k' (algebraMap (biChartRing W i' j') _ x) =
      algebraMap (transRing W i j i' j') _ (transHom W i j i' j' x) := by
  rw [psiSnd, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (lawTwoTriple W i' j' k')
      (isUnit_algebraMap_transRing_transHom_lawTwoTriple W i j i' j' k k') x]
  rfl

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j' tower factorization)** ψ_i'j' restricted to `biChartRing(i'j')`
is
`(algebraMap transRing S).comp transHom` — direct from `liftAlgHom_algebraMap` (the base map already
IS
this composite), no whnf hazard. -/
lemma psiSnd_toRingHom_comp' (k k' : Fin 3) :
    (psiSnd W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i' j') (Localization.Away (lawTwoTriple W i' j' k'))) =
      (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))).comp
        (transHom W i j i' j').toRingHom :=
  RingHom.ext (psiSnd_algebraMap W i j i' j' k k')

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j'–σ identification)** `Spec(ψ_i'j') ≫ pieceAwayι(i'j'k') =
Spec(transRing→S) ≫ transι`: the `(i',j')`-piece immersion precomposed with `Spec(ψ_i'j')` is the
triple-localization immersion, reading `transι` through the `(i',j')` chart-product (`transι_eq`,
the
`transHom` form). The psiSnd mirror of `specMap_psiFst_pieceAwayι`, again packaged by the
variable-ring
barrier `spec_map_comp_congr` so `isDefEq` never touches the concrete tower. -/
lemma specMap_psiSnd_pieceAwayι (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiSnd W i j i' j' k k').toRingHom) ≫ pieceAwayι W i' j' k' =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [pieceAwayι_eq, transι_eq]
  exact spec_map_comp_congr _ _ _ _ _
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, psiSnd_toRingHom_comp'])

/-- **([C4-HF-ASSEMBLY] L3, w.hom ≫ ι = Spec(ψ_i'j') ≫ σ')** The `(i',j')`-side reading of the
overlap
immersion: `w` into `E ×_R E` equals `Spec(ψ_i'j')` followed by the `(i',j')`-piece immersion. The
psiSnd mirror of `overlapPieceIso_hom_ι_eq_specMap_psiFst`, sharing the same value
`Spec(transRing → S) ≫ transι`. Together the two give the cross-chart glue. -/
lemma overlapPieceIso_hom_ι_eq_specMap_psiSnd (k k' : Fin 3) :
    (overlapPieceIso W i j i' j' k k').hom ≫ (overlapPiece W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (psiSnd W i j i' j' k k').toRingHom) ≫ pieceAwayι W i' j' k' :=
  (overlapPieceIso_hom_ι W i j i' j' k k').trans
    (specMap_psiSnd_pieceAwayι W i j i' j' k k').symm

/-- An on-curve triple pushed along any `R`-algebra map stays on the curve — the `AlgHom`
generalisation of `equation_mapTriple` (which is the `algebraMap` special case). Used to carry the
law-2 triple into `transRing` along `transHom` (which is *not* the canonical scalar-tower map, so
`equation_mapTriple` doesn't directly apply). -/
lemma equation_mapTriple_algHom {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (t : Fin 3 → A) (ht : (W.map (algebraMap R A)).toProjective.Equation t) :
    (W.map (algebraMap R B)).toProjective.Equation (fun m => f (t m)) := by
  have h := ht.map f.toRingHom
  have hmap : (W.map (algebraMap R A)).map f.toRingHom = W.map (algebraMap R B) := by
    rw [WeierstrassCurve.map_map]; exact congrArg W.map f.comp_algebraMap
  exact hmap ▸ h

/-- **([C4-HF-ASSEMBLY] L4, ψ_ij pushed triple)** ψ_ij carries the `(i,j)` law-2 triple to
`algebraMap transRing S ∘ (transAlgHom ∘ lawTwoTriple ij)` — the `(i,j)` reading of the addition
triple over `S`. Element-level tower step (`algebraMap_biChartRing_eq` via `congrFun`, term-mode so
it
never whnf-explodes), keeping the composite `algebraMap biChartRing S` out of the goal. -/
lemma psiFst_algebraMap_lawTwoTriple (k k' m : Fin 3) :
    psiFst W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawTwoTriple W i j k)) (lawTwoTriple W i j m)) =
      algebraMap (transRing W i j i' j') _ (transAlgHom W i j i' j' (lawTwoTriple W i j m)) := by
  rw [psiFst_algebraMap]
  exact congrFun (congrArg DFunLike.coe (algebraMap_biChartRing_eq W i j i' j' _))
    (lawTwoTriple W i j m)

/-- The `k`-th coordinate of the ψ_ij-pushed triple is invertible with the pushed `invSelf`. -/
lemma psiFst_algebraMap_mul_invSelf (k k' : Fin 3) :
    psiFst W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawTwoTriple W i j k)) (lawTwoTriple W i j k)) *
      psiFst W i j i' j' k k' (IsLocalization.Away.invSelf (lawTwoTriple W i j k)) = 1 := by
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- The `k'`-th coordinate of the ψ_i'j'-pushed triple is invertible with the pushed `invSelf`. -/
lemma psiSnd_algebraMap_mul_invSelf (k k' : Fin 3) :
    psiSnd W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' k')) *
      psiSnd W i j i' j' k k' (IsLocalization.Away.invSelf (lawTwoTriple W i' j' k')) = 1 := by
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- **([C4-HF-ASSEMBLY] L4, proportionality over S)** The two pushed triples are proportional: the
ψ_i'j' triple is `(cd)²`-times the ψ_ij triple over `S`, the bidegree-`(2,2)` transition factor
pushed
from `transRing` (`transHom_lawTwoTriple_eq_smul`). Term-mode `.trans` chain (all middles are
`algebraMap transRing S …`, never the composite), so it stays off the concrete tower. This is the
crux's
`hsmul` hypothesis. -/
lemma psiSnd_algebraMap_lawTwoTriple_eq_smul (k k' m : Fin 3) :
    psiSnd W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' m)) =
      algebraMap (transRing W i j i' j') _
        ((transInvFst W i j i' j' * transInvSnd W i j i' j') ^ 2) *
      psiFst W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawTwoTriple W i j k)) (lawTwoTriple W i j m)) :=
  (psiSnd_algebraMap W i j i' j' k k' (lawTwoTriple W i' j' m)).trans
    ((congrArg (algebraMap (transRing W i j i' j') _)
        (transHom_lawTwoTriple_eq_smul W i j i' j' m)).trans
      ((map_mul _ _ _).trans
        (congrArg (algebraMap (transRing W i j i' j') _
            ((transInvFst W i j i' j' * transInvSnd W i j i' j') ^ 2) * ·)
          (psiFst_algebraMap_lawTwoTriple W i j i' j' k k' m).symm)))

variable [IsJacobsonRing R]

/-- **([C4-HF-ASSEMBLY] L4, ψ_ij triple on-curve)** The ψ_ij-pushed law-2 triple satisfies the model
equation over `S`. Routed through `transRing` (via `transAlgHom`, the canonical tower map — cheap
`[Algebra transRing S]`), never the composite `[Algebra biChartRing S]`. -/
lemma equation_psiFst_lawTwoTriple [IsDomain (biChartRing W i j)] (hΔ : IsUnit W.Δ) (k k' : Fin 3) :
    (W.map (algebraMap R (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k'))))).toProjective.Equation
        (fun m => psiFst W i j i' j' k k' (algebraMap (biChartRing W i j)
          (Localization.Away (lawTwoTriple W i j k)) (lawTwoTriple W i j m))) := by
  rw [funext (psiFst_algebraMap_lawTwoTriple W i j i' j' k k')]
  exact equation_mapTriple W (fun m => transAlgHom W i j i' j' (lawTwoTriple W i j m))
    (equation_mapTriple_algHom W (transAlgHom W i j i' j') (lawTwoTriple W i j)
      (equation_lawTwoTriple_of_isDomain W i j hΔ))

/-- **([C4-HF-ASSEMBLY] L4, ψ_i'j' triple on-curve)** The ψ_i'j'-pushed law-2 triple satisfies the
model equation over `S`, routed through `transRing` via `transHom` (`equation_mapTriple_algHom`). -/
lemma equation_psiSnd_lawTwoTriple [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ)
  (k k' : Fin 3) :
    (W.map (algebraMap R (Localization.Away (transAlgHom W i j i' j' (lawTwoTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k'))))).toProjective.Equation
        (fun m => psiSnd W i j i' j' k k' (algebraMap (biChartRing W i' j')
          (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' m))) := by
  rw [funext (fun m => psiSnd_algebraMap W i j i' j' k k' (lawTwoTriple W i' j' m))]
  exact equation_mapTriple W (fun m => transHom W i j i' j' (lawTwoTriple W i' j' m))
    (equation_mapTriple_algHom W (transHom W i j i' j') (lawTwoTriple W i' j')
      (equation_lawTwoTriple_of_isDomain W i' j' hΔ))

/-- **([C4-HF-ASSEMBLY] L4, THE cross-chart ψ-agreement)** Over `Spec S`, the `(i,j,k)` and
`(i',j',k')` law-2 piece morphisms agree after pulling back along `Spec(ψ_ij)`, `Spec(ψ_i'j')`. Both
sides go to `chartAwayHomOfTriple`-form via `specMap_comp_pieceMorOfTriple`, and the general crux
`chartι_comp_specMap_chartAwayHom_smul_eq` closes them using the proportionality of the two pushed
triples. Term-mode `.trans` chain with syntactically-shared `chartAwayHomOfTriple` middles — the
decomposition into clean-context sub-lemmas is what keeps `isDefEq` off the concrete tower. -/
lemma specMap_psiFst_addOnYPieceMor_cross [IsDomain (biChartRing W i j)]
    [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ) (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiFst W i j i' j' k k').toRingHom) ≫ addOnYPieceMor W i j k hΔ =
      Spec.map (CommRingCat.ofHom (psiSnd W i j i' j' k k').toRingHom) ≫
        addOnYPieceMor W i' j' k' hΔ := by
  rw [addOnYPieceMor_eq, addOnYPieceMor_eq]
  exact (specMap_comp_pieceMorOfTriple W (lawTwoTriple W i j)
      (equation_lawTwoTriple_of_isDomain W i j hΔ) k (psiFst W i j i' j' k k')
      (psiFst_algebraMap_mul_invSelf W i j i' j' k k')
      (equation_psiFst_lawTwoTriple W i j i' j' hΔ k k')).trans
    (((chartι_comp_specMap_chartAwayHom_smul_eq W k k' _ _ _ _ _
        (psiSnd_algebraMap_lawTwoTriple_eq_smul W i j i' j' k k')
        (psiFst_algebraMap_mul_invSelf W i j i' j' k k')
        (psiSnd_algebraMap_mul_invSelf W i j i' j' k k')
        (equation_psiFst_lawTwoTriple W i j i' j' hΔ k k')
        (equation_psiSnd_lawTwoTriple W i j i' j' hΔ k k')).symm).trans
      (specMap_comp_pieceMorOfTriple W (lawTwoTriple W i' j')
        (equation_lawTwoTriple_of_isDomain W i' j' hΔ) k' (psiSnd W i j i' j' k k')
        (psiSnd_algebraMap_mul_invSelf W i j i' j' k k')
        (equation_psiSnd_lawTwoTriple W i j i' j' hΔ k k')).symm)

/-- The `k`-th piece immersion `pieceAwayι` is an open immersion (hence mono): a composite of the
`specBasicOpenIsoAway` iso, the basic-open immersion, the chart-product iso, and `pieceι`. -/
instance instIsOpenImmersionPieceAwayι (k : Fin 3) : IsOpenImmersion (pieceAwayι W i j k) := by
  rw [pieceAwayι]; infer_instance

omit [IsJacobsonRing R] in
set_option backward.isDefEq.respectTransparency.types false in
/-- **([C4-HF-ASSEMBLY] L5, σ-cancel, (i,j) side)** `w.hom` followed by the `(i,j)` L1 prefactor `σ`
(the `homOfLE / isoImage.inv / morphismRestrict / specBasicOpenIsoAway.inv` chain landing in
`Spec(Away(lawTwoTriple ij k))`) equals `Spec(ψ_ij)`. Cancelled against the `pieceAwayι` mono: both
composed with `pieceAwayι` give `w.hom ≫ overlapPiece.ι` (via the σ-immersion identity
`isoImage_specBasicOpen_pieceAwayι` and `Scheme.homOfLE_ι`), which is `Spec(ψ_ij) ≫ pieceAwayι` by
L3.
This turns L1's image-level prefactor into `Spec(ψ_ij)` once precomposed with `w`. -/
@[reassoc]
lemma w_homOfLE_sigma_psiFst (k k' : Fin 3) :
    (overlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left : overlapPiece W i j i' j' k k' ≤
          pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) ≫
      (Scheme.Hom.isoImage (pieceι W i j) (blOpenYPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).inv =
    Spec.map (CommRingCat.ofHom (psiFst W i j i' j' k k').toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i j) (blOpenYPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).inv ≫
      pieceAwayι W i j k = (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k).ι := by
    rw [← isoImage_specBasicOpen_pieceAwayι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceAwayι W i j k)]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact overlapPieceIso_hom_ι_eq_specMap_psiFst W i j i' j' k k'

omit [IsJacobsonRing R] in
set_option backward.isDefEq.respectTransparency.types false in
/-- **([C4-HF-ASSEMBLY] L5, σ-cancel, (i',j') side)** The psiSnd mirror of `w_homOfLE_sigma_psiFst`.
-/
@[reassoc]
lemma w_homOfLE_sigma_psiSnd (k k' : Fin 3) :
    (overlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right : overlapPiece W i j i' j' k k' ≤
          pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k') ≫
      (Scheme.Hom.isoImage (pieceι W i' j') (blOpenYPieceFamily W i' j' k')).inv ≫
      morphismRestrict (chartPieceIso W i' j').hom
        (specBasicOpen (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')).inv =
    Spec.map (CommRingCat.ofHom (psiSnd W i j i' j' k k').toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i' j') (blOpenYPieceFamily W i' j' k')).inv ≫
      morphismRestrict (chartPieceIso W i' j').hom
        (specBasicOpen (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')).inv ≫
      pieceAwayι W i' j' k' = (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k').ι := by
    rw [← isoImage_specBasicOpen_pieceAwayι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceAwayι W i' j' k')]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact overlapPieceIso_hom_ι_eq_specMap_psiSnd W i j i' j' k k'

/-- **([C4-HF-ASSEMBLY] L5, per-overlap chart agreement)** On the overlap piece `A_k ⊓ B_k'`, the
`(i,j)` and `(i',j')` image-level law-2 morphisms agree. Proved by precomposing with the affine
identification `w` (an iso, cancelled via `cancel_epi`): L1 turns each side into `σ ≫
addOnYPieceMor`,
the σ-cancels turn `w.hom ≫ σ` into `Spec(ψ)`, and L4 identifies the two `Spec(ψ) ≫ addOnYPieceMor`.
Fully term-mode (`congrArg`/`.trans`) so no `rw` motive ever touches the concrete tower `S`. -/
lemma overlapPiece_addOnYOnImage_agree [IsDomain (biChartRing W i j)]
    [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ) (k k' : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left.trans ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k))) ≫
        addOnYOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right.trans ((pieceι W i' j').image_mono (le_iSup
          (blOpenYPieceFamily W i' j') k'))) ≫
        addOnYOnImage W hΔ i' j' := by
  have eL : (overlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left.trans ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k))) ≫
        addOnYOnImage W hΔ i j =
      Spec.map (CommRingCat.ofHom
        (psiFst W i j i' j' k k').toRingHom) ≫ addOnYPieceMor W i j k hΔ :=
    (congrArg ((overlapPieceIso W i j i' j' k k').hom ≫ ·)
        (homOfLE_addOnYOnImage_eq W i j hΔ k (overlapPiece W i j i' j' k k') inf_le_left)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnYPieceMor W i j k hΔ) (w_homOfLE_sigma_psiFst W i j i' j' k k')))
  have eR : (overlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right.trans ((pieceι W i' j').image_mono (le_iSup
          (blOpenYPieceFamily W i' j') k'))) ≫
        addOnYOnImage W hΔ i' j' =
      Spec.map (CommRingCat.ofHom
        (psiSnd W i j i' j' k k').toRingHom) ≫ addOnYPieceMor W i' j' k' hΔ :=
    (congrArg ((overlapPieceIso W i j i' j' k k').hom ≫ ·)
        (homOfLE_addOnYOnImage_eq W i' j' hΔ k' (overlapPiece W i j i' j' k k') inf_le_right)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnYPieceMor W i' j' k' hΔ) (w_homOfLE_sigma_psiSnd W i j i' j' k k')))
  exact (cancel_epi (overlapPieceIso W i j i' j' k k').hom).mp
    (eL.trans ((specMap_psiFst_addOnYPieceMor_cross W i j i' j' hΔ k k').trans eR.symm))

/-- **([C4-HF-ASSEMBLY] L5, full cross-chart agreement)** The `(i,j)` and `(i',j')` image-level
law-2
morphisms agree on their entire overlap `blOpenYImage(i,j) ⊓ blOpenYImage(i',j')`. The overlap is
covered by the `(k,k')` overlap pieces (`blOpenYImage_inf_eq_iSup`), so `Scheme.Cover.hom_ext`
reduces
to the per-piece agreement `overlapPiece_addOnYOnImage_agree`; the two nested `homOfLE`s of the
cover
inclusion and the overlap inclusion collapse via `Scheme.homOfLE_homOfLE_assoc`. Stated with the
overlap `Ω` as a parameter (`subst`) so the cover lands on it directly, no dependent rewriting. -/
lemma addOnYOnImage_agree [IsDomain (biChartRing W i j)] [IsDomain (biChartRing W i' j')]
    (hΔ : IsUnit W.Δ) (Ω : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hk : Ω ≤ blOpenYImage W i j) (hl : Ω ≤ blOpenYImage W i' j')
    (hΩ : Ω = ⨆ p : Fin 3 × Fin 3, overlapPiece W i j i' j' p.1 p.2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnYOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE hl ≫ addOnYOnImage W hΔ i' j' := by
  subst hΩ
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun p : Fin 3 × Fin 3 => overlapPiece W i j i' j' p.1 p.2)) _ _ (fun p => ?_)
  have hf : (Scheme.Opens.iSupOpenCover
      (fun p : Fin 3 × Fin 3 => overlapPiece W i j i' j' p.1 p.2)).f p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun p : Fin 3 × Fin 3 => overlapPiece W i j i' j' p.1 p.2) p) := rfl
  rw [hf]
  exact (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ p) hk (addOnYOnImage W hΔ i j)).trans
    ((overlapPiece_addOnYOnImage_agree W i j i' j' hΔ p.1 p.2).trans
      (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ p) hl (addOnYOnImage W hΔ i' j')).symm)

variable [IsDomain R]

/-- **([C4-HF-ASSEMBLY] L5, the four-chart pairwise agreement)** The `hf` obligation of
`glueMorphisms` for the `blOpenYFamily` cover: any two of the four chart-product law-2 morphisms
agree
on their overlap. The 16 cases (`fin_cases`) each reduce to `addOnYOnImage_agree` for the
corresponding
chart pair (diagonal included — same-chart agreement is the same statement). -/
lemma addOnYFamily_agree (hΔ : IsUnit W.Δ) (p q : Fin 2 × Fin 2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left : blOpenYFamily W p ⊓ blOpenYFamily W q ≤ blOpenYFamily W p) ≫
        addOnYFamily W hΔ p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ addOnYFamily W hΔ q := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    exact addOnYOnImage_agree W _ _ _ _ hΔ _ inf_le_left inf_le_right
      (blOpenYImage_inf_eq_iSup W _ _ _ _)

/-- **([C4-HF-ASSEMBLY] L5, addOnY — the second Bosma–Lenstra law as a morphism)** The `Y = 0`
addition law glued into a single scheme morphism on its whole regularity open `blOpenY = ⨆
blOpenYFamily`.
`glueMorphisms` on the four-chart cover, with the pairwise agreement `addOnYFamily_agree` packaged
by
`glueMorphisms_hf_of_agree`. This is the geometric assembly of T-W7.0c-i (Y-law). -/
noncomputable def addOnY (hΔ : IsUnit W.Δ) : (blOpenY W).toScheme ⟶ projModel W :=
  (blOpenYCover W).glueMorphisms (addOnYFamily W hΔ)
    (glueMorphisms_hf_of_agree (blOpenYFamily W) (addOnYFamily W hΔ) (addOnYFamily_agree W hΔ))

end Overlap

section OverlapZ

variable (i j i' j' : Fin 3)

lemma transι_preimage_blOpenZImage_piece (k : Fin 3) :
    transι W i j i' j' ⁻¹ᵁ (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) =
      specBasicOpen (CommRingCat.of (transRing W i j i' j'))
        (transAlgHom W i j i' j' (lawOneTriple W i j k)) := by
  show (Spec.map (CommRingCat.ofHom (transAlgHom W i j i' j').toRingHom) ≫
    (chartPieceIso W i j).inv ≫ pieceι W i j) ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq,
    blOpenZPieceFamily,
    ← Scheme.Hom.comp_preimage (chartPieceIso W i j).inv (chartPieceIso W i j).hom,
    Iso.inv_hom_id, Scheme.Hom.id_preimage]
  exact SpecMap_preimage_basicOpen _ _

/-- **([C4-HF-ASSEMBLY] L2b)** Via the `(i',j')` factorization (`transι_eq`), the preimage of the
`(i',j')` k'-th image piece is the basic open where `transHom(lawOneTriple i'j' k')` is invertible.
-/
lemma transι_preimage_blOpenZImage_piece' (k' : Fin 3) :
    transι W i j i' j' ⁻¹ᵁ (pieceι W i' j' ''ᵁ blOpenZPieceFamily W i' j' k') =
      specBasicOpen (CommRingCat.of (transRing W i j i' j'))
        (transHom W i j i' j' (lawOneTriple W i' j' k')) := by
  rw [transι_eq]
  show (Spec.map (CommRingCat.ofHom (transHom W i j i' j').toRingHom) ≫
    (chartPieceIso W i' j').inv ≫ pieceι W i' j') ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq,
    blOpenZPieceFamily,
    ← Scheme.Hom.comp_preimage (chartPieceIso W i' j').inv (chartPieceIso W i' j').hom,
    Iso.inv_hom_id, Scheme.Hom.id_preimage]
  exact SpecMap_preimage_basicOpen _ _

/-- **([C4-HF-ASSEMBLY] L2c)** The preimage under `transι` of the overlap piece `A_k ⊓ B_k'` is the
single basic open of `Spec transRing` at the product of the two transported piece coordinates — the
affine identification of the overlap piece with the triple-localization locus. -/
lemma transι_preimage_pieceZ_inf (k k' : Fin 3) :
    transι W i j i' j' ⁻¹ᵁ ((pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) ⊓
        (pieceι W i' j' ''ᵁ blOpenZPieceFamily W i' j' k')) =
      specBasicOpen (CommRingCat.of (transRing W i j i' j'))
        (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k')) := by
  rw [Scheme.Hom.preimage_inf, transι_preimage_blOpenZImage_piece,
    transι_preimage_blOpenZImage_piece', specBasicOpen_mul]

/-- **([C4-HF-ASSEMBLY] L3)** The affine immersion of the k-th image piece:
`Spec(Away(lawOneTriple ij k)) → E ×_R E`. -/
noncomputable def pieceAwayZι (k : Fin 3) :
    Spec (CommRingCat.of (Localization.Away (lawOneTriple W i j k))) ⟶
      pullback (projModelπ W) (projModelπ W) :=
  (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).hom ≫
    (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).ι ≫
    (chartPieceIso W i j).inv ≫ pieceι W i j

set_option backward.isDefEq.respectTransparency.types false in
/-- **([C4-HF-ASSEMBLY] L3, the σ-immersion identity)** The `isoImage/morphismRestrict/
specBasicOpenIsoAway.inv` chain out of `A_k` (the `σ` of L1), followed by `pieceAwayZι`, is exactly
`A_k.ι`. So `σ` is the section identifying `A_k` with `Spec(Away(lawOneTriple ij k))`, and
`pieceAwayZι` its immersion into `E ×_R E`. Instantiates the variable-scheme
`isoImage_inv_morphismRestrict_ι`. -/
lemma isoImage_specBasicOpen_pieceAwayZι (k : Fin 3) :
    ((Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
        (lawOneTriple W i j k)).inv) ≫ pieceAwayZι W i j k =
      (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k).ι := by
  rw [pieceAwayZι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact isoImage_inv_morphismRestrict_ι (pieceι W i j) (chartPieceIso W i j)
    (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k))

/-- **([C4-HF-ASSEMBLY] L3b1)** `pieceAwayZι` in `Spec.map` form: the localization map into
`Away(lawOneTriple ij k)` followed by the chart-product identification and the piece immersion — the
same shape as `transι`, localizing at a single piece coordinate instead of the transition product.
-/
lemma pieceAwayZι_eq (k : Fin 3) :
    pieceAwayZι W i j k =
      Spec.map (CommRingCat.ofHom (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)))) ≫
        (chartPieceIso W i j).inv ≫ pieceι W i j := by
  rw [pieceAwayZι, ← Category.assoc, specBasicOpenIsoAway_hom_ι]

/-- The overlap piece `P := A_k ⊓ B_k'` of two law-2 regularity image pieces. -/
noncomputable abbrev overlapPieceZ (k k' : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) ⊓
    (pieceι W i' j' ''ᵁ blOpenZPieceFamily W i' j' k')

/-- **([C4-HF-ASSEMBLY] L3, the affine identification)** `Spec(Away transRing g) ≅ P`, where
`g = transAlgHom(lawOneTriple ij k) · transHom(lawOneTriple i'j' k')`. Built from
`specBasicOpenIsoAway`,
the preimage computation `transι_preimage_pieceZ_inf` (L2c), and `transι.isoImage` (P ≤ range transι
by helper A). This is `w`: it makes the overlap piece an affine `Spec`, where every morphism out of
it
is `Spec.map`. -/
noncomputable def overlapPieceZIso (k k' : Fin 3) :
    Spec (CommRingCat.of (Localization.Away
        (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k')))) ≅
      (overlapPieceZ W i j i' j' k k').toScheme :=
  specBasicOpenIsoAway (CommRingCat.of (transRing W i j i' j'))
      (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawOneTriple W i' j' k')) ≪≫
    ((Spec (CommRingCat.of (transRing W i j i' j'))).isoOfEq
      (transι_preimage_pieceZ_inf W i j i' j' k k').symm) ≪≫
    Scheme.Hom.isoImage (transι W i j i' j')
      (transι W i j i' j' ⁻¹ᵁ overlapPieceZ W i j i' j' k k') ≪≫
    (pullback (projModelπ W) (projModelπ W)).isoOfEq (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
      exact (inf_le_inf ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))
        ((pieceι W i' j').image_mono (le_iSup (blOpenZPieceFamily W i' j') k'))).trans
        (blOpenZImage_inf_le_transι W i j i' j'))

/-- **([C4-HF-ASSEMBLY] L3, w-transι identity)** The affine identification, composed with the piece
inclusion into `E ×_R E`, is `Spec` of the localization `transRing → S` followed by `transι`. -/
lemma overlapPieceZIso_hom_ι (k k' : Fin 3) :
    (overlapPieceZIso W i j i' j' k k').hom ≫ (overlapPieceZ W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [overlapPieceZIso]
  simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc,
    Scheme.Hom.isoImage_hom_ι]
  rw [← Category.assoc, specBasicOpenIsoAway_hom_ι]

lemma isUnit_algebraMap_biChartRing_lawOneTriple (k k' : Fin 3) :
    IsUnit ((algebraMap (biChartRing W i j)
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k'))))
      (lawOneTriple W i j k)) := by
  rw [IsScalarTower.algebraMap_apply (biChartRing W i j) (transRing W i j i' j')
    (Localization.Away _)]
  exact IsLocalization.Away.isUnit_of_dvd
    (transAlgHom W i j i' j' (lawOneTriple W i j k) * transHom W i j i' j'
      (lawOneTriple W i' j' k'))
    ⟨transHom W i j i' j' (lawOneTriple W i' j' k'), rfl⟩

/-- **([C4-HF-ASSEMBLY] L3, ψ_ij)** The localization lift `Away(lawOneTriple ij k) →ₐ[R] S` into the
triple-localization, agreeing with the tower map `biChartRing → S` on the base. -/
noncomputable def psiFstZ (k k' : Fin 3) :
    Localization.Away (lawOneTriple W i j k) →ₐ[R]
      Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawOneTriple W i' j' k')) :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R (biChartRing W i j) _)
    (lawOneTriple W i j k) (isUnit_algebraMap_biChartRing_lawOneTriple W i j i' j' k k')

@[simp]
lemma psiFstZ_algebraMap (k k' : Fin 3) (x : biChartRing W i j) :
    psiFstZ W i j i' j' k k' (algebraMap (biChartRing W i j) _ x) =
      algebraMap (biChartRing W i j) _ x :=
  IsLocalization.Away.lift_eq (lawOneTriple W i j k)
    (isUnit_algebraMap_biChartRing_lawOneTriple W i j i' j' k k') x

/-- **([C4-HF-ASSEMBLY] L3, ψ_ij ring identity)** ψ_ij restricted to `biChartRing` is the tower map
`biChartRing → S` — a whnf-safe `RingHom.ext` (the RHS is `algebraMap biChartRing S`, no
composition,
so it never forces the concrete triple-localization). -/
lemma psiFstZ_toRingHom_comp (k k' : Fin 3) :
    (psiFstZ W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i j) (Localization.Away (lawOneTriple W i j k))) =
      algebraMap (biChartRing W i j)
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k'))) :=
  RingHom.ext (psiFstZ_algebraMap W i j i' j' k k')

/-- **([C4-HF-ASSEMBLY] L3, ψ_ij tower factorization)** ψ_ij restricted to `biChartRing`, routed
through the *middle* ring `transRing` — `= (algebraMap transRing S).comp transAlgHom`, the tower
map read as "localize `transRing`, then pull back along `transAlgHom`". The middle term of the
`.trans` is `algebraMap biChartRing S`, syntactically shared by both halves so `Eq.trans` closes
it without ever unfolding the concrete triple-localization (contrast: `rw
[algebraMap_biChartRing_eq]`
on a goal already carrying `algebraMap biChartRing S` explodes `isDefEq`). This is the form the
`Spec.map` identification consumes, keeping `algebraMap biChartRing S` out of the scheme goal. -/
lemma psiFstZ_toRingHom_comp' (k k' : Fin 3) :
    (psiFstZ W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i j) (Localization.Away (lawOneTriple W i j k))) =
      (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k')))).comp
        (transAlgHom W i j i' j').toRingHom :=
  (psiFstZ_toRingHom_comp W i j i' j' k k').trans
    (algebraMap_biChartRing_eq W i j i' j' _)

/-- **([C4-HF-ASSEMBLY] L3, the ψ_ij–σ identification)** `Spec(ψ_ij) ≫ pieceAwayZι =
Spec(transRing→S) ≫
transι`: the piece immersion `σ = pieceAwayZι` precomposed with `Spec(ψ_ij)` is the
triple-localization
immersion `transι` precomposed with `Spec` of the localization `transRing → S`. Both sides reduce,
via the definitions of `pieceAwayZι`/`transι` and functoriality of `Spec`, to
`Spec(ofHom ((algebraMap transRing S).comp transAlgHom)) ≫ (chartPieceIso).inv ≫ pieceι`; the shared
tail and the base identity `psiFstZ_toRingHom_comp'` are packaged by `spec_map_comp_congr` (the
variable-ring barrier), which keeps `isDefEq` off the concrete tower — under 5k heartbeats. -/
lemma specMap_psiFstZ_pieceAwayZι (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiFstZ W i j i' j' k k').toRingHom) ≫ pieceAwayZι W i j k =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [pieceAwayZι_eq, transι]
  exact spec_map_comp_congr _ _ _ _ _
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, psiFstZ_toRingHom_comp'])

/-- **([C4-HF-ASSEMBLY] L3, w ≫ ι = Spec(ψ_ij) ≫ σ)** The two affine factorizations of the overlap
immersion agree: the affine identification `w = overlapPieceZIso` (`P ≅ Spec S`) into `E ×_R E`
equals
`Spec(ψ_ij)` followed by the k-th piece immersion `σ = pieceAwayZι`. Both routes share the value
`Spec(transRing → S) ≫ transι` — `w` by `overlapPieceZIso_hom_ι`, the ψ_ij route by
`specMap_psiFstZ_pieceAwayZι` — so this is their transitive glue. This is the identity L4/L5
precompose
against `w.hom` and cancel (`w` an iso). -/
lemma overlapPieceZIso_hom_ι_eq_specMap_psiFstZ (k k' : Fin 3) :
    (overlapPieceZIso W i j i' j' k k').hom ≫ (overlapPieceZ W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (psiFstZ W i j i' j' k k').toRingHom) ≫ pieceAwayZι W i j k :=
  (overlapPieceZIso_hom_ι W i j i' j' k k').trans
    (specMap_psiFstZ_pieceAwayZι W i j i' j' k k').symm

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j' unit)** The second transition coordinate `transHom(lawOneTriple
i'j' k')` maps to a unit in `S`: it is the second factor of the localization generator, hence
divides
it. The `(i',j')`-side analogue of `isUnit_algebraMap_biChartRing_lawOneTriple`, but stated directly
over `transRing` (no `biChartRing → transRing` rewrite — the map is `transHom`, not the canonical
tower map). -/
lemma isUnit_algebraMap_transRing_transHom_lawOneTriple (k k' : Fin 3) :
    IsUnit (((IsScalarTower.toAlgHom R (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k')))).comp
        (transHom W i j i' j')) (lawOneTriple W i' j' k')) := by
  rw [AlgHom.comp_apply]
  exact IsLocalization.Away.isUnit_of_dvd
    (transAlgHom W i j i' j' (lawOneTriple W i j k) * transHom W i j i' j'
      (lawOneTriple W i' j' k'))
    ⟨transAlgHom W i j i' j' (lawOneTriple W i j k), mul_comm _ _⟩

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j')** The `(i',j')`-side localization lift `Away(lawOneTriple i'j'
k')
→ₐ[R] S`. Unlike `ψ_ij = psiFstZ`, its base map is built *explicitly* through the middle ring —
`(algebraMap transRing S).comp transHom` — since `transHom` (not the canonical scalar tower) carries
`biChartRing(i'j')` into `transRing`. Consequently its base identity `psiSndZ_toRingHom_comp'` is
direct
(no `.trans` bridge, no composite `algebraMap biChartRing(i'j') S` instance). -/
noncomputable def psiSndZ (k k' : Fin 3) :
    Localization.Away (lawOneTriple W i' j' k') →ₐ[R]
      Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawOneTriple W i' j' k')) :=
  IsLocalization.Away.liftAlgHom
    (f := (IsScalarTower.toAlgHom R (transRing W i j i' j') _).comp (transHom W i j i' j'))
    (lawOneTriple W i' j' k') (isUnit_algebraMap_transRing_transHom_lawOneTriple W i j i' j' k k')

@[simp]
lemma psiSndZ_algebraMap (k k' : Fin 3) (x : biChartRing W i' j') :
    psiSndZ W i j i' j' k k' (algebraMap (biChartRing W i' j') _ x) =
      algebraMap (transRing W i j i' j') _ (transHom W i j i' j' x) := by
  rw [psiSndZ, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (lawOneTriple W i' j' k')
      (isUnit_algebraMap_transRing_transHom_lawOneTriple W i j i' j' k k') x]
  rfl

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j' tower factorization)** ψ_i'j' restricted to `biChartRing(i'j')`
is
`(algebraMap transRing S).comp transHom` — direct from `liftAlgHom_algebraMap` (the base map already
IS
this composite), no whnf hazard. -/
lemma psiSndZ_toRingHom_comp' (k k' : Fin 3) :
    (psiSndZ W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i' j') (Localization.Away (lawOneTriple W i' j' k'))) =
      (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k')))).comp
        (transHom W i j i' j').toRingHom :=
  RingHom.ext (psiSndZ_algebraMap W i j i' j' k k')

/-- **([C4-HF-ASSEMBLY] L3, ψ_i'j'–σ identification)** `Spec(ψ_i'j') ≫ pieceAwayZι(i'j'k') =
Spec(transRing→S) ≫ transι`: the `(i',j')`-piece immersion precomposed with `Spec(ψ_i'j')` is the
triple-localization immersion, reading `transι` through the `(i',j')` chart-product (`transι_eq`,
the
`transHom` form). The psiSndZ mirror of `specMap_psiFstZ_pieceAwayZι`, again packaged by the
variable-ring
barrier `spec_map_comp_congr` so `isDefEq` never touches the concrete tower. -/
lemma specMap_psiSndZ_pieceAwayZι (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiSndZ W i j i' j' k k').toRingHom) ≫ pieceAwayZι W i' j' k' =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawOneTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [pieceAwayZι_eq, transι_eq]
  exact spec_map_comp_congr _ _ _ _ _
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, psiSndZ_toRingHom_comp'])

/-- **([C4-HF-ASSEMBLY] L3, w.hom ≫ ι = Spec(ψ_i'j') ≫ σ')** The `(i',j')`-side reading of the
overlap
immersion: `w` into `E ×_R E` equals `Spec(ψ_i'j')` followed by the `(i',j')`-piece immersion. The
psiSndZ mirror of `overlapPieceZIso_hom_ι_eq_specMap_psiFstZ`, sharing the same value
`Spec(transRing → S) ≫ transι`. Together the two give the cross-chart glue. -/
lemma overlapPieceZIso_hom_ι_eq_specMap_psiSndZ (k k' : Fin 3) :
    (overlapPieceZIso W i j i' j' k k').hom ≫ (overlapPieceZ W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (psiSndZ W i j i' j' k k').toRingHom) ≫ pieceAwayZι W i' j' k' :=
  (overlapPieceZIso_hom_ι W i j i' j' k k').trans
    (specMap_psiSndZ_pieceAwayZι W i j i' j' k k').symm



/-- **([C4-HF-ASSEMBLY] L4, ψ_ij pushed triple)** ψ_ij carries the `(i,j)` law-2 triple to
`algebraMap transRing S ∘ (transAlgHom ∘ lawOneTriple ij)` — the `(i,j)` reading of the addition
triple over `S`. Element-level tower step (`algebraMap_biChartRing_eq` via `congrFun`, term-mode so
it
never whnf-explodes), keeping the composite `algebraMap biChartRing S` out of the goal. -/
lemma psiFstZ_algebraMap_lawOneTriple (k k' m : Fin 3) :
    psiFstZ W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j m)) =
      algebraMap (transRing W i j i' j') _ (transAlgHom W i j i' j' (lawOneTriple W i j m)) := by
  rw [psiFstZ_algebraMap]
  exact congrFun (congrArg DFunLike.coe (algebraMap_biChartRing_eq W i j i' j' _))
    (lawOneTriple W i j m)

/-- The `k`-th coordinate of the ψ_ij-pushed triple is invertible with the pushed `invSelf`. -/
lemma psiFstZ_algebraMap_mul_invSelf (k k' : Fin 3) :
    psiFstZ W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j k)) *
      psiFstZ W i j i' j' k k' (IsLocalization.Away.invSelf (lawOneTriple W i j k)) = 1 := by
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- The `k'`-th coordinate of the ψ_i'j'-pushed triple is invertible with the pushed `invSelf`. -/
lemma psiSndZ_algebraMap_mul_invSelf (k k' : Fin 3) :
    psiSndZ W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawOneTriple W i' j' k')) (lawOneTriple W i' j' k')) *
      psiSndZ W i j i' j' k k' (IsLocalization.Away.invSelf (lawOneTriple W i' j' k')) = 1 := by
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- **([C4-HF-ASSEMBLY] L4, proportionality over S)** The two pushed triples are proportional: the
ψ_i'j' triple is `(cd)²`-times the ψ_ij triple over `S`, the bidegree-`(2,2)` transition factor
pushed
from `transRing` (`transHom_lawOneTriple_eq_smul`). Term-mode `.trans` chain (all middles are
`algebraMap transRing S …`, never the composite), so it stays off the concrete tower. This is the
crux's
`hsmul` hypothesis. -/
lemma psiSndZ_algebraMap_lawOneTriple_eq_smul (k k' m : Fin 3) :
    psiSndZ W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawOneTriple W i' j' k')) (lawOneTriple W i' j' m)) =
      algebraMap (transRing W i j i' j') _
        ((transInvFst W i j i' j' * transInvSnd W i j i' j') ^ 2) *
      psiFstZ W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j m)) :=
  (psiSndZ_algebraMap W i j i' j' k k' (lawOneTriple W i' j' m)).trans
    ((congrArg (algebraMap (transRing W i j i' j') _)
        (transHom_lawOneTriple_eq_smul W i j i' j' m)).trans
      ((map_mul _ _ _).trans
        (congrArg (algebraMap (transRing W i j i' j') _
            ((transInvFst W i j i' j' * transInvSnd W i j i' j') ^ 2) * ·)
          (psiFstZ_algebraMap_lawOneTriple W i j i' j' k k' m).symm)))

variable [IsJacobsonRing R]

/-- **([C4-HF-ASSEMBLY] L4, ψ_ij triple on-curve)** The ψ_ij-pushed law-2 triple satisfies the model
equation over `S`. Routed through `transRing` (via `transAlgHom`, the canonical tower map — cheap
`[Algebra transRing S]`), never the composite `[Algebra biChartRing S]`. -/
lemma equation_psiFstZ_lawOneTriple [IsDomain (biChartRing W i j)] (hΔ : IsUnit W.Δ)
  (k k' : Fin 3) :
    (W.map (algebraMap R (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawOneTriple W i' j' k'))))).toProjective.Equation
        (fun m => psiFstZ W i j i' j' k k' (algebraMap (biChartRing W i j)
          (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j m))) := by
  rw [funext (psiFstZ_algebraMap_lawOneTriple W i j i' j' k k')]
  exact equation_mapTriple W (fun m => transAlgHom W i j i' j' (lawOneTriple W i j m))
    (equation_mapTriple_algHom W (transAlgHom W i j i' j') (lawOneTriple W i j)
      (equation_lawOneTriple_of_isDomain W i j hΔ))

/-- **([C4-HF-ASSEMBLY] L4, ψ_i'j' triple on-curve)** The ψ_i'j'-pushed law-2 triple satisfies the
model equation over `S`, routed through `transRing` via `transHom` (`equation_mapTriple_algHom`). -/
lemma equation_psiSndZ_lawOneTriple [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ)
  (k k' : Fin 3) :
    (W.map (algebraMap R (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawOneTriple W i' j' k'))))).toProjective.Equation
        (fun m => psiSndZ W i j i' j' k k' (algebraMap (biChartRing W i' j')
          (Localization.Away (lawOneTriple W i' j' k')) (lawOneTriple W i' j' m))) := by
  rw [funext (fun m => psiSndZ_algebraMap W i j i' j' k k' (lawOneTriple W i' j' m))]
  exact equation_mapTriple W (fun m => transHom W i j i' j' (lawOneTriple W i' j' m))
    (equation_mapTriple_algHom W (transHom W i j i' j') (lawOneTriple W i' j')
      (equation_lawOneTriple_of_isDomain W i' j' hΔ))

/-- **([C4-HF-ASSEMBLY] L4, THE cross-chart ψ-agreement)** Over `Spec S`, the `(i,j,k)` and
`(i',j',k')` law-2 piece morphisms agree after pulling back along `Spec(ψ_ij)`, `Spec(ψ_i'j')`. Both
sides go to `chartAwayHomOfTriple`-form via `specMap_comp_pieceMorOfTriple`, and the general crux
`chartι_comp_specMap_chartAwayHom_smul_eq` closes them using the proportionality of the two pushed
triples. Term-mode `.trans` chain with syntactically-shared `chartAwayHomOfTriple` middles — the
decomposition into clean-context sub-lemmas is what keeps `isDefEq` off the concrete tower. -/
lemma specMap_psiFstZ_addOnZPieceMor_cross [IsDomain (biChartRing W i j)]
    [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ) (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiFstZ W i j i' j' k k').toRingHom) ≫ addOnZPieceMor W i j k hΔ =
      Spec.map (CommRingCat.ofHom (psiSndZ W i j i' j' k k').toRingHom) ≫
        addOnZPieceMor W i' j' k' hΔ := by
  rw [addOnZPieceMor_eq, addOnZPieceMor_eq]
  exact (specMap_comp_pieceMorOfTriple W (lawOneTriple W i j)
      (equation_lawOneTriple_of_isDomain W i j hΔ) k (psiFstZ W i j i' j' k k')
      (psiFstZ_algebraMap_mul_invSelf W i j i' j' k k')
      (equation_psiFstZ_lawOneTriple W i j i' j' hΔ k k')).trans
    (((chartι_comp_specMap_chartAwayHom_smul_eq W k k' _ _ _ _ _
        (psiSndZ_algebraMap_lawOneTriple_eq_smul W i j i' j' k k')
        (psiFstZ_algebraMap_mul_invSelf W i j i' j' k k')
        (psiSndZ_algebraMap_mul_invSelf W i j i' j' k k')
        (equation_psiFstZ_lawOneTriple W i j i' j' hΔ k k')
        (equation_psiSndZ_lawOneTriple W i j i' j' hΔ k k')).symm).trans
      (specMap_comp_pieceMorOfTriple W (lawOneTriple W i' j')
        (equation_lawOneTriple_of_isDomain W i' j' hΔ) k' (psiSndZ W i j i' j' k k')
        (psiSndZ_algebraMap_mul_invSelf W i j i' j' k k')
        (equation_psiSndZ_lawOneTriple W i j i' j' hΔ k k')).symm)

/-- The `k`-th piece immersion `pieceAwayZι` is an open immersion (hence mono): a composite of the
`specBasicOpenIsoAway` iso, the basic-open immersion, the chart-product iso, and `pieceι`. -/
instance instIsOpenImmersionPieceAwayZι (k : Fin 3) : IsOpenImmersion (pieceAwayZι W i j k) := by
  rw [pieceAwayZι]; infer_instance

omit [IsJacobsonRing R] in
set_option backward.isDefEq.respectTransparency.types false in
/-- **([C4-HF-ASSEMBLY] L5, σ-cancel, (i,j) side)** `w.hom` followed by the `(i,j)` L1 prefactor `σ`
(the `homOfLE / isoImage.inv / morphismRestrict / specBasicOpenIsoAway.inv` chain landing in
`Spec(Away(lawOneTriple ij k))`) equals `Spec(ψ_ij)`. Cancelled against the `pieceAwayZι` mono: both
composed with `pieceAwayZι` give `w.hom ≫ overlapPieceZ.ι` (via the σ-immersion identity
`isoImage_specBasicOpen_pieceAwayZι` and `Scheme.homOfLE_ι`), which is `Spec(ψ_ij) ≫ pieceAwayZι` by
L3.
This turns L1's image-level prefactor into `Spec(ψ_ij)` once precomposed with `w`. -/
@[reassoc]
lemma w_homOfLE_sigma_psiFstZ (k k' : Fin 3) :
    (overlapPieceZIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left : overlapPieceZ W i j i' j' k k' ≤
          pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) ≫
      (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv =
    Spec.map (CommRingCat.ofHom (psiFstZ W i j i' j' k k').toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv ≫
      pieceAwayZι W i j k = (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k).ι := by
    rw [← isoImage_specBasicOpen_pieceAwayZι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceAwayZι W i j k)]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact overlapPieceZIso_hom_ι_eq_specMap_psiFstZ W i j i' j' k k'

omit [IsJacobsonRing R] in
set_option backward.isDefEq.respectTransparency.types false in
/-- **([C4-HF-ASSEMBLY] L5, σ-cancel, (i',j') side)** The psiSndZ mirror of
`w_homOfLE_sigma_psiFstZ`. -/
@[reassoc]
lemma w_homOfLE_sigma_psiSndZ (k k' : Fin 3) :
    (overlapPieceZIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right : overlapPieceZ W i j i' j' k k' ≤
          pieceι W i' j' ''ᵁ blOpenZPieceFamily W i' j' k') ≫
      (Scheme.Hom.isoImage (pieceι W i' j') (blOpenZPieceFamily W i' j' k')).inv ≫
      morphismRestrict (chartPieceIso W i' j').hom
        (specBasicOpen (CommRingCat.of (biChartRing W i' j')) (lawOneTriple W i' j' k')) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i' j')) (lawOneTriple W i' j' k')).inv =
    Spec.map (CommRingCat.ofHom (psiSndZ W i j i' j' k k').toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i' j') (blOpenZPieceFamily W i' j' k')).inv ≫
      morphismRestrict (chartPieceIso W i' j').hom
        (specBasicOpen (CommRingCat.of (biChartRing W i' j')) (lawOneTriple W i' j' k')) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i' j')) (lawOneTriple W i' j' k')).inv ≫
      pieceAwayZι W i' j' k' = (pieceι W i' j' ''ᵁ blOpenZPieceFamily W i' j' k').ι := by
    rw [← isoImage_specBasicOpen_pieceAwayZι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceAwayZι W i' j' k')]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact overlapPieceZIso_hom_ι_eq_specMap_psiSndZ W i j i' j' k k'

/-- **([C4-HF-ASSEMBLY] L5, per-overlap chart agreement)** On the overlap piece `A_k ⊓ B_k'`, the
`(i,j)` and `(i',j')` image-level law-2 morphisms agree. Proved by precomposing with the affine
identification `w` (an iso, cancelled via `cancel_epi`): L1 turns each side into `σ ≫
addOnZPieceMor`,
the σ-cancels turn `w.hom ≫ σ` into `Spec(ψ)`, and L4 identifies the two `Spec(ψ) ≫ addOnZPieceMor`.
Fully term-mode (`congrArg`/`.trans`) so no `rw` motive ever touches the concrete tower `S`. -/
lemma overlapPieceZ_addOnZOnImage_agree [IsDomain (biChartRing W i j)]
    [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ) (k k' : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left.trans ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))) ≫
        addOnZOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right.trans ((pieceι W i' j').image_mono (le_iSup
          (blOpenZPieceFamily W i' j') k'))) ≫
        addOnZOnImage W hΔ i' j' := by
  have eL : (overlapPieceZIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left.trans ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))) ≫
        addOnZOnImage W hΔ i j =
      Spec.map (CommRingCat.ofHom
        (psiFstZ W i j i' j' k k').toRingHom) ≫ addOnZPieceMor W i j k hΔ :=
    (congrArg ((overlapPieceZIso W i j i' j' k k').hom ≫ ·)
        (homOfLE_addOnZOnImage_eq W i j hΔ k (overlapPieceZ W i j i' j' k k') inf_le_left)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnZPieceMor W i j k hΔ) (w_homOfLE_sigma_psiFstZ W i j i' j' k k')))
  have eR : (overlapPieceZIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right.trans ((pieceι W i' j').image_mono (le_iSup
          (blOpenZPieceFamily W i' j') k'))) ≫
        addOnZOnImage W hΔ i' j' =
      Spec.map (CommRingCat.ofHom
        (psiSndZ W i j i' j' k k').toRingHom) ≫ addOnZPieceMor W i' j' k' hΔ :=
    (congrArg ((overlapPieceZIso W i j i' j' k k').hom ≫ ·)
        (homOfLE_addOnZOnImage_eq W i' j' hΔ k'
          (overlapPieceZ W i j i' j' k k') inf_le_right)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnZPieceMor W i' j' k' hΔ) (w_homOfLE_sigma_psiSndZ W i j i' j' k k')))
  exact (cancel_epi (overlapPieceZIso W i j i' j' k k').hom).mp
    (eL.trans ((specMap_psiFstZ_addOnZPieceMor_cross W i j i' j' hΔ k k').trans eR.symm))

/-- **([C4-HF-ASSEMBLY] L5, full cross-chart agreement)** The `(i,j)` and `(i',j')` image-level
law-2
morphisms agree on their entire overlap `blOpenZImage(i,j) ⊓ blOpenZImage(i',j')`. The overlap is
covered by the `(k,k')` overlap pieces (`blOpenZImage_inf_eq_iSup`), so `Scheme.Cover.hom_ext`
reduces
to the per-piece agreement `overlapPieceZ_addOnZOnImage_agree`; the two nested `homOfLE`s of the
cover
inclusion and the overlap inclusion collapse via `Scheme.homOfLE_homOfLE_assoc`. Stated with the
overlap `Ω` as a parameter (`subst`) so the cover lands on it directly, no dependent rewriting. -/
lemma addOnZOnImage_agree [IsDomain (biChartRing W i j)] [IsDomain (biChartRing W i' j')]
    (hΔ : IsUnit W.Δ) (Ω : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hk : Ω ≤ blOpenZImage W i j) (hl : Ω ≤ blOpenZImage W i' j')
    (hΩ : Ω = ⨆ p : Fin 3 × Fin 3, overlapPieceZ W i j i' j' p.1 p.2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnZOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE hl ≫ addOnZOnImage W hΔ i' j' := by
  subst hΩ
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun p : Fin 3 × Fin 3 => overlapPieceZ W i j i' j' p.1 p.2)) _ _ (fun p => ?_)
  have hf : (Scheme.Opens.iSupOpenCover
      (fun p : Fin 3 × Fin 3 => overlapPieceZ W i j i' j' p.1 p.2)).f p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun p : Fin 3 × Fin 3 => overlapPieceZ W i j i' j' p.1 p.2) p) := rfl
  rw [hf]
  exact (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ p) hk (addOnZOnImage W hΔ i j)).trans
    ((overlapPieceZ_addOnZOnImage_agree W i j i' j' hΔ p.1 p.2).trans
      (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ p) hl (addOnZOnImage W hΔ i' j')).symm)

variable [IsDomain R]

/-- **([C4-HF-ASSEMBLY] L5, the four-chart pairwise agreement)** The `hf` obligation of
`glueMorphisms` for the `blOpenZFamily` cover: any two of the four chart-product law-2 morphisms
agree
on their overlap. The 16 cases (`fin_cases`) each reduce to `addOnZOnImage_agree` for the
corresponding
chart pair (diagonal included — same-chart agreement is the same statement). -/
lemma addOnZFamily_agree (hΔ : IsUnit W.Δ) (p q : Fin 2 × Fin 2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left : blOpenZFamily W p ⊓ blOpenZFamily W q ≤ blOpenZFamily W p) ≫
        addOnZFamily W hΔ p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ addOnZFamily W hΔ q := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    exact addOnZOnImage_agree W _ _ _ _ hΔ _ inf_le_left inf_le_right
      (blOpenZImage_inf_eq_iSup W _ _ _ _)

/-- **([C4-HF-ASSEMBLY] L5, addOnZ — the second Bosma–Lenstra law as a morphism)** The `Y = 0`
addition law glued into a single scheme morphism on its whole regularity open `blOpenZ = ⨆
blOpenZFamily`.
`glueMorphisms` on the four-chart cover, with the pairwise agreement `addOnZFamily_agree` packaged
by
`glueMorphisms_hf_of_agree`. This is the geometric assembly of T-W7.0c-i (Y-law). -/
noncomputable def addOnZ (hΔ : IsUnit W.Δ) : (blOpenZ W).toScheme ⟶ projModel W :=
  (blOpenZCover W).glueMorphisms (addOnZFamily W hΔ)
    (glueMorphisms_hf_of_agree (blOpenZFamily W) (addOnZFamily W hΔ) (addOnZFamily_agree W hΔ))

end OverlapZ

section OverlapCrossLaw

variable (i j : Fin 3)

/-- **(c3, general piece immersion)** `Spec(Away g) ↪ E ×_R E` for ANY generator `g : biChartRing`,
generalising `pieceAwayι` (which is the case `g = lawTwoTriple ij k`). The same-chart cross-law
overlap
piece is this at `g = lawTwoTriple ij k · lawOneTriple ij k`. -/
noncomputable def pieceGenι (g : biChartRing W i j) :
    Spec (CommRingCat.of (Localization.Away g)) ⟶ pullback (projModelπ W) (projModelπ W) :=
  (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) g).hom ≫
    (specBasicOpen (CommRingCat.of (biChartRing W i j)) g).ι ≫
    (chartPieceIso W i j).inv ≫ pieceι W i j

instance instIsOpenImmersionPieceGenι (g : biChartRing W i j) :
    IsOpenImmersion (pieceGenι W i j g) := by rw [pieceGenι]; infer_instance

/-- `pieceGenι` in `Spec.map` form (as `pieceAwayι_eq`). -/
lemma pieceGenι_eq (g : biChartRing W i j) :
    pieceGenι W i j g =
      Spec.map (CommRingCat.ofHom (algebraMap (biChartRing W i j) (Localization.Away g))) ≫
        (chartPieceIso W i j).inv ≫ pieceι W i j := by
  rw [pieceGenι, ← Category.assoc, specBasicOpenIsoAway_hom_ι]

/-- The `σ`-immersion identity for `pieceGenι` (as `isoImage_specBasicOpen_pieceAwayι`): the
`isoImage / morphismRestrict / specBasicOpenIsoAway.inv` chain out of the image piece, followed by
`pieceGenι`, is the image inclusion. -/
lemma isoImage_specBasicOpen_pieceGenι (g : biChartRing W i j) :
    ((Scheme.Hom.isoImage (pieceι W i j)
        ((chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j)) g)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) g) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) g).inv) ≫ pieceGenι W i j g =
      (pieceι W i j ''ᵁ ((chartPieceIso W i j).hom ⁻¹ᵁ
        specBasicOpen (CommRingCat.of (biChartRing W i j)) g)).ι := by
  rw [pieceGenι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact isoImage_inv_morphismRestrict_ι (pieceι W i j) (chartPieceIso W i j)
    (specBasicOpen (CommRingCat.of (biChartRing W i j)) g)

noncomputable abbrev crossPiece (k : Fin 3) : (pullback (projModelπ W) (projModelπ W)).Opens :=
  pieceι W i j ''ᵁ ((chartPieceIso W i j).hom ⁻¹ᵁ
    specBasicOpen (CommRingCat.of (biChartRing W i j))
      (lawTwoTriple W i j k * lawOneTriple W i j k))

noncomputable def crossPieceIso (k : Fin 3) :
    Spec (CommRingCat.of (Localization.Away
        (lawTwoTriple W i j k * lawOneTriple W i j k))) ≅ (crossPiece W i j k).toScheme :=
  (asIso ((Scheme.Hom.isoImage (pieceι W i j)
        ((chartPieceIso W i j).hom ⁻¹ᵁ specBasicOpen (CommRingCat.of (biChartRing W i j))
          (lawTwoTriple W i j k * lawOneTriple W i j k))).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j))
          (lawTwoTriple W i j k * lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
        (lawTwoTriple W i j k * lawOneTriple W i j k)).inv)).symm

lemma crossPieceIso_hom_ι (k : Fin 3) :
    (crossPieceIso W i j k).hom ≫ (crossPiece W i j k).ι =
      Spec.map (CommRingCat.ofHom (algebraMap (biChartRing W i j)
        (Localization.Away (lawTwoTriple W i j k * lawOneTriple W i j k)))) ≫
        (chartPieceIso W i j).inv ≫ pieceι W i j := by
  rw [← pieceGenι_eq, crossPieceIso, Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact (isoImage_specBasicOpen_pieceGenι W i j
    (lawTwoTriple W i j k * lawOneTriple W i j k)).symm

/-- crossPieceIso ≫ ι, Y-side: = Spec(awayPairRight) ≫ pieceAwayι(lawTwo_k). -/
lemma crossPieceIso_hom_ι_awayPairRight (k : Fin 3) :
    (crossPieceIso W i j k).hom ≫ (crossPiece W i j k).ι =
      Spec.map (CommRingCat.ofHom
        (awayPairRight R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) ≫
        pieceAwayι W i j k := by
  rw [crossPieceIso_hom_ι, pieceAwayι_eq, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  exact (RingHom.ext fun c => (awayPairRight_algebraMap R _ _ c).symm)

/-- crossPieceIso ≫ ι, Z-side: = Spec(awayPairLeft) ≫ pieceGenι(lawOne_k). -/
lemma crossPieceIso_hom_ι_awayPairLeft (k : Fin 3) :
    (crossPieceIso W i j k).hom ≫ (crossPiece W i j k).ι =
      Spec.map (CommRingCat.ofHom
        (awayPairLeft R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) ≫
        pieceGenι W i j (lawOneTriple W i j k) := by
  rw [crossPieceIso_hom_ι, pieceGenι_eq, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  exact (RingHom.ext fun c => (awayPairLeft_algebraMap R _ _ c).symm)
/-- crossPiece ≤ the k-th Y-piece image (D(lawTwo_k·lawOne_k) ⊆ D(lawTwo_k)). -/
lemma crossPiece_le_blOpenYPieceImage (k : Fin 3) :
    crossPiece W i j k ≤ pieceι W i j ''ᵁ blOpenYPieceFamily W i j k := by
  show pieceι W i j ''ᵁ _ ≤ pieceι W i j ''ᵁ blOpenYPieceFamily W i j k
  rw [blOpenYPieceFamily]; gcongr; exact specBasicOpen_mul_le_left _ _ _

/-- crossPiece ≤ the k-th Z-piece image (D(lawTwo_k·lawOne_k) ⊆ D(lawOne_k)). -/
lemma crossPiece_le_blOpenZPieceImage (k : Fin 3) :
    crossPiece W i j k ≤ pieceι W i j ''ᵁ blOpenZPieceFamily W i j k := by
  show pieceι W i j ''ᵁ _ ≤ pieceι W i j ''ᵁ blOpenZPieceFamily W i j k
  rw [blOpenZPieceFamily]; gcongr; exact specBasicOpen_mul_le_right _ _ _

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma crossHom_sigma_awayPairRight (k : Fin 3) :
    (crossPieceIso W i j k).hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE (crossPiece_le_blOpenYPieceImage W i j k) ≫
      (Scheme.Hom.isoImage (pieceι W i j) (blOpenYPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).inv =
    Spec.map (CommRingCat.ofHom
      (awayPairRight R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i j) (blOpenYPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).inv ≫
      pieceAwayι W i j k = (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k).ι := by
    rw [← isoImage_specBasicOpen_pieceAwayι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceAwayι W i j k)]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact crossPieceIso_hom_ι_awayPairRight W i j k

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma crossHom_sigma_awayPairLeft (k : Fin 3) :
    (crossPieceIso W i j k).hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE (crossPiece_le_blOpenZPieceImage W i j k) ≫
      (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv =
    Spec.map (CommRingCat.ofHom
      (awayPairLeft R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv ≫
      pieceGenι W i j (lawOneTriple W i j k) = (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k).ι := by
    simp only [blOpenZPieceFamily]
    rw [← isoImage_specBasicOpen_pieceGenι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceGenι W i j (lawOneTriple W i j k))]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact crossPieceIso_hom_ι_awayPairLeft W i j k

variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)]

/-- **(c3, per-crossPiece agreement)** On the overlap piece `crossPiece k = D(lawTwo_k·lawOne_k)`,
the
Z-law and Y-law image morphisms agree. Precompose with the affine iso `crossPieceIso` (cancel_epi);
L1
turns each into `σ ≫ pieceMor`, the σ-cancels turn `crossPieceIso.hom ≫ σ` into `Spec(awayPair)`,
and
`addOnYPieceMor_eq_addOnZPieceMor` identifies them. Fully term-mode. -/
lemma crossPiece_addOn_agree (hΔ : IsUnit W.Δ) (k : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((crossPiece_le_blOpenZPieceImage W i j k).trans
          ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))) ≫
        addOnZOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((crossPiece_le_blOpenYPieceImage W i j k).trans
          ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k))) ≫
        addOnYOnImage W hΔ i j := by
  have eZ : (crossPieceIso W i j k).hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((crossPiece_le_blOpenZPieceImage W i j k).trans
          ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))) ≫
        addOnZOnImage W hΔ i j =
      Spec.map (CommRingCat.ofHom
        (awayPairLeft R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) ≫
        addOnZPieceMor W i j k hΔ :=
    (congrArg ((crossPieceIso W i j k).hom ≫ ·)
        (homOfLE_addOnZOnImage_eq W i j hΔ k (crossPiece W i j k)
          (crossPiece_le_blOpenZPieceImage W i j k))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnZPieceMor W i j k hΔ) (crossHom_sigma_awayPairLeft W i j k)))
  have eY : (crossPieceIso W i j k).hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((crossPiece_le_blOpenYPieceImage W i j k).trans
          ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k))) ≫
        addOnYOnImage W hΔ i j =
      Spec.map (CommRingCat.ofHom
        (awayPairRight R (lawTwoTriple W i j k) (lawOneTriple W i j k)).toRingHom) ≫
        addOnYPieceMor W i j k hΔ :=
    (congrArg ((crossPieceIso W i j k).hom ≫ ·)
        (homOfLE_addOnYOnImage_eq W i j hΔ k (crossPiece W i j k)
          (crossPiece_le_blOpenYPieceImage W i j k))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnYPieceMor W i j k hΔ) (crossHom_sigma_awayPairRight W i j k)))
  exact (cancel_epi (crossPieceIso W i j k).hom).mp
    (eZ.trans (((addOnYPieceMor_eq_addOnZPieceMor W i j hΔ k).symm).trans eY.symm))


/-- **(c3, same-chart addOn_agree)** On a single chart-product `(i,j)`, the Z-law and Y-law image
morphisms agree on their whole overlap `blOpenZImage ⊓ blOpenYImage`. Cover.hom_ext over the
crossPiece
cover (`blOpenZImage_inf_blOpenYImage_eq_iSup`) → `crossPiece_addOn_agree`. -/
lemma addOnZOnImage_eq_addOnYOnImage (hΔ : IsUnit W.Δ)
    (Ω : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hk : Ω ≤ blOpenZImage W i j) (hl : Ω ≤ blOpenYImage W i j)
    (hΩ : Ω = ⨆ k, crossPiece W i j k) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnZOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE hl ≫ addOnYOnImage W hΔ i j := by
  subst hΩ
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun k : Fin 3 => crossPiece W i j k)) _ _ (fun k => ?_)
  have hf : (Scheme.Opens.iSupOpenCover (fun k : Fin 3 => crossPiece W i j k)).f k =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun k : Fin 3 => crossPiece W i j k) k) := rfl
  rw [hf]
  exact (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ k) hk (addOnZOnImage W hΔ i j)).trans
    ((crossPiece_addOn_agree W i j hΔ k).trans
      (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ k) hl (addOnYOnImage W hΔ i j)).symm)

end OverlapCrossLaw

section OverlapCrossChart

variable (i j i' j' : Fin 3)

/-- **(c3, cross-chart-cross-law overlap geometry)** The `transι`-preimage of the overlap where the
`(i,j)` Z-law k-th piece meets the `(i',j')` Y-law k'-th piece is the single basic open at
`transAlgHom(lawOne ijk) · transHom(lawTwo i'j'k')` — the cross-law analogue of
`transι_preimage_piece_inf`. This is the locus the cross-chart-cross-law `addOn_agree` reduces over
(and where the transRing tower — hence the isDefEq walls — recurs). -/
lemma transι_preimage_crossPiece_inf (k k' : Fin 3) :
    transι W i j i' j' ⁻¹ᵁ ((pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) ⊓
        (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k')) =
      specBasicOpen (CommRingCat.of (transRing W i j i' j'))
        (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')) := by
  rw [Scheme.Hom.preimage_inf, transι_preimage_blOpenZImage_piece,
    transι_preimage_blOpenYImage_piece', specBasicOpen_mul]

lemma blOpenZImage_inf_blOpenYImage_le_transι :
    blOpenZImage W i j ⊓ blOpenYImage W i' j' ≤ (transι W i j i' j').opensRange :=
  le_trans (inf_le_inf (blOpenZImage_le_range W i j) (blOpenYImage_le_range W i' j'))
    (pieceι_range_inf_le_transι W i j i' j')

noncomputable abbrev crossOverlapPiece (k k' : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).Opens :=
  (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) ⊓
    (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k')

noncomputable def crossOverlapPieceIso (k k' : Fin 3) :
    Spec (CommRingCat.of (Localization.Away
        (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))) ≅
      (crossOverlapPiece W i j i' j' k k').toScheme :=
  specBasicOpenIsoAway (CommRingCat.of (transRing W i j i' j'))
      (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k')) ≪≫
    ((Spec (CommRingCat.of (transRing W i j i' j'))).isoOfEq
      (transι_preimage_crossPiece_inf W i j i' j' k k').symm) ≪≫
    Scheme.Hom.isoImage (transι W i j i' j')
      (transι W i j i' j' ⁻¹ᵁ crossOverlapPiece W i j i' j' k k') ≪≫
    (pullback (projModelπ W) (projModelπ W)).isoOfEq (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right]
      exact (inf_le_inf ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))
        ((pieceι W i' j').image_mono (le_iSup (blOpenYPieceFamily W i' j') k'))).trans
        (blOpenZImage_inf_blOpenYImage_le_transι W i j i' j'))

lemma crossOverlapPieceIso_hom_ι (k k' : Fin 3) :
    (crossOverlapPieceIso W i j i' j' k k').hom ≫ (crossOverlapPiece W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [crossOverlapPieceIso]
  simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.isoOfEq_hom_ι_assoc,
    Scheme.Hom.isoImage_hom_ι]
  rw [← Category.assoc, specBasicOpenIsoAway_hom_ι]

/-- The cross-chart-cross-law minor over transRing: the two triples transAlgHom(lawOne ij) and
transHom(lawTwo i'j') have vanishing 2×2 minors. Combines transHom_lawTwoTriple_eq_smul
(cross-chart)
with the transAlgHom-pushed cross-law minor lawOneTriple_mul_lawTwoTriple. -/
lemma transHom_lawTwo_mul_transAlgHom_lawOne (k m : Fin 3) :
    transHom W i j i' j' (lawTwoTriple W i' j' m) *
        transAlgHom W i j i' j' (lawOneTriple W i j k) =
      transHom W i j i' j' (lawTwoTriple W i' j' k) *
        transAlgHom W i j i' j' (lawOneTriple W i j m) := by
  rw [transHom_lawTwoTriple_eq_smul, transHom_lawTwoTriple_eq_smul,
    mul_assoc, mul_assoc, ← map_mul, ← map_mul]
  congr 2
  rw [mul_comm (lawTwoTriple W i j m), mul_comm (lawTwoTriple W i j k),
    lawOneTriple_mul_lawTwoTriple]

lemma isUnit_algebraMap_biChartRing_lawOneTriple_cross (k k' : Fin 3) :
    IsUnit ((algebraMap (biChartRing W i j)
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))
      (lawOneTriple W i j k)) := by
  rw [IsScalarTower.algebraMap_apply (biChartRing W i j) (transRing W i j i' j')
    (Localization.Away _)]
  exact IsLocalization.Away.isUnit_of_dvd
    (transAlgHom W i j i' j' (lawOneTriple W i j k) * transHom W i j i' j'
      (lawTwoTriple W i' j' k'))
    ⟨transHom W i j i' j' (lawTwoTriple W i' j' k'), rfl⟩

noncomputable def psiFstCross (k k' : Fin 3) :
    Localization.Away (lawOneTriple W i j k) →ₐ[R]
      Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k')) :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom R (biChartRing W i j) _)
    (lawOneTriple W i j k) (isUnit_algebraMap_biChartRing_lawOneTriple_cross W i j i' j' k k')

@[simp]
lemma psiFstCross_algebraMap (k k' : Fin 3) (x : biChartRing W i j) :
    psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j) _ x) =
      algebraMap (biChartRing W i j) _ x :=
  IsLocalization.Away.lift_eq (lawOneTriple W i j k)
    (isUnit_algebraMap_biChartRing_lawOneTriple_cross W i j i' j' k k') x

lemma psiFstCross_toRingHom_comp' (k k' : Fin 3) :
    (psiFstCross W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i j) (Localization.Away (lawOneTriple W i j k))) =
      (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))).comp
        (transAlgHom W i j i' j').toRingHom :=
  (RingHom.ext (psiFstCross_algebraMap W i j i' j' k k')).trans
    (algebraMap_biChartRing_eq W i j i' j' _)

lemma isUnit_algebraMap_transRing_transHom_lawTwoTriple_cross (k k' : Fin 3) :
    IsUnit (((IsScalarTower.toAlgHom R (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))).comp
        (transHom W i j i' j')) (lawTwoTriple W i' j' k')) := by
  rw [AlgHom.comp_apply]
  exact IsLocalization.Away.isUnit_of_dvd
    (transAlgHom W i j i' j' (lawOneTriple W i j k) * transHom W i j i' j'
      (lawTwoTriple W i' j' k'))
    ⟨transAlgHom W i j i' j' (lawOneTriple W i j k), mul_comm _ _⟩

noncomputable def psiSndCross (k k' : Fin 3) :
    Localization.Away (lawTwoTriple W i' j' k') →ₐ[R]
      Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k')) :=
  IsLocalization.Away.liftAlgHom
    (f := (IsScalarTower.toAlgHom R (transRing W i j i' j') _).comp (transHom W i j i' j'))
    (lawTwoTriple W i' j' k')
      (isUnit_algebraMap_transRing_transHom_lawTwoTriple_cross W i j i' j' k k')

@[simp]
lemma psiSndCross_algebraMap (k k' : Fin 3) (x : biChartRing W i' j') :
    psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j') _ x) =
      algebraMap (transRing W i j i' j') _ (transHom W i j i' j' x) := by
  rw [psiSndCross, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq (lawTwoTriple W i' j' k')
      (isUnit_algebraMap_transRing_transHom_lawTwoTriple_cross W i j i' j' k k') x]
  rfl

lemma psiSndCross_toRingHom_comp' (k k' : Fin 3) :
    (psiSndCross W i j i' j' k k').toRingHom.comp
        (algebraMap (biChartRing W i' j') (Localization.Away (lawTwoTriple W i' j' k'))) =
      (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k')))).comp
        (transHom W i j i' j').toRingHom :=
  RingHom.ext (psiSndCross_algebraMap W i j i' j' k k')


lemma psiFstCross_algebraMap_lawOneTriple (k k' m : Fin 3) :
    psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j m)) =
      algebraMap (transRing W i j i' j') _ (transAlgHom W i j i' j' (lawOneTriple W i j m)) := by
  rw [psiFstCross_algebraMap]
  exact congrFun (congrArg DFunLike.coe (algebraMap_biChartRing_eq W i j i' j' _))
    (lawOneTriple W i j m)

lemma psiFstCross_algebraMap_mul_invSelf (k k' : Fin 3) :
    psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j k)) *
      psiFstCross W i j i' j' k k' (IsLocalization.Away.invSelf (lawOneTriple W i j k)) = 1 := by
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

lemma psiSndCross_algebraMap_mul_invSelf (k k' : Fin 3) :
    psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' k')) *
      psiSndCross W i j i' j' k k' (IsLocalization.Away.invSelf (lawTwoTriple W i' j' k')) = 1 := by
  rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- The proportionality (crux hsmul): the Y-triple over S' is `(t'_k · invSelf(t_k))`-times the
Z-triple.
Derived from the pushed cross-minor `transHom_lawTwo_mul_transAlgHom_lawOne` and `t_k · invSelf =
1`. -/
lemma psiSndCross_eq_smul (k k' m : Fin 3) :
    psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' m)) =
      (psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j')
          (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' k)) *
        psiFstCross W i j i' j' k k' (IsLocalization.Away.invSelf (lawOneTriple W i j k))) *
      psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j m)) := by
  have hmin : psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' m)) *
      psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j k)) =
      psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j')
        (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' k)) *
      psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j m)) :=
    (congr_arg₂ (· * ·) (psiSndCross_algebraMap W i j i' j' k k' (lawTwoTriple W i' j' m))
        (psiFstCross_algebraMap_lawOneTriple W i j i' j' k k' k)).trans
      (((map_mul (algebraMap (transRing W i j i' j') _) _ _).symm.trans
          ((congrArg (algebraMap (transRing W i j i' j') _)
              (transHom_lawTwo_mul_transAlgHom_lawOne W i j i' j' k m)).trans
            (map_mul (algebraMap (transRing W i j i' j') _) _ _))).trans
        (congr_arg₂ (· * ·) (psiSndCross_algebraMap W i j i' j' k k' (lawTwoTriple W i' j' k)).symm
          (psiFstCross_algebraMap_lawOneTriple W i j i' j' k k' m).symm))
  have hu := psiFstCross_algebraMap_mul_invSelf W i j i' j' k k'
  calc psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j') _ (lawTwoTriple W i' j' m))
      = psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j') _ (lawTwoTriple W i' j' m)) *
        (psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j) _ (lawOneTriple W i j k)) *
          psiFstCross W i j i' j' k k' (IsLocalization.Away.invSelf (lawOneTriple W i j k))) := by
        rw [hu, mul_one]
    _ = (psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j') _
      (lawTwoTriple W i' j' m)) *
          psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j) _ (lawOneTriple W i j k))) *
        psiFstCross W i j i' j' k k' (IsLocalization.Away.invSelf (lawOneTriple W i j k)) := by ring
    _ = _ := by rw [hmin]; ring


variable [IsJacobsonRing R]

lemma equation_psiFstCross_lawOneTriple [IsDomain (biChartRing W i j)] (hΔ : IsUnit W.Δ)
  (k k' : Fin 3) :
    (W.map (algebraMap R (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k'))))).toProjective.Equation
        (fun m => psiFstCross W i j i' j' k k' (algebraMap (biChartRing W i j)
          (Localization.Away (lawOneTriple W i j k)) (lawOneTriple W i j m))) := by
  rw [funext (psiFstCross_algebraMap_lawOneTriple W i j i' j' k k')]
  exact equation_mapTriple W (fun m => transAlgHom W i j i' j' (lawOneTriple W i j m))
    (equation_mapTriple_algHom W (transAlgHom W i j i' j') (lawOneTriple W i j)
      (equation_lawOneTriple_of_isDomain W i j hΔ))

lemma equation_psiSndCross_lawTwoTriple [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ)
  (k k' : Fin 3) :
    (W.map (algebraMap R (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
        transHom W i j i' j' (lawTwoTriple W i' j' k'))))).toProjective.Equation
        (fun m => psiSndCross W i j i' j' k k' (algebraMap (biChartRing W i' j')
          (Localization.Away (lawTwoTriple W i' j' k')) (lawTwoTriple W i' j' m))) := by
  rw [funext (fun m => psiSndCross_algebraMap W i j i' j' k k' (lawTwoTriple W i' j' m))]
  exact equation_mapTriple W (fun m => transHom W i j i' j' (lawTwoTriple W i' j' m))
    (equation_mapTriple_algHom W (transHom W i j i' j') (lawTwoTriple W i' j')
      (equation_lawTwoTriple_of_isDomain W i' j' hΔ))

/-- **(c3, L4 cross-chart-cross-law ψ-agreement)** Over S', the (i,j)-Z piece morphism and the
(i',j')-Y piece morphism agree after pullback along Spec(ψ). specMap_comp_pieceMorOfTriple both
sides +
the crux (via the smul e = t'_k · invSelf, from the transRing cross-minor). -/
lemma specMap_psiFstCross_addOnZPieceMor_cross [IsDomain (biChartRing W i j)]
    [IsDomain (biChartRing W i' j')] (hΔ : IsUnit W.Δ) (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom
      (psiFstCross W i j i' j' k k').toRingHom) ≫ addOnZPieceMor W i j k hΔ =
      Spec.map (CommRingCat.ofHom (psiSndCross W i j i' j' k k').toRingHom) ≫
        addOnYPieceMor W i' j' k' hΔ := by
  rw [addOnZPieceMor_eq, addOnYPieceMor_eq]
  exact (specMap_comp_pieceMorOfTriple W (lawOneTriple W i j)
      (equation_lawOneTriple_of_isDomain W i j hΔ) k (psiFstCross W i j i' j' k k')
      (psiFstCross_algebraMap_mul_invSelf W i j i' j' k k')
      (equation_psiFstCross_lawOneTriple W i j i' j' hΔ k k')).trans
    (((chartι_comp_specMap_chartAwayHom_smul_eq W k k' _ _ _ _ _
        (psiSndCross_eq_smul W i j i' j' k k')
        (psiFstCross_algebraMap_mul_invSelf W i j i' j' k k')
        (psiSndCross_algebraMap_mul_invSelf W i j i' j' k k')
        (equation_psiFstCross_lawOneTriple W i j i' j' hΔ k k')
        (equation_psiSndCross_lawTwoTriple W i j i' j' hΔ k k')).symm).trans
      (specMap_comp_pieceMorOfTriple W (lawTwoTriple W i' j')
        (equation_lawTwoTriple_of_isDomain W i' j' hΔ) k' (psiSndCross W i j i' j' k k')
        (psiSndCross_algebraMap_mul_invSelf W i j i' j' k k')
        (equation_psiSndCross_lawTwoTriple W i j i' j' hΔ k k')).symm)

lemma specMap_psiFstCross_pieceGenι (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiFstCross W i j i' j' k k').toRingHom) ≫
        pieceGenι W i j (lawOneTriple W i j k) =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [pieceGenι_eq, transι]
  exact spec_map_comp_congr _ _ _ _ _
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, psiFstCross_toRingHom_comp'])

lemma specMap_psiSndCross_pieceGenι (k k' : Fin 3) :
    Spec.map (CommRingCat.ofHom (psiSndCross W i j i' j' k k').toRingHom) ≫
        pieceGenι W i' j' (lawTwoTriple W i' j' k') =
      Spec.map (CommRingCat.ofHom (algebraMap (transRing W i j i' j')
        (Localization.Away (transAlgHom W i j i' j' (lawOneTriple W i j k) *
          transHom W i j i' j' (lawTwoTriple W i' j' k'))))) ≫ transι W i j i' j' := by
  rw [pieceGenι_eq, transι_eq]
  exact spec_map_comp_congr _ _ _ _ _
    (by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, psiSndCross_toRingHom_comp'])

lemma crossOverlapPieceIso_hom_ι_eq_specMap_psiFstCross (k k' : Fin 3) :
    (crossOverlapPieceIso W i j i' j' k k').hom ≫ (crossOverlapPiece W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (psiFstCross W i j i' j' k k').toRingHom) ≫
        pieceGenι W i j (lawOneTriple W i j k) :=
  (crossOverlapPieceIso_hom_ι W i j i' j' k k').trans
    (specMap_psiFstCross_pieceGenι W i j i' j' k k').symm

lemma crossOverlapPieceIso_hom_ι_eq_specMap_psiSndCross (k k' : Fin 3) :
    (crossOverlapPieceIso W i j i' j' k k').hom ≫ (crossOverlapPiece W i j i' j' k k').ι =
      Spec.map (CommRingCat.ofHom (psiSndCross W i j i' j' k k').toRingHom) ≫
        pieceGenι W i' j' (lawTwoTriple W i' j' k') :=
  (crossOverlapPieceIso_hom_ι W i j i' j' k k').trans
    (specMap_psiSndCross_pieceGenι W i j i' j' k k').symm


set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma crossW_homOfLE_sigma_psiFstCross (k k' : Fin 3) :
    (crossOverlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left : crossOverlapPiece W i j i' j' k k' ≤
          pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) ≫
      (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv =
    Spec.map (CommRingCat.ofHom (psiFstCross W i j i' j' k k').toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i j) (blOpenZPieceFamily W i j k)).inv ≫
      morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv ≫
      pieceGenι W i j (lawOneTriple W i j k) = (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k).ι := by
    simp only [blOpenZPieceFamily]
    rw [← isoImage_specBasicOpen_pieceGenι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceGenι W i j (lawOneTriple W i j k))]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact crossOverlapPieceIso_hom_ι_eq_specMap_psiFstCross W i j i' j' k k'

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
lemma crossW_homOfLE_sigma_psiSndCross (k k' : Fin 3) :
    (crossOverlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right : crossOverlapPiece W i j i' j' k k' ≤
          pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k') ≫
      (Scheme.Hom.isoImage (pieceι W i' j') (blOpenYPieceFamily W i' j' k')).inv ≫
      morphismRestrict (chartPieceIso W i' j').hom
        (specBasicOpen (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')).inv =
    Spec.map (CommRingCat.ofHom (psiSndCross W i j i' j' k k').toRingHom) := by
  have h6 : (Scheme.Hom.isoImage (pieceι W i' j') (blOpenYPieceFamily W i' j' k')).inv ≫
      morphismRestrict (chartPieceIso W i' j').hom
        (specBasicOpen (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i' j')) (lawTwoTriple W i' j' k')).inv ≫
      pieceGenι W i' j' (lawTwoTriple W i' j' k') =
      (pieceι W i' j' ''ᵁ blOpenYPieceFamily W i' j' k').ι := by
    simp only [blOpenYPieceFamily]
    rw [← isoImage_specBasicOpen_pieceGenι]; simp only [Category.assoc]
  rw [← cancel_mono (pieceGenι W i' j' (lawTwoTriple W i' j' k'))]; simp only [Category.assoc, h6]
  rw [Scheme.homOfLE_ι]; exact crossOverlapPieceIso_hom_ι_eq_specMap_psiSndCross W i j i' j' k k'


/-- The cross-chart-cross-law overlap decomposed into the (k,k') cross pieces. -/
lemma blOpenZImage_inf_blOpenYImage_eq_iSup_cross :
    blOpenZImage W i j ⊓ blOpenYImage W i' j' =
      ⨆ p : Fin 3 × Fin 3, crossOverlapPiece W i j i' j' p.1 p.2 := by
  rw [blOpenZImage_eq_iSup, blOpenYImage_eq_iSup, iSup_inf_iSup]

variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)] [IsDomain (biChartRing W i' j')]

/-- **(c3, per cross-piece agreement)** On the cross overlap piece, the (i,j)-Z and (i',j')-Y image
morphisms agree. cancel_epi crossOverlapPieceIso + L1 + σ-cancels + L4. -/
lemma crossOverlapPiece_addOn_agree (hΔ : IsUnit W.Δ) (k k' : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left.trans ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))) ≫
        addOnZOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right.trans ((pieceι W i' j').image_mono (le_iSup
          (blOpenYPieceFamily W i' j') k'))) ≫
        addOnYOnImage W hΔ i' j' := by
  have eZ : (crossOverlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left.trans ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k))) ≫
        addOnZOnImage W hΔ i j =
      Spec.map (CommRingCat.ofHom
        (psiFstCross W i j i' j' k k').toRingHom) ≫ addOnZPieceMor W i j k hΔ :=
    (congrArg ((crossOverlapPieceIso W i j i' j' k k').hom ≫ ·)
        (homOfLE_addOnZOnImage_eq W i j hΔ k
          (crossOverlapPiece W i j i' j' k k') inf_le_left)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnZPieceMor W i j k hΔ)
          (crossW_homOfLE_sigma_psiFstCross W i j i' j' k k')))
  have eY : (crossOverlapPieceIso W i j i' j' k k').hom ≫
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_right.trans ((pieceι W i' j').image_mono (le_iSup
          (blOpenYPieceFamily W i' j') k'))) ≫
        addOnYOnImage W hΔ i' j' =
      Spec.map (CommRingCat.ofHom (psiSndCross W i j i' j' k k').toRingHom) ≫
        addOnYPieceMor W i' j' k' hΔ :=
    (congrArg ((crossOverlapPieceIso W i j i' j' k k').hom ≫ ·)
        (homOfLE_addOnYOnImage_eq W i' j' hΔ k'
          (crossOverlapPiece W i j i' j' k k') inf_le_right)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ addOnYPieceMor W i' j' k' hΔ)
          (crossW_homOfLE_sigma_psiSndCross W i j i' j' k k')))
  exact (cancel_epi (crossOverlapPieceIso W i j i' j' k k').hom).mp
    (eZ.trans ((specMap_psiFstCross_addOnZPieceMor_cross W i j i' j' hΔ k k').trans eY.symm))

/-- **(c3, cross-chart-cross-law addOn_agree)** addOnZOnImage(i,j) = addOnYOnImage(i',j') on their
overlap. Cover.hom_ext over the cross-piece cover → crossOverlapPiece_addOn_agree. -/
lemma addOnZOnImage_eq_addOnYOnImage_cross (hΔ : IsUnit W.Δ)
    (Ω : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hk : Ω ≤ blOpenZImage W i j) (hl : Ω ≤ blOpenYImage W i' j')
    (hΩ : Ω = ⨆ p : Fin 3 × Fin 3, crossOverlapPiece W i j i' j' p.1 p.2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnZOnImage W hΔ i j =
      (pullback (projModelπ W) (projModelπ W)).homOfLE hl ≫ addOnYOnImage W hΔ i' j' := by
  subst hΩ
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun p : Fin 3 × Fin 3 => crossOverlapPiece W i j i' j' p.1 p.2)) _ _ (fun p => ?_)
  have hf : (Scheme.Opens.iSupOpenCover
      (fun p : Fin 3 × Fin 3 => crossOverlapPiece W i j i' j' p.1 p.2)).f p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun p : Fin 3 × Fin 3 => crossOverlapPiece W i j i' j' p.1 p.2) p) := rfl
  rw [hf]
  exact (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ p) hk (addOnZOnImage W hΔ i j)).trans
    ((crossOverlapPiece_addOn_agree W i j i' j' hΔ p.1 p.2).trans
      (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ p) hl (addOnYOnImage W hΔ i' j')).symm)

end OverlapCrossChart

section FamilyAssembly

variable [IsDomain R] [IsJacobsonRing R] (hΔ : IsUnit W.Δ)

/-- **(c3, glueMorphisms restriction — Z)** `addOnZ` restricted to the `p`-th chart-product image is
`addOnZFamily p`: `homOfLE (blOpenZFamily p ≤ blOpenZ) ≫ addOnZ = addOnZFamily p`. Immediate from
`Scheme.Cover.ι_glueMorphisms` on the four-chart cover `addOnZ` glues over. -/
lemma homOfLE_le_addOnZ (p : Fin 2 × Fin 2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenZFamily W) p) ≫ addOnZ W hΔ =
      addOnZFamily W hΔ p := by
  rw [addOnZ]
  exact Scheme.Cover.ι_glueMorphisms (Scheme.Opens.iSupOpenCover (blOpenZFamily W))
    (addOnZFamily W hΔ) _ p

/-- **(c3, glueMorphisms restriction — Y)** `addOnY` restricted to the `q`-th chart-product image is
`addOnYFamily q`. Mirror of `homOfLE_le_addOnZ`. -/
lemma homOfLE_le_addOnY (q : Fin 2 × Fin 2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenYFamily W) q) ≫ addOnY W hΔ =
      addOnYFamily W hΔ q := by
  rw [addOnY]
  exact Scheme.Cover.ι_glueMorphisms (Scheme.Opens.iSupOpenCover (blOpenYFamily W))
    (addOnYFamily W hΔ) _ q

/-- **(c3, the pairwise cross-law family agreement)** On `blOpenZFamily p ⊓ blOpenYFamily q` the
`p`-th
law-1 (Z) morphism and the `q`-th law-2 (Y) morphism agree. The 16 `fin_cases` each discharge to
`addOnZOnImage_eq_addOnYOnImage_cross` — the cross-chart-cross-law image agreement, which subsumes
the
same-chart diagonal (`transRing` degenerates to `biChartRing` there, so the cross apparatus applies
uniformly). This is the two-law analogue of `addOnZFamily_agree`/`addOnYFamily_agree`. -/
lemma addOnZFamily_eq_addOnYFamily (p q : Fin 2 × Fin 2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left : blOpenZFamily W p ⊓ blOpenYFamily W q ≤ blOpenZFamily W p) ≫
        addOnZFamily W hΔ p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ addOnYFamily W hΔ q := by
  obtain ⟨p1, p2⟩ := p; obtain ⟨q1, q2⟩ := q
  fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
    exact addOnZOnImage_eq_addOnYOnImage_cross W _ _ _ _ hΔ _ inf_le_left inf_le_right
      (blOpenZImage_inf_blOpenYImage_eq_iSup_cross W _ _ _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- **(c3, addOn_agree — THE two-law agreement)** The two Bosma–Lenstra addition morphisms — law 1
(`addOnZ`, regular on `blOpenZ`) and law 2 (`addOnY`, regular on `blOpenY`) — agree on the overlap
`blOpenZ ⊓ blOpenY` of their regularity opens. `Scheme.Cover.hom_ext` over the `(p,q)` family
refinement `⨆ blOpenZFamily p ⊓ blOpenYFamily q`; each cover piece reduces via the glueMorphisms
restrictions `homOfLE_le_addOnZ/Y` to the pairwise family agreement `addOnZFamily_eq_addOnYFamily`.
This is the compatibility `mulModelHom`'s two-open (`blOpenZ ⊔ blOpenY = ⊤`) glue consumes. -/
lemma addOn_agree (Ω : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hk : Ω ≤ blOpenZ W) (hl : Ω ≤ blOpenY W)
    (hΩ : Ω = ⨆ pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
      blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnZ W hΔ =
      (pullback (projModelπ W) (projModelπ W)).homOfLE hl ≫ addOnY W hΔ := by
  subst hΩ
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
      blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2)) _ _ (fun pq => ?_)
  have hf : (Scheme.Opens.iSupOpenCover
      (fun pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
        blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2)).f pq =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
          blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2) pq) := rfl
  have eZ : (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
          blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2) pq) ≫
        (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnZ W hΔ =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_left ≫ addOnZFamily W hΔ pq.1 := by
    rw [Scheme.homOfLE_homOfLE_assoc, ← homOfLE_le_addOnZ W hΔ pq.1, Scheme.homOfLE_homOfLE_assoc]
    rfl
  have eY : (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2) =>
          blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2) pq) ≫
        (pullback (projModelπ W) (projModelπ W)).homOfLE hl ≫ addOnY W hΔ =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ addOnYFamily W hΔ pq.2 := by
    rw [Scheme.homOfLE_homOfLE_assoc, ← homOfLE_le_addOnY W hΔ pq.2, Scheme.homOfLE_homOfLE_assoc]
    rfl
  rw [hf]
  exact eZ.trans ((addOnZFamily_eq_addOnYFamily W hΔ pq.1 pq.2).trans eY.symm)

end FamilyAssembly

section CoverAssembly

variable (i j : Fin 3)

/-- **(c2, the two laws cover the chart-product scheme)** The Z-law and Y-law regularity pieces
cover the whole `(i,j)` chart-product `Spec biChartRing`. Each piece family is a `chartPieceIso`
preimage of a `specBasicOpen`, so the `⊔` is `chartPieceIso.hom ⁻¹ᵁ` of the joint regularity open,
which is `⊤` by the joint-unit-ideal `span_lawOneTriple_union_lawTwoTriple_eq_top` (via
`regularityOpen_sup_eq_top_iff`). -/
lemma blOpenZPieceSup_sup_blOpenYPieceSup_eq_top (hΔ : IsUnit W.Δ) :
    (⨆ k, blOpenZPieceFamily W i j k) ⊔ (⨆ k, blOpenYPieceFamily W i j k) = ⊤ := by
  have hZ : (⨆ k, blOpenZPieceFamily W i j k) = (chartPieceIso W i j).hom ⁻¹ᵁ
      (⨆ k, specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) :=
    ((chartPieceIso W i j).hom.preimage_iSup _).symm
  have hY : (⨆ k, blOpenYPieceFamily W i j k) = (chartPieceIso W i j).hom ⁻¹ᵁ
      (⨆ k, specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) :=
    ((chartPieceIso W i j).hom.preimage_iSup _).symm
  rw [hZ, hY, ← Scheme.Hom.preimage_sup,
    show (⨆ k, specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ⊔
        (⨆ k, specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) = ⊤ from
      (regularityOpen_sup_eq_top_iff _ _).mpr
        (span_lawOneTriple_union_lawTwoTriple_eq_top W i j hΔ),
    Scheme.Hom.preimage_top]

/-- **(c2, per-chart cover)** On each `(i,j)` chart-product image the two Bosma–Lenstra laws'
regularity opens cover the whole chart image `range pieceι`. `image` distributes over `⊔`
(`Set.image_union`) and the pieces cover the source (`blOpenZPieceSup_sup_blOpenYPieceSup_eq_top`),
so the image of `⊤` is `opensRange`. -/
lemma blOpenZImage_sup_blOpenYImage_eq_opensRange (hΔ : IsUnit W.Δ) :
    blOpenZImage W i j ⊔ blOpenYImage W i j = (pieceι W i j).opensRange := by
  have himg : ∀ A B : (Limits.pullback (chartι W i ≫ projModelπ W)
      (chartι W j ≫ projModelπ W)).Opens,
      pieceι W i j ''ᵁ A ⊔ pieceι W i j ''ᵁ B = pieceι W i j ''ᵁ (A ⊔ B) := fun A B =>
    TopologicalSpace.Opens.ext (by
      simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_sup, Set.image_union])
  rw [blOpenZImage, blOpenYImage, himg, blOpenZPieceSup_sup_blOpenYPieceSup_eq_top W i j hΔ,
    Scheme.Hom.image_top_eq_opensRange]

end CoverAssembly

/-- **(T-W7.0c·c2 [C2-BEZOUT], THE COVER — the two Bosma–Lenstra laws cover `E ×_R E`)** The
regularity opens of the two laws cover the whole product, over any base with `Δ` a unit. This is the
compatibility `mulModelHom`'s two-open glue needs (`blOpen_cover`). The four chart-products cover
`E ×_R E` (`chartY_sup_chartZ_eq_top` on each factor, `pieceι_opensRange` = `fst⁻¹chart ⊓
snd⁻¹chart`,
frame distributivity), and on each the two laws cover the chart image
(`blOpenZImage_sup_blOpenYImage_eq_opensRange`). **No Bezout certificate**: the whole cover rests on
the point-level non-vanishing `addXYZ_ne_zero_or_dblAddXYZ_ne_zero`. -/
theorem blOpenZ_sup_blOpenY_eq_top (hΔ : IsUnit W.Δ) : blOpenZ W ⊔ blOpenY W = ⊤ := by
  rw [eq_top_iff]
  have hle : ∀ i j : Fin 3, blOpenZImage W i j ≤ blOpenZ W → blOpenYImage W i j ≤ blOpenY W →
      (pieceι W i j).opensRange ≤ blOpenZ W ⊔ blOpenY W := fun i j hZ hY => by
    rw [← blOpenZImage_sup_blOpenYImage_eq_opensRange W i j hΔ]
    exact sup_le_sup hZ hY
  have hcov : (chartι W 1).opensRange ⊔ (chartι W 2).opensRange = ⊤ := chartY_sup_chartZ_eq_top W
  calc (⊤ : (pullback (projModelπ W) (projModelπ W)).Opens)
      = pullback.fst (projModelπ W) (projModelπ W) ⁻¹ᵁ
            ((chartι W 1).opensRange ⊔ (chartι W 2).opensRange) ⊓
          pullback.snd (projModelπ W) (projModelπ W) ⁻¹ᵁ
            ((chartι W 1).opensRange ⊔ (chartι W 2).opensRange) := by
        rw [hcov]; simp
    _ ≤ blOpenZ W ⊔ blOpenY W := by
        rw [Scheme.Hom.preimage_sup, Scheme.Hom.preimage_sup, inf_sup_left, inf_sup_right,
          inf_sup_right]
        refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
        · rw [← pieceι_opensRange]
          exact hle 1 1 (le_iSup (blOpenZFamily W) (0, 0)) (le_iSup (blOpenYFamily W) (0, 0))
        · rw [← pieceι_opensRange]
          exact hle 2 1 (le_iSup (blOpenZFamily W) (1, 0)) (le_iSup (blOpenYFamily W) (1, 0))
        · rw [← pieceι_opensRange]
          exact hle 1 2 (le_iSup (blOpenZFamily W) (0, 1)) (le_iSup (blOpenYFamily W) (0, 1))
        · rw [← pieceι_opensRange]
          exact hle 2 2 (le_iSup (blOpenZFamily W) (1, 1)) (le_iSup (blOpenYFamily W) (1, 1))

section MulModel

variable [IsDomain R] [IsJacobsonRing R]

/-- The two-open cover `{blOpenZ, blOpenY}` of `E ×_R E`, as a `Bool`-indexed family. -/
noncomputable def blCoverFam : Bool → (pullback (projModelπ W) (projModelπ W)).Opens :=
  fun b => cond b (blOpenZ W) (blOpenY W)

/-- The two Bosma–Lenstra addition morphisms, indexed to match `blCoverFam`. -/
noncomputable def blCoverMor (hΔ : IsUnit W.Δ) :
    ∀ b, (blCoverFam W b).toScheme ⟶ projModel W
  | true => addOnZ W hΔ
  | false => addOnY W hΔ

/-- The two laws agree pairwise on the two-open cover — the `hf` obligation. The off-diagonal
`Bool` cases are `addOn_agree` (and its symmetry), with `Ω = blOpenZ ⊓ blOpenY` decomposed by
`iSup_inf_iSup`; the diagonal cases are `rfl`. -/
lemma blCoverMor_agree (hΔ : IsUnit W.Δ) (k l : Bool) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (inf_le_left : blCoverFam W k ⊓ blCoverFam W l ≤ blCoverFam W k) ≫ blCoverMor W hΔ k =
      (pullback (projModelπ W) (projModelπ W)).homOfLE inf_le_right ≫ blCoverMor W hΔ l := by
  have hΩ : blOpenZ W ⊓ blOpenY W = ⨆ pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
      blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2 := by
    rw [blOpenZ, blOpenY, iSup_inf_iSup]
  have hΩ' : blOpenY W ⊓ blOpenZ W = ⨆ pq : (Fin 2 × Fin 2) × (Fin 2 × Fin 2),
      blOpenZFamily W pq.1 ⊓ blOpenYFamily W pq.2 := by
    rw [inf_comm, blOpenZ, blOpenY, iSup_inf_iSup]
  cases k <;> cases l
  · rfl
  · exact (addOn_agree W hΔ _ inf_le_right inf_le_left hΩ').symm
  · exact addOn_agree W hΔ _ inf_le_left inf_le_right hΩ
  · rfl

/-- The two-open cover is everything: `⨆ blCoverFam = blOpenZ ⊔ blOpenY = ⊤`. -/
lemma iSup_blCoverFam_eq_top (hΔ : IsUnit W.Δ) : ⨆ b, blCoverFam W b = ⊤ := by
  rw [iSup_bool_eq]
  show blOpenZ W ⊔ blOpenY W = ⊤
  exact blOpenZ_sup_blOpenY_eq_top W hΔ

/-- **(T-W7.0c·c4, THE multiplication morphism over a Jacobson domain)** The addition morphism on
the projective Weierstrass model `E ×_R E ⟶ E`, glued from the two Bosma–Lenstra laws on the
two-open cover `blOpenZ ⊔ blOpenY = ⊤` (`glueMorphisms` + the top iso). Both `addOnZ`/`addOnY` and
their agreement `addOn_agree` are consumed here. Over the universal atlas `ℤ[a₁..a₆][Δ⁻¹]`
(a Jacobson domain) this is the source that base-change transports to every ring (c4.5). -/
noncomputable def mulModelHom (hΔ : IsUnit W.Δ) :
    pullback (projModelπ W) (projModelπ W) ⟶ projModel W :=
  (pullback (projModelπ W) (projModelπ W)).topIso.inv ≫
    (pullback (projModelπ W) (projModelπ W)).homOfLE (iSup_blCoverFam_eq_top W hΔ).ge ≫
    (Scheme.Opens.iSupOpenCover (blCoverFam W)).glueMorphisms (blCoverMor W hΔ)
      (glueMorphisms_hf_of_agree (blCoverFam W) (blCoverMor W hΔ) (blCoverMor_agree W hΔ))

set_option backward.isDefEq.respectTransparency.types false in
/-- `blOpenZ.ι ≫ topIso.inv ≫ homOfLE` collapses to the cover inclusion of the `blOpenZ` piece. -/
@[reassoc]
lemma ι_topIso_inv_homOfLE_true (hΔ : IsUnit W.Δ) :
    (blOpenZ W).ι ≫ (pullback (projModelπ W) (projModelπ W)).topIso.inv ≫
        (pullback (projModelπ W) (projModelπ W)).homOfLE (iSup_blCoverFam_eq_top W hΔ).ge =
      (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blCoverFam W) true) := by
  have h2 : (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blCoverFam W) true) ≫
      (⨆ b, blCoverFam W b).ι = (blOpenZ W).ι := Scheme.homOfLE_ι _ _
  rw [← cancel_mono (⨆ b, blCoverFam W b).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
    Scheme.toIso_inv_ι, Category.comp_id]
  exact h2.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- `blOpenY.ι ≫ topIso.inv ≫ homOfLE` collapses to the cover inclusion of the `blOpenY` piece. -/
@[reassoc]
lemma ι_topIso_inv_homOfLE_false (hΔ : IsUnit W.Δ) :
    (blOpenY W).ι ≫ (pullback (projModelπ W) (projModelπ W)).topIso.inv ≫
        (pullback (projModelπ W) (projModelπ W)).homOfLE (iSup_blCoverFam_eq_top W hΔ).ge =
      (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blCoverFam W) false) := by
  have h2 : (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blCoverFam W) false) ≫
      (⨆ b, blCoverFam W b).ι = (blOpenY W).ι := Scheme.homOfLE_ι _ _
  rw [← cancel_mono (⨆ b, blCoverFam W b).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
    Scheme.toIso_inv_ι, Category.comp_id]
  exact h2.symm

/-- **(T-W7.0c·c4-Z-spec)** `mulModelHom` restricts to the `Z`-law on `blOpenZ`. -/
theorem blOpenZ_ι_mulModelHom (hΔ : IsUnit W.Δ) :
    (blOpenZ W).ι ≫ mulModelHom W hΔ = addOnZ W hΔ := by
  rw [mulModelHom, ι_topIso_inv_homOfLE_true_assoc W hΔ]
  exact (Scheme.Opens.iSupOpenCover (blCoverFam W)).ι_glueMorphisms _ _ true

/-- **(T-W7.0c·c4-Y-spec)** `mulModelHom` restricts to the `Y`-law on `blOpenY`. -/
theorem blOpenY_ι_mulModelHom (hΔ : IsUnit W.Δ) :
    (blOpenY W).ι ≫ mulModelHom W hΔ = addOnY W hΔ := by
  rw [mulModelHom, ι_topIso_inv_homOfLE_false_assoc W hΔ]
  exact (Scheme.Opens.iSupOpenCover (blCoverFam W)).ι_glueMorphisms _ _ false

end MulModel

/-! ## π-compatibility: the two-law glue is over `Spec R` (c4.5 first act) -/

section

variable (i j : Fin 3)
variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)]

set_option backward.isDefEq.respectTransparency.types false in
/-- Per-piece: the k-th image piece of addOnYOnImage is over R, matching the piece's fst-structure.
-/
lemma addOnYOnImage_piece_projModelπ (hΔ : IsUnit W.Δ) (k : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((pieceι W i j).image_mono (le_iSup (blOpenYPieceFamily W i j) k)) ≫
        addOnYOnImage W hΔ i j ≫ projModelπ W =
      (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, addOnYOnImage_piece, addOnYOnFamily]
  simp only [Category.assoc]
  rw [addOnYPieceMor_projModelπ, ← isoImage_specBasicOpen_pieceAwayι]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
    (pieceAwayι_fst_projModelπ W i j k).symm))
end

section

variable (i j : Fin 3)

/-- Z-side base case: the k-th law-1 piece embeds as an R-scheme. -/
lemma pieceAwayZι_fst_projModelπ (k : Fin 3) :
    pieceAwayZι W i j k ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away (lawOneTriple W i j k)))) := by
  rw [pieceAwayZι_eq]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [pieceι_fst]
  slice_lhs 4 5 => rw [chartι_projModelπ]
  slice_lhs 2 3 => rw [chartPieceIso_inv_fst]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  show (algebraMap (biChartRing W i j) (Localization.Away (lawOneTriple W i j k)))
      ((biChartRingAwayTensorEquiv W i j).symm
        (algebraMap R (TensorProduct R (chartAway W i) (chartAway W j)) r)) =
    algebraMap R (Localization.Away (lawOneTriple W i j k)) r
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
end

section

variable (i j : Fin 3)
variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)]

set_option backward.isDefEq.respectTransparency.types false in
/-- Z-side per-piece π-compat. -/
lemma addOnZOnImage_piece_projModelπ (hΔ : IsUnit W.Δ) (k : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        ((pieceι W i j).image_mono (le_iSup (blOpenZPieceFamily W i j) k)) ≫
        addOnZOnImage W hΔ i j ≫ projModelπ W =
      (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, addOnZOnImage_piece, addOnZOnFamily]
  simp only [Category.assoc]
  rw [addOnZPieceMor_projModelπ, ← isoImage_specBasicOpen_pieceAwayZι]
  simp only [Category.assoc]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
    (pieceAwayZι_fst_projModelπ W i j k).symm))
end

section

variable (i j : Fin 3)
variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)]

omit [IsJacobsonRing R] [IsDomain (biChartRing W i j)] in
/-- homOfLE into the piece-⨆ composed with ι-fst-π collapses to the piece's ι-fst-π. -/
lemma homOfLE_iSup_pieceImage_ι_fst_projModelπ (k : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun k => pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) k) ≫
        (⨆ k, pieceι W i j ''ᵁ blOpenYPieceFamily W i j k).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      (pieceι W i j ''ᵁ blOpenYPieceFamily W i j k).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- Ω-form π-compat for addOnYOnImage: over the piece cover, the law-2 image morphism is over R. -/
lemma homOfLE_addOnYOnImage_projModelπ (hΔ : IsUnit W.Δ)
    (Ω : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hk : Ω ≤ blOpenYImage W i j)
    (hΩ : Ω = ⨆ k, pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnYOnImage W hΔ i j ≫ projModelπ W =
      Ω.ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  subst hΩ
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun k => pieceι W i j ''ᵁ blOpenYPieceFamily W i j k)) _ _ (fun k => ?_)
  have hf : (Scheme.Opens.iSupOpenCover
      (fun k => pieceι W i j ''ᵁ blOpenYPieceFamily W i j k)).f k =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun k => pieceι W i j ''ᵁ blOpenYPieceFamily W i j k) k) := rfl
  rw [hf]
  exact (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ k) hk
      (addOnYOnImage W hΔ i j ≫ projModelπ W)).trans
    ((addOnYOnImage_piece_projModelπ W i j hΔ k).trans
      (homOfLE_iSup_pieceImage_ι_fst_projModelπ W i j k).symm)
end

section

variable (i j : Fin 3)

/-- Z-mirror of the hoisted collapse lemma. -/
lemma homOfLE_iSup_pieceImageZ_ι_fst_projModelπ (k : Fin 3) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun k => pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) k) ≫
        (⨆ k, pieceι W i j ''ᵁ blOpenZPieceFamily W i j k).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      (pieceι W i j ''ᵁ blOpenZPieceFamily W i j k).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable [IsJacobsonRing R] [IsDomain (biChartRing W i j)]

/-- Z-side Ω-form π-compat. -/
lemma homOfLE_addOnZOnImage_projModelπ (hΔ : IsUnit W.Δ)
    (Ω : (pullback (projModelπ W) (projModelπ W)).Opens)
    (hk : Ω ≤ blOpenZImage W i j)
    (hΩ : Ω = ⨆ k, pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE hk ≫ addOnZOnImage W hΔ i j ≫ projModelπ W =
      Ω.ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  subst hΩ
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun k => pieceι W i j ''ᵁ blOpenZPieceFamily W i j k)) _ _ (fun k => ?_)
  have hf : (Scheme.Opens.iSupOpenCover
      (fun k => pieceι W i j ''ᵁ blOpenZPieceFamily W i j k)).f k =
      (pullback (projModelπ W) (projModelπ W)).homOfLE
        (le_iSup (fun k => pieceι W i j ''ᵁ blOpenZPieceFamily W i j k) k) := rfl
  rw [hf]
  exact (Scheme.homOfLE_homOfLE_assoc _ (le_iSup _ k) hk
      (addOnZOnImage W hΔ i j ≫ projModelπ W)).trans
    ((addOnZOnImage_piece_projModelπ W i j hΔ k).trans
      (homOfLE_iSup_pieceImageZ_ι_fst_projModelπ W i j k).symm)
end

section

variable [IsDomain R] [IsJacobsonRing R]

omit [IsDomain R] in
/-- Bare OnImage π-compat, Y-side (Ω := blOpenYImage itself via homOfLE_rfl + id_comp). -/
lemma addOnYOnImage_projModelπ (hΔ : IsUnit W.Δ) (i j : Fin 3) [IsDomain (biChartRing W i j)] :
    addOnYOnImage W hΔ i j ≫ projModelπ W =
      (blOpenYImage W i j).ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W :=
  (Category.id_comp _).symm.trans
    ((congrArg (· ≫ addOnYOnImage W hΔ i j ≫ projModelπ W)
      (Scheme.homOfLE_rfl _ _)).symm.trans
    (homOfLE_addOnYOnImage_projModelπ W i j hΔ _ le_rfl (blOpenYImage_eq_iSup W i j)))

omit [IsDomain R] in
/-- Bare OnImage π-compat, Z-side. -/
lemma addOnZOnImage_projModelπ (hΔ : IsUnit W.Δ) (i j : Fin 3) [IsDomain (biChartRing W i j)] :
    addOnZOnImage W hΔ i j ≫ projModelπ W =
      (blOpenZImage W i j).ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W :=
  (Category.id_comp _).symm.trans
    ((congrArg (· ≫ addOnZOnImage W hΔ i j ≫ projModelπ W)
      (Scheme.homOfLE_rfl _ _)).symm.trans
    (homOfLE_addOnZOnImage_projModelπ W i j hΔ _ le_rfl (blOpenZImage_eq_iSup W i j)))

/-- Family-level π-compat, Z-side: 4 fin_cases to the bare OnImage form. -/
lemma addOnZFamily_projModelπ (hΔ : IsUnit W.Δ) (p : Fin 2 × Fin 2) :
    addOnZFamily W hΔ p ≫ projModelπ W =
      (blOpenZFamily W p).ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  obtain ⟨p1, p2⟩ := p
  fin_cases p1 <;> fin_cases p2 <;> exact addOnZOnImage_projModelπ W hΔ _ _

/-- Family-level π-compat, Y-side. -/
lemma addOnYFamily_projModelπ (hΔ : IsUnit W.Δ) (p : Fin 2 × Fin 2) :
    addOnYFamily W hΔ p ≫ projModelπ W =
      (blOpenYFamily W p).ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  obtain ⟨p1, p2⟩ := p
  fin_cases p1 <;> fin_cases p2 <;> exact addOnYOnImage_projModelπ W hΔ _ _
end

section


/-- Family-sup ι-collapse, Z-side (no instance baggage). -/
lemma homOfLE_iSup_blOpenZFamily_ι_fst_projModelπ (p : Fin 2 × Fin 2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenZFamily W) p) ≫
        (⨆ p, blOpenZFamily W p).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      (blOpenZFamily W p).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

/-- Family-sup ι-collapse, Y-side. -/
lemma homOfLE_iSup_blOpenYFamily_ι_fst_projModelπ (p : Fin 2 × Fin 2) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenYFamily W) p) ≫
        (⨆ p, blOpenYFamily W p).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      (blOpenYFamily W p).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable [IsDomain R] [IsJacobsonRing R]

/-- **(π-compat, Z-law)** `addOnZ` is a morphism over `Spec R`. -/
lemma addOnZ_projModelπ (hΔ : IsUnit W.Δ) :
    addOnZ W hΔ ≫ projModelπ W =
      (blOpenZ W).ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover (blOpenZFamily W)) _ _ (fun p => ?_)
  have hf : (Scheme.Opens.iSupOpenCover (blOpenZFamily W)).f p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenZFamily W) p) := rfl
  rw [hf]
  exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ projModelπ W) (homOfLE_le_addOnZ W hΔ p)).trans
        (addOnZFamily_projModelπ W hΔ p))).trans
    (homOfLE_iSup_blOpenZFamily_ι_fst_projModelπ W p).symm

/-- **(π-compat, Y-law)** `addOnY` is a morphism over `Spec R`. -/
lemma addOnY_projModelπ (hΔ : IsUnit W.Δ) :
    addOnY W hΔ ≫ projModelπ W =
      (blOpenY W).ι ≫ pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover (blOpenYFamily W)) _ _ (fun p => ?_)
  have hf : (Scheme.Opens.iSupOpenCover (blOpenYFamily W)).f p =
      (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenYFamily W) p) := rfl
  rw [hf]
  exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ projModelπ W) (homOfLE_le_addOnY W hΔ p)).trans
        (addOnYFamily_projModelπ W hΔ p))).trans
    (homOfLE_iSup_blOpenYFamily_ι_fst_projModelπ W p).symm
end

section


/-- blCover-sup ι-collapse. -/
lemma homOfLE_iSup_blCoverFam_ι_fst_projModelπ [IsDomain R] [IsJacobsonRing R] (b : Bool) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blCoverFam W) b) ≫
        (⨆ b, blCoverFam W b).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      (blCoverFam W b).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

variable [IsDomain R] [IsJacobsonRing R]

/-- Glue-level π-compat: the glued two-law morphism is over R on the ⨆ of the two-open cover. -/
lemma glueMorphisms_blCover_projModelπ (hΔ : IsUnit W.Δ) :
    (Scheme.Opens.iSupOpenCover (blCoverFam W)).glueMorphisms (blCoverMor W hΔ)
        (glueMorphisms_hf_of_agree (blCoverFam W) (blCoverMor W hΔ) (blCoverMor_agree W hΔ)) ≫
        projModelπ W =
      (⨆ b, blCoverFam W b).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover (blCoverFam W)) _ _ (fun b => ?_)
  have hf : (Scheme.Opens.iSupOpenCover (blCoverFam W)).f b =
      (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blCoverFam W) b) := rfl
  have hglue : (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blCoverFam W) b) ≫
      (Scheme.Opens.iSupOpenCover (blCoverFam W)).glueMorphisms (blCoverMor W hΔ)
        (glueMorphisms_hf_of_agree (blCoverFam W) (blCoverMor W hΔ) (blCoverMor_agree W hΔ)) =
      blCoverMor W hΔ b :=
    Scheme.Cover.ι_glueMorphisms (Scheme.Opens.iSupOpenCover (blCoverFam W)) (blCoverMor W hΔ) _ b
  rw [hf]
  refine ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ projModelπ W) hglue).trans ?_)).trans
    (homOfLE_iSup_blCoverFam_ι_fst_projModelπ W b).symm
  cases b
  · exact addOnY_projModelπ W hΔ
  · exact addOnZ_projModelπ W hΔ

/-- Collapse: homOfLE(⊤≤⨆) ≫ ⨆.ι ≫ fst ≫ π = ⊤.ι ≫ fst ≫ π. -/
lemma homOfLE_top_blCover_ι_fst_projModelπ (hΔ : IsUnit W.Δ) :
    (pullback (projModelπ W) (projModelπ W)).homOfLE (iSup_blCoverFam_eq_top W hΔ).ge ≫
        (⨆ b, blCoverFam W b).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      (⊤ : (pullback (projModelπ W) (projModelπ W)).Opens).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

omit [IsDomain R] [IsJacobsonRing R] in
/-- Collapse: topIso.inv ≫ ⊤.ι ≫ fst ≫ π = fst ≫ π. -/
lemma topIso_inv_top_ι_fst_projModelπ :
    (pullback (projModelπ W) (projModelπ W)).topIso.inv ≫
        (⊤ : (pullback (projModelπ W) (projModelπ W)).Opens).ι ≫
        pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]

/-- **(T-W7.0d over the domain setting)** `mulModelHom` is a morphism over `Spec R`:
`mulModelHom ≫ projModelπ = pullback.fst ≫ projModelπ`. The π-compat of the whole two-law glue —
propagated from the piece level (`pieceAwayι_fst_projModelπ`) through every glue stage. This is the
agreement leg the c4.5 base-change `pullback.lift` needs. -/
theorem mulModelHom_projModelπ (hΔ : IsUnit W.Δ) :
    mulModelHom W hΔ ≫ projModelπ W =
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W := by
  rw [mulModelHom]
  simp only [Category.assoc]
  rw [glueMorphisms_blCover_projModelπ W hΔ]
  exact (congrArg ((pullback (projModelπ W) (projModelπ W)).topIso.inv ≫ ·)
    (homOfLE_top_blCover_ι_fst_projModelπ W hΔ)).trans (topIso_inv_top_ι_fst_projModelπ W)
end

end WeierstrassCurve.Projective
