import ModularCurves.EllipticCurve.AdditionChartOpen
import ModularCurves.EllipticCurve.AdditionChartTransition

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

namespace WeierstrassCurve.Projective

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

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

end Overlap

end WeierstrassCurve.Projective
