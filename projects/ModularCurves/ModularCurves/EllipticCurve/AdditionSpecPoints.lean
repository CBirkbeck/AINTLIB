/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.GroupLawConstruction
import ModularCurves.ForMathlib.UniquePointFactorsISup

/-!
# Field-points of the two-law multiplication (T-W7.0c·c6, [C6-SPECPOINTS])

The evaluation layer for `mulModelHom_specPoints`: a field-valued point of `E ×_R E` factors
through one of the two regularity opens (`blOpen_cover` + the unique point of `Spec K`), where
the multiplication restricts to the corresponding Bosma–Lenstra law.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
open scoped TensorProduct

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- [C6-a] A field-valued point of `E ×_R E` factors through `blOpenZ` or `blOpenY`. -/
theorem SpecPoint.factors_blOpen (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K]
    (g : Spec (CommRingCat.of K) ⟶ pullback (projModelπ W) (projModelπ W)) :
    (∃ h, h ≫ (blOpenZ W).ι = g) ∨ (∃ h, h ≫ (blOpenY W).ι = g) := by
  have hmem : g.base default ∈ blOpenZ W ⊔ blOpenY W := by
    rw [blOpen_cover]
    trivial
  have hrange : Set.range g.base = {g.base default} := Set.range_unique
  rcases (TopologicalSpace.Opens.mem_sup).mp hmem with hx | hx
  · refine Or.inl ⟨IsOpenImmersion.lift (blOpenZ W).ι g ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rw [Scheme.Opens.range_ι, hrange]
    exact Set.singleton_subset_iff.mpr hx
  · refine Or.inr ⟨IsOpenImmersion.lift (blOpenY W).ι g ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rw [Scheme.Opens.range_ι, hrange]
    exact Set.singleton_subset_iff.mpr hx

section Descent

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) [IsDomain R] [IsJacobsonRing R]

/-- [C6-d1a, Z] Family-level descent: a field point through `addOnZ` evaluates through some
chart-product family member. -/
theorem SpecPoint.addOnZ_family (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (WeierstrassCurve.Projective.blOpenZ W).toScheme) :
    ∃ (p : Fin 2 × Fin 2) (h₁ : Spec (CommRingCat.of K) ⟶ (blOpenZFamily W p).toScheme),
      h₁ ≫ (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenZFamily W) p) = h ∧
      h ≫ WeierstrassCurve.Projective.addOnZ W hΔ = h₁ ≫ addOnZFamily W hΔ p := by
  obtain ⟨p, h₁, hh₁⟩ := exists_lift_iSup_of_unique (blOpenZFamily W) h
  exact ⟨p, h₁, hh₁, (congrArg (· ≫ WeierstrassCurve.Projective.addOnZ W hΔ) hh₁.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (homOfLE_le_addOnZ W hΔ p)))⟩

/-- [C6-d1a, Y] Family-level descent: a field point through `addOnY` evaluates through some
chart-product family member. -/
theorem SpecPoint.addOnY_family (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (WeierstrassCurve.Projective.blOpenY W).toScheme) :
    ∃ (p : Fin 2 × Fin 2) (h₁ : Spec (CommRingCat.of K) ⟶ (blOpenYFamily W p).toScheme),
      h₁ ≫ (pullback (projModelπ W) (projModelπ W)).homOfLE (le_iSup (blOpenYFamily W) p) = h ∧
      h ≫ WeierstrassCurve.Projective.addOnY W hΔ = h₁ ≫ addOnYFamily W hΔ p := by
  obtain ⟨p, h₁, hh₁⟩ := exists_lift_iSup_of_unique (blOpenYFamily W) h
  exact ⟨p, h₁, hh₁, (congrArg (· ≫ WeierstrassCurve.Projective.addOnY W hΔ) hh₁.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (homOfLE_le_addOnY W hΔ p)))⟩

end Descent

section StrengthenedDescent

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) [IsDomain R] [IsJacobsonRing R]
variable (i j : Fin 3) [IsDomain (biChartRing W i j)]

/-- Standalone collapse: the image inclusion through `isoImage.inv`. -/
lemma blOpenZImage_ι_eq :
    (blOpenZImage W i j).ι =
      (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenZPieceFamily W i j k)).inv ≫
        (⨆ k, blOpenZPieceFamily W i j k).ι ≫ pieceι W i j :=
  (Iso.inv_hom_id_assoc _ _).symm.trans
    (congrArg ((Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenZPieceFamily W i j k)).inv ≫ ·)
      (Scheme.Hom.isoImage_hom_ι (pieceι W i j) _))

/-- Standalone collapse: the σ-chain into `pieceAwayZι` is the piece inclusion. -/
lemma mR_isoAway_pieceAwayZι (k : Fin 3) :
    morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
        (lawOneTriple W i j k)).inv ≫ pieceAwayZι W i j k =
      (blOpenZPieceFamily W i j k).ι ≫ pieceι W i j := by
  rw [pieceAwayZι]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, morphismRestrict_ι]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- [C6-d3, Z] The strengthened within-chart descent: the factoring ψ ALSO satisfies the
immersion equation — `Spec.map ψ ≫ pieceAwayZι` is the original point's total immersion. -/
theorem SpecPoint.factors_addOnZImage (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (blOpenZImage W i j).toScheme) :
    ∃ (k : Fin 3) (ψ : Localization.Away (lawOneTriple W i j k) →+* K),
      h ≫ addOnZOnImage W hΔ i j = Spec.map (CommRingCat.ofHom ψ) ≫ addOnZPieceMor W i j k hΔ ∧
      Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k = h ≫ (blOpenZImage W i j).ι := by
  obtain ⟨k, h₂, hh₂⟩ := exists_lift_iSup_of_unique (blOpenZPieceFamily W i j)
    (h ≫ (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenZPieceFamily W i j k)).inv)
  refine ⟨k, CommRingCat.Hom.hom (Spec.preimage (h₂ ≫ morphismRestrict (chartPieceIso W i j).hom
      (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
    (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv)),
    ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have e₁ : h ≫ addOnZOnImage W hΔ i j =
        (h ≫ (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenZPieceFamily W i j k)).inv) ≫
          addOnZOnSup W i j hΔ := by
      rw [addOnZOnImage, Category.assoc]
    have e₂ : (h ≫ (Scheme.Hom.isoImage (pieceι W i j)
          (⨆ k, blOpenZPieceFamily W i j k)).inv) ≫ addOnZOnSup W i j hΔ =
        h₂ ≫ addOnZOnFamily W i j k hΔ :=
      (congrArg (· ≫ addOnZOnSup W i j hΔ) hh₂.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (h₂ ≫ ·) (ι_addOnZOnSup W i j hΔ k)))
    rw [e₁, e₂, addOnZOnFamily]
    simp only [Category.assoc]
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hR : h ≫ (blOpenZImage W i j).ι =
        h₂ ≫ (blOpenZPieceFamily W i j k).ι ≫ pieceι W i j :=
      (congrArg (h ≫ ·) (blOpenZImage_ι_eq W i j)).trans
        (((Category.assoc _ _ _).symm).trans
          ((congrArg (· ≫ (⨆ k, blOpenZPieceFamily W i j k).ι ≫ pieceι W i j) hh₂.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (h₂ ≫ ·)
                ((Category.assoc _ _ _).symm.trans
                  (congrArg (· ≫ pieceι W i j) (Scheme.homOfLE_ι _ _)))))))
    rw [hR]
    exact (Category.assoc _ _ _).trans (congrArg (h₂ ≫ ·) (mR_isoAway_pieceAwayZι W i j k))

/-- Standalone collapse: the image inclusion through `isoImage.inv`. -/
lemma blOpenYImage_ι_eq :
    (blOpenYImage W i j).ι =
      (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenYPieceFamily W i j k)).inv ≫
        (⨆ k, blOpenYPieceFamily W i j k).ι ≫ pieceι W i j :=
  (Iso.inv_hom_id_assoc _ _).symm.trans
    (congrArg ((Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenYPieceFamily W i j k)).inv ≫ ·)
      (Scheme.Hom.isoImage_hom_ι (pieceι W i j) _))

/-- Standalone collapse: the σ-chain into `pieceAwayι` is the piece inclusion. -/
lemma mR_isoAway_pieceAwayι (k : Fin 3) :
    morphismRestrict (chartPieceIso W i j).hom
        (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
      (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j))
        (lawTwoTriple W i j k)).inv ≫ pieceAwayι W i j k =
      (blOpenYPieceFamily W i j k).ι ≫ pieceι W i j := by
  rw [pieceAwayι]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, morphismRestrict_ι]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- [C6-d3, Y] The strengthened within-chart descent: the factoring ψ ALSO satisfies the
immersion equation — `Spec.map ψ ≫ pieceAwayι` is the original point's total immersion. -/
theorem SpecPoint.factors_addOnYImage (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (blOpenYImage W i j).toScheme) :
    ∃ (k : Fin 3) (ψ : Localization.Away (lawTwoTriple W i j k) →+* K),
      h ≫ addOnYOnImage W hΔ i j = Spec.map (CommRingCat.ofHom ψ) ≫ addOnYPieceMor W i j k hΔ ∧
      Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k = h ≫ (blOpenYImage W i j).ι := by
  obtain ⟨k, h₂, hh₂⟩ := exists_lift_iSup_of_unique (blOpenYPieceFamily W i j)
    (h ≫ (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenYPieceFamily W i j k)).inv)
  refine ⟨k, CommRingCat.Hom.hom (Spec.preimage (h₂ ≫ morphismRestrict (chartPieceIso W i j).hom
      (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
    (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).inv)),
    ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have e₁ : h ≫ addOnYOnImage W hΔ i j =
        (h ≫ (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenYPieceFamily W i j k)).inv) ≫
          addOnYOnSup W i j hΔ := by
      rw [addOnYOnImage, Category.assoc]
    have e₂ : (h ≫ (Scheme.Hom.isoImage (pieceι W i j)
          (⨆ k, blOpenYPieceFamily W i j k)).inv) ≫ addOnYOnSup W i j hΔ =
        h₂ ≫ addOnYOnFamily W i j k hΔ :=
      (congrArg (· ≫ addOnYOnSup W i j hΔ) hh₂.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (h₂ ≫ ·) (ι_addOnYOnSup W i j hΔ k)))
    rw [e₁, e₂, addOnYOnFamily]
    simp only [Category.assoc]
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    have hR : h ≫ (blOpenYImage W i j).ι =
        h₂ ≫ (blOpenYPieceFamily W i j k).ι ≫ pieceι W i j :=
      (congrArg (h ≫ ·) (blOpenYImage_ι_eq W i j)).trans
        (((Category.assoc _ _ _).symm).trans
          ((congrArg (· ≫ (⨆ k, blOpenYPieceFamily W i j k).ι ≫ pieceι W i j) hh₂.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (h₂ ≫ ·)
                ((Category.assoc _ _ _).symm.trans
                  (congrArg (· ≫ pieceι W i j) (Scheme.homOfLE_ι _ _)))))))
    rw [hR]
    exact (Category.assoc _ _ _).trans (congrArg (h₂ ≫ ·) (mR_isoAway_pieceAwayι W i j k))

end StrengthenedDescent

section TensorLegs

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) (i j : Fin 3)

/-- [C6-d4a, left] The left tensor leg carries the chart coordinate to the first tautological
point's coordinate. -/
lemma tensorLeftLeg_chartCoord (m : {l : Fin 3 // l ≠ i}) :
    ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom
          (A := chartAway W i) (B := chartAway W j)))
      (chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.X m))) =
      biChartPointFst W i j m := by
  rw [RingHom.comp_apply]
  show (biChartRingAwayTensorEquiv W i j).symm
      ((chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.X m))) ⊗ₜ[R] 1) = _
  rw [biChartRingAwayTensorEquiv]
  show (biChartRingTensorEquiv W i j).symm
      ((Algebra.TensorProduct.congr (chartCoordAlgEquiv W i) (chartCoordAlgEquiv W j)).symm
        ((chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.X m))) ⊗ₜ[R] 1)) = _
  have hcongr : (Algebra.TensorProduct.congr (chartCoordAlgEquiv W i)
        (chartCoordAlgEquiv W j)).symm
      ((chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.X m))) ⊗ₜ[R] 1) =
      (Ideal.Quotient.mk _ (MvPolynomial.X m)) ⊗ₜ[R] (1 : affineChartRing W j) := by
    rw [Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul, map_one]
    congr 1
    exact (chartCoordEquiv W i).symm_apply_apply _
  rw [hcongr]
  have hten : (biChartRingTensorEquiv W i j)
      (Ideal.Quotient.mk _ (rename Sum.inl (MvPolynomial.X m))) =
      (Ideal.Quotient.mk _ (MvPolynomial.X m) : affineChartRing W i) ⊗ₜ[R]
        (1 : affineChartRing W j) :=
    biChartRingTensorEquiv_mk_rename_inl W i j _
  rw [← hten, AlgEquiv.symm_apply_apply, rename_X]
  rw [biChartPointFst, dif_neg m.2]

/-- [C6-d4a, right] The right tensor leg carries the chart coordinate to the second tautological
point's coordinate. -/
lemma tensorRightLeg_chartCoord (m : {l : Fin 3 // l ≠ j}) :
    ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := R) (A := chartAway W i) (B := chartAway W j)).toRingHom)
      (chartCoordEquiv W j (Ideal.Quotient.mk _ (MvPolynomial.X m))) =
      biChartPointSnd W i j m := by
  rw [RingHom.comp_apply]
  show (biChartRingAwayTensorEquiv W i j).symm
      ((1 : chartAway W i) ⊗ₜ[R] (chartCoordEquiv W j (Ideal.Quotient.mk _
        (MvPolynomial.X m)))) = _
  rw [biChartRingAwayTensorEquiv]
  show (biChartRingTensorEquiv W i j).symm
      ((Algebra.TensorProduct.congr (chartCoordAlgEquiv W i) (chartCoordAlgEquiv W j)).symm
        ((1 : chartAway W i) ⊗ₜ[R]
          (chartCoordEquiv W j (Ideal.Quotient.mk _ (MvPolynomial.X m))))) = _
  have hcongr : (Algebra.TensorProduct.congr (chartCoordAlgEquiv W i)
        (chartCoordAlgEquiv W j)).symm
      ((1 : chartAway W i) ⊗ₜ[R]
        (chartCoordEquiv W j (Ideal.Quotient.mk _ (MvPolynomial.X m)))) =
      (1 : affineChartRing W i) ⊗ₜ[R] (Ideal.Quotient.mk _ (MvPolynomial.X m)) := by
    rw [Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul, map_one]
    congr 1
    exact (chartCoordEquiv W j).symm_apply_apply _
  rw [hcongr]
  have hten : (biChartRingTensorEquiv W i j)
      (Ideal.Quotient.mk _ (rename Sum.inr (MvPolynomial.X m))) =
      (1 : affineChartRing W i) ⊗ₜ[R]
        (Ideal.Quotient.mk _ (MvPolynomial.X m) : affineChartRing W j) :=
    biChartRingTensorEquiv_mk_rename_inr W i j _
  rw [← hten, AlgEquiv.symm_apply_apply, rename_X]
  rw [biChartPointSnd, dif_neg m.2]

end TensorLegs

section PieceProjections

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) (i j : Fin 3)

/-- [C6-d4b, Z-fst] Through the piece immersion, the first projection is the chart point of the
composite ring map through the left tensor leg. -/
lemma specMap_pieceAwayZι_fst {K : Type u} [CommRing K] (k : Fin 3)
    (ψ : Localization.Away (lawOneTriple W i j k) →+* K) :
    Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k ≫
        pullback.fst (projModelπ W) (projModelπ W) =
      Spec.map (CommRingCat.ofHom (ψ.comp
        ((algebraMap (biChartRing W i j) (Localization.Away (lawOneTriple W i j k))).comp
          ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom
              (A := chartAway W i) (B := chartAway W j)))))) ≫ chartι W i := by
  rw [pieceAwayZι_eq]
  simp only [Category.assoc]
  rw [pieceι_fst]
  rw [← Category.assoc (chartPieceIso W i j).inv, chartPieceIso_inv_fst]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
/-- [C6-d4b, Z-snd] Through the piece immersion, the second projection is the chart point of the
composite ring map through the right tensor leg. -/
lemma specMap_pieceAwayZι_snd {K : Type u} [CommRing K] (k : Fin 3)
    (ψ : Localization.Away (lawOneTriple W i j k) →+* K) :
    Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k ≫
        pullback.snd (projModelπ W) (projModelπ W) =
      Spec.map (CommRingCat.ofHom (ψ.comp
        ((algebraMap (biChartRing W i j) (Localization.Away (lawOneTriple W i j k))).comp
          ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
            (Algebra.TensorProduct.includeRight
              (R := R) (A := chartAway W i) (B := chartAway W j)).toRingHom)))) ≫ chartι W j := by
  rw [pieceAwayZι_eq]
  simp only [Category.assoc]
  rw [pieceι_snd]
  rw [← Category.assoc (chartPieceIso W i j).inv, chartPieceIso_inv_snd]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- [C6-d4b, Y-fst] Through the piece immersion, the first projection is the chart point of the
composite ring map through the left tensor leg. -/
lemma specMap_pieceAwayι_fst {K : Type u} [CommRing K] (k : Fin 3)
    (ψ : Localization.Away (lawTwoTriple W i j k) →+* K) :
    Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k ≫
        pullback.fst (projModelπ W) (projModelπ W) =
      Spec.map (CommRingCat.ofHom (ψ.comp
        ((algebraMap (biChartRing W i j) (Localization.Away (lawTwoTriple W i j k))).comp
          ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom
              (A := chartAway W i) (B := chartAway W j)))))) ≫ chartι W i := by
  rw [pieceAwayι_eq]
  simp only [Category.assoc]
  rw [pieceι_fst]
  rw [← Category.assoc (chartPieceIso W i j).inv, chartPieceIso_inv_fst]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- [C6-d4b, Y-snd] Through the piece immersion, the second projection is the chart point of the
composite ring map through the right tensor leg. -/
lemma specMap_pieceAwayι_snd {K : Type u} [CommRing K] (k : Fin 3)
    (ψ : Localization.Away (lawTwoTriple W i j k) →+* K) :
    Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k ≫
        pullback.snd (projModelπ W) (projModelπ W) =
      Spec.map (CommRingCat.ofHom (ψ.comp
        ((algebraMap (biChartRing W i j) (Localization.Away (lawTwoTriple W i j k))).comp
          ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
            (Algebra.TensorProduct.includeRight
              (R := R) (A := chartAway W i) (B := chartAway W j)).toRingHom)))) ≫ chartι W j := by
  rw [pieceAwayι_eq]
  simp only [Category.assoc]
  rw [pieceι_snd]
  rw [← Category.assoc (chartPieceIso W i j).inv, chartPieceIso_inv_snd]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end PieceProjections

section TripleIdentification

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) (i j : Fin 3)

/-- [C6-d5, law 1] A ring map out of the chart-product ring carries the law-1 triple to
mathlib's `addXYZ` of the images of the tautological points. -/
lemma ringHom_lawOneTriple {K : Type u} [CommRing K] (χ : biChartRing W i j →+* K) :
    χ ∘ lawOneTriple W i j =
      ((W.map (algebraMap R (biChartRing W i j))).toProjective.map χ).addXYZ
        (χ ∘ biChartPointFst W i j) (χ ∘ biChartPointSnd W i j) := by
  rw [lawOneTriple]
  exact (map_addXYZ χ _ _).symm

/-- [C6-d5, law 2] Mirror for the law-2 triple (`dblAddXYZ`). -/
lemma ringHom_lawTwoTriple {K : Type u} [CommRing K] (χ : biChartRing W i j →+* K) :
    χ ∘ lawTwoTriple W i j =
      ((W.map (algebraMap R (biChartRing W i j))).toProjective.map χ).dblAddXYZ
        (χ ∘ biChartPointFst W i j) (χ ∘ biChartPointSnd W i j) := by
  rw [lawTwoTriple]
  exact (map_dblAddXYZ χ _ _).symm

end TripleIdentification

section ChartNaturality

open WeierstrassCurve.Projective HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- [C6-c'0] `Proj.awayι` transported across an element equality (`eqToHom` quarantine).

ForMathlib candidate: a general graded-ring `Proj.awayι` transport, with no elliptic-curve
content. -/
theorem Proj_awayι_congr {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {m : ℕ} (hm : 0 < m)
    (f g : A) (h : f = g) (hf : f ∈ 𝒜 m) (hg : g ∈ 𝒜 m) :
    Proj.awayι 𝒜 f hf hm =
      eqToHom (by rw [h]) ≫ Proj.awayι 𝒜 g hg hm := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

variable {U : Type u} [CommRing U] {R : Type u} [CommRing R]

/-- The graded `Away`-map of the base change at the `i`-th chart generator. -/
noncomputable def bcChartAwayMap (f : U →+* R) (W₀ : WeierstrassCurve U) (i : Fin 3) :
    HomogeneousLocalization.Away (quotientGrading (projIdeal W₀))
        ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i)) →+*
      HomogeneousLocalization.Away (quotientGrading (projIdeal (W₀.map f)))
        (baseChangeGradedHom f W₀ ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i))) :=
  HomogeneousLocalization.Away.map (baseChangeGradedHom f W₀)
    ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i))

/-- [C6-c'1] The literal chart-restriction of the base change (`awayι_comp_map` instantiated). -/
theorem awayι_image_comp_projModelBaseChange (f : U →+* R) (W₀ : WeierstrassCurve U)
    (i : Fin 3) :
    Proj.awayι (quotientGrading (projIdeal (W₀.map f)))
        (baseChangeGradedHom f W₀ ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i)))
        ((baseChangeGradedHom f W₀).2 (mk_X_mem_quotientGrading_one W₀ i)) one_pos ≫
        projModelBaseChange f W₀ =
      Spec.map (CommRingCat.ofHom (bcChartAwayMap f W₀ i)) ≫ chartι W₀ i :=
  Proj.awayι_comp_map (baseChangeGradedHom f W₀) (baseChangeGradedHom_irrelevant_le f W₀)
    one_pos _ (mk_X_mem_quotientGrading_one W₀ i)

variable {U : Type u} [CommRing U]

/-- The chart generator's image under the base change is the mapped chart generator. -/
lemma baseChangeGradedHom_chartGen (f : U →+* R) (W₀ : WeierstrassCurve U) (i : Fin 3) :
    baseChangeGradedHom f W₀ ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i)) =
      (quotientGradingHom (projIdeal (W₀.map f))) (MvPolynomial.X i) := by
  have h := HomogeneousIdeal.quotientGradingMap_mk (mvMapGraded f) (projIdeal W₀)
    (projIdeal (W₀.map f)) (projIdeal_le_comap f W₀) (MvPolynomial.X i)
  rw [quotientGradingHom_apply, quotientGradingHom_apply]
  rw [show baseChangeGradedHom f W₀ = quotientGradingMap (mvMapGraded f) (projIdeal W₀)
    (projIdeal (W₀.map f)) (projIdeal_le_comap f W₀) from rfl]
  rw [h]
  congr 1
  exact MvPolynomial.map_X f i

/-- [C6-c'2] The mapped chart immersion through the base change: `eqToHom`-quarantined form. -/
theorem chartι_map_comp_projModelBaseChange (f : U →+* R) (W₀ : WeierstrassCurve U) (i : Fin 3) :
    chartι (W₀.map f) i ≫ projModelBaseChange f W₀ =
      eqToHom (by rw [baseChangeGradedHom_chartGen f W₀ i]) ≫
        Spec.map (CommRingCat.ofHom (bcChartAwayMap f W₀ i)) ≫ chartι W₀ i := by
  have hcongr := Proj_awayι_congr (quotientGrading (projIdeal (W₀.map f))) one_pos
    ((quotientGradingHom (projIdeal (W₀.map f))) (MvPolynomial.X i))
    (baseChangeGradedHom f W₀ ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i)))
    (baseChangeGradedHom_chartGen f W₀ i).symm
    (mk_X_mem_quotientGrading_one (W₀.map f) i)
    ((baseChangeGradedHom f W₀).2 (mk_X_mem_quotientGrading_one W₀ i))
  show Proj.awayι _ _ (mk_X_mem_quotientGrading_one (W₀.map f) i) one_pos ≫
      projModelBaseChange f W₀ = _
  rw [hcongr, Category.assoc, awayι_image_comp_projModelBaseChange]

/-- [C6-e4a] `bcChartAwayMap` carries the chart coordinate elements to the image coordinates. -/
lemma bcChartAwayMap_isLocalizationElem (f : U →+* R) (W₀ : WeierstrassCurve U) (i m : Fin 3) :
    bcChartAwayMap f W₀ i (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W₀ i) (mk_X_mem_quotientGrading_one W₀ m)) =
      HomogeneousLocalization.Away.isLocalizationElem
        ((baseChangeGradedHom f W₀).2 (mk_X_mem_quotientGrading_one W₀ i))
        ((baseChangeGradedHom f W₀).2 (mk_X_mem_quotientGrading_one W₀ m)) := by
  rw [bcChartAwayMap]
  simp only [HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.map_mk]
  congr 1
  rw [pow_one, pow_one]
  rfl

/-- [C6-e4, scheme level] A W-side chart point pushed through the base change is the atlas-side
chart point of the composed ring map (`Spec.map_eqToHom` collapses the transport). -/
theorem specMap_chartι_comp_baseChange (f : U →+* R) (W₀ : WeierstrassCurve U) (i : Fin 3)
    {K : Type u} [CommRing K] (φ : chartAway (W₀.map f) i →+* K)
    (e : CommRingCat.of (HomogeneousLocalization.Away
        (quotientGrading (projIdeal (W₀.map f)))
        (baseChangeGradedHom f W₀
          ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i)))) =
      CommRingCat.of (chartAway (W₀.map f) i)) :
    (Spec.map (CommRingCat.ofHom φ) ≫ chartι (W₀.map f) i) ≫ projModelBaseChange f W₀ =
      Spec.map (CommRingCat.ofHom ((φ.comp
          (CommRingCat.Hom.hom (eqToHom e))).comp (bcChartAwayMap f W₀ i))) ≫
        chartι W₀ i := by
  rw [Category.assoc, chartι_map_comp_projModelBaseChange f W₀ i]
  rw [show (eqToHom (by rw [baseChangeGradedHom_chartGen f W₀ i]) :
      Spec (CommRingCat.of (chartAway (W₀.map f) i)) ⟶
        Spec (CommRingCat.of (HomogeneousLocalization.Away
          (quotientGrading (projIdeal (W₀.map f)))
          (baseChangeGradedHom f W₀
            ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X i)))))) =
    Spec.map (eqToHom e) from by rw [Spec.map_eqToHom]]
  simp only [← Category.assoc, ← Spec.map_comp]
  rw [← CommRingCat.ofHom_hom (eqToHom e), ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]

section ChartPointTriple

open WeierstrassCurve.Projective HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The `φ`-triple of a chart point: the dictionary-side coordinates of `Spec.map φ ≫ chartι k`. -/
noncomputable def chartPointTriple (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] (φ : chartAway W k →+* K) : Fin 3 → K := fun m ↦
  φ (HomogeneousLocalization.Away.isLocalizationElem
    (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m))

/-- The k-th coordinate of the φ-triple is 1. -/
lemma ChartPointTriple.self_eq_one (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] (φ : chartAway W k →+* K) :
    chartPointTriple W k φ k = 1 := by
  rw [chartPointTriple]
  have h1 : (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W k) :
        chartAway W k) = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
    exact Localization.mk_self
      (⟨(quotientGradingHom (projIdeal W)) (MvPolynomial.X k) ^ 1, ⟨1, rfl⟩⟩ :
        Submonoid.powers ((quotientGradingHom (projIdeal W)) (MvPolynomial.X k)))
  rw [h1, map_one]

/-- The φ-triple is the affine chart point pushed through the coordinate equivalence and φ. -/
lemma ChartPointTriple.eq_comp (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] (φ : chartAway W k →+* K) :
    chartPointTriple W k φ =
      (φ.comp (chartCoordAlgEquiv W k).toRingHom) ∘ affineChartPoint W k := by
  funext m
  by_cases hm : m = k
  · subst hm
    rw [ChartPointTriple.self_eq_one]
    show _ = (φ.comp (chartCoordAlgEquiv W m).toRingHom) (affineChartPoint W m m)
    rw [show affineChartPoint W m m = 1 from dif_pos rfl]
    simp
  · show chartPointTriple W k φ m = (φ.comp (chartCoordAlgEquiv W k).toRingHom)
      (affineChartPoint W k m)
    rw [show affineChartPoint W k m = Ideal.Quotient.mk _ (MvPolynomial.X ⟨m, hm⟩)
      from dif_neg hm]
    rw [chartPointTriple, RingHom.comp_apply]
    congr 1
    exact (chartCoordEquiv_mk_X W k ⟨m, hm⟩).symm

/-- The φ-triple lies on the base-changed curve (the chart relation is killed in `chartAway`). -/
lemma ChartPointTriple.equation (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K] (φ : chartAway W k →+* K)
    (hφ : φ.comp (algebraMap R (chartAway W k)) = algebraMap R K) :
    (W.map (algebraMap R K)).toProjective.Equation (chartPointTriple W k φ) := by
  rw [ChartPointTriple.eq_comp]
  have heq := (equation_affineChartPoint W k).map
    (φ.comp (chartCoordAlgEquiv W k).toRingHom)
  rw [show ((W.map (algebraMap R (affineChartRing W k))).toProjective.map
      (φ.comp (chartCoordAlgEquiv W k).toRingHom)) = (W.map (algebraMap R K)).toProjective
      from ?_] at heq
  · exact heq
  · show (W.map (algebraMap R (affineChartRing W k))).map
      (φ.comp (chartCoordAlgEquiv W k).toRingHom) = W.map (algebraMap R K)
    rw [WeierstrassCurve.map_map]
    congr 1
    rw [RingHom.comp_assoc]
    rw [show (chartCoordAlgEquiv W k).toRingHom.comp (algebraMap R (affineChartRing W k)) =
      algebraMap R (chartAway W k) from (chartCoordAlgEquiv W k).toAlgHom.comp_algebraMap]
    exact hφ

/-- [k1] Ring maps out of a chart ring are determined by the base and the coordinates. -/
lemma chartAwayHom_ext (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] (χ₁ χ₂ : chartAway W k →+* K)
    (hR : χ₁.comp (algebraMap R (chartAway W k)) = χ₂.comp (algebraMap R (chartAway W k)))
    (hcoord : ∀ m : {l : Fin 3 // l ≠ k},
      χ₁ (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m)) =
      χ₂ (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m))) :
    χ₁ = χ₂ := by
  have hsurj : Function.Surjective (chartCoordAlgEquiv W k).toRingHom :=
    (chartCoordAlgEquiv W k).surjective
  rw [← RingHom.cancel_right hsurj]
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    show χ₁ ((chartCoordAlgEquiv W k) (Ideal.Quotient.mk _ (MvPolynomial.C r))) =
      χ₂ ((chartCoordAlgEquiv W k) (Ideal.Quotient.mk _ (MvPolynomial.C r)))
    rw [show ((chartCoordAlgEquiv W k) (Ideal.Quotient.mk _ (MvPolynomial.C r)) :
        chartAway W k) = chartCoordEquiv W k (Ideal.Quotient.mk _ (MvPolynomial.C r)) from rfl,
      chartCoordEquiv_mk_C, ← chartAway_algebraMap_apply]
    exact RingHom.congr_fun hR r
  · intro m
    simp only [RingHom.comp_apply]
    show χ₁ ((chartCoordAlgEquiv W k) (Ideal.Quotient.mk _ (MvPolynomial.X m))) =
      χ₂ ((chartCoordAlgEquiv W k) (Ideal.Quotient.mk _ (MvPolynomial.X m)))
    rw [show ((chartCoordAlgEquiv W k) (Ideal.Quotient.mk _ (MvPolynomial.X m)) :
        chartAway W k) = chartCoordEquiv W k (Ideal.Quotient.mk _ (MvPolynomial.X m)) from rfl,
      chartCoordEquiv_mk_X]
    exact hcoord m

/-- Generic coordinate action of a chart-triple morphism on the localization coordinates. -/
lemma chartAwayHomOfTriple_isLocalizationElem (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K] (t : Fin 3 → K) (u : K) (hu : t k * u = 1)
    (ht : (W.map (algebraMap R K)).toProjective.Equation t) (m : {l : Fin 3 // l ≠ k}) :
    chartAwayHomOfTriple W k t u hu ht (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m)) =
      t m * u := by
  rw [← chartCoordEquiv_mk_X]
  unfold chartAwayHomOfTriple
  have hround : (chartCoordAlgEquiv W k).symm (chartCoordEquiv W k (Ideal.Quotient.mk _
      (MvPolynomial.X m))) = Ideal.Quotient.mk _ (MvPolynomial.X m) :=
    (chartCoordEquiv W k).symm_apply_apply _
  show (chartHomOfTriple W k t u hu ht)
      ((chartCoordAlgEquiv W k).symm (chartCoordEquiv W k (Ideal.Quotient.mk _
        (MvPolynomial.X m)))) = _
  rw [hround, chartHomOfTriple_coord]

/-- [k2] An `R`-compatible ring map out of a chart ring IS the chart morphism of its own
coordinate triple. -/
lemma ChartPointTriple.eq_chartHom (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K] (φ : chartAway W k →+* K)
    (hφ : φ.comp (algebraMap R (chartAway W k)) = algebraMap R K)
    (hu : chartPointTriple W k φ k * 1 = 1)
    (hT : (W.map (algebraMap R K)).toProjective.Equation (chartPointTriple W k φ)) :
    φ = (chartAwayHomOfTriple W k (chartPointTriple W k φ) 1 hu hT).toRingHom := by
  refine chartAwayHom_ext W k _ _ ?_ ?_
  · rw [hφ]
    exact ((chartAwayHomOfTriple W k (chartPointTriple W k φ) 1 hu hT).comp_algebraMap).symm
  · intro m
    rw [show ((chartAwayHomOfTriple W k (chartPointTriple W k φ) 1 hu hT).toRingHom :
        chartAway W k →+* K) (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m)) =
      chartPointTriple W k φ m * 1 from
        chartAwayHomOfTriple_isLocalizationElem W k _ 1 hu hT m, mul_one]
    rfl

/-- **[e5c-key] The dictionary reads any chart point as `toAffine` of its coordinate triple.** -/
theorem Dictionary.eq_toAffine (W : WeierstrassCurve R) [W.IsElliptic] (k : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (φ : chartAway W k →+* K)
    (hφ : φ.comp (algebraMap R (chartAway W k)) = algebraMap R K)
    (g : SpecPoints (projModel W) (projModelπ W) K)
    (hg : Spec.map (CommRingCat.ofHom φ) ≫ chartι W k = g.1) :
    projModelPointsEquiv W K g =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        (chartPointTriple W k φ) := by
  classical
  have hT : (W.map (algebraMap R K)).toProjective.Equation (chartPointTriple W k φ) :=
    ChartPointTriple.equation W k φ hφ
  have : ((W.map (algebraMap R K)).toProjective).IsElliptic := by
    constructor
    rw [map_Δ]
    exact W.isUnit_Δ.map _
  -- the φ-subtype (the grade-0 compat form is defeq to hφ via chartAway_algebraMap_apply)
  have hφ' : φ.comp ((algebraMap (↥(quotientGrading (projIdeal W) 0))
      (Away (quotientGrading (projIdeal W))
        ((quotientGradingHom (projIdeal W)) (MvPolynomial.X k)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
      algebraMap R K := hφ
  by_cases hz : chartPointTriple W k φ 2 = 0
  · -- infinity branch
    rw [WeierstrassCurve.Projective.Point.toAffine_of_Z_eq_zero hz]
    have hiff := inZChart_iff_of_specMap W k ⟨φ, hφ'⟩ g hg
    have hnotZ : ¬ InZChart W g := fun hin ↦ (hiff.mp hin) hz
    show projModelPointsEquivEll W ‹W.IsElliptic› K g = 0
    exact projModelPointsEquivEll_infinity W ‹W.IsElliptic› K g hnotZ
  · -- affine branch
    have hne : chartPointTriple W k φ ≠ 0 := fun h0 ↦ by
      have := congrFun h0 k
      rw [ChartPointTriple.self_eq_one] at this
      exact one_ne_zero this
    have hNS : (W.map (algebraMap R K)).toProjective.Nonsingular (chartPointTriple W k φ) :=
      WeierstrassCurve.Projective.nonsingular_of_equation_of_ne_zero hT hne
    rw [WeierstrassCurve.Projective.Point.toAffine_of_Z_ne_zero hNS hz]
    -- the chart-2 form of the point
    have hu1 : chartPointTriple W k φ k * 1 = 1 := by
      rw [ChartPointTriple.self_eq_one, mul_one]
    have hv : chartPointTriple W k φ 2 * (chartPointTriple W k φ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ hz
    have hfac2 : Spec.map (CommRingCat.ofHom
        (chartAwayHomOfTriple W 2 (chartPointTriple W k φ) (chartPointTriple W k φ 2)⁻¹
          hv hT).toRingHom) ≫ chartι W 2 = g.1 := by
      by_cases hk : k = 2
      · subst hk
        rw [← hg]
        congr 2
        have h1 : (chartPointTriple W 2 φ 2)⁻¹ = 1 := by
          rw [ChartPointTriple.self_eq_one, inv_one]
        rw [show (chartAwayHomOfTriple W 2 (chartPointTriple W 2 φ)
            (chartPointTriple W 2 φ 2)⁻¹ hv hT) =
          (chartAwayHomOfTriple W 2 (chartPointTriple W 2 φ) 1 hu1 hT) from by
            simp only [h1]]
        exact congrArg CommRingCat.ofHom (ChartPointTriple.eq_chartHom W 2 φ hφ hu1 hT).symm
      · rw [chartι_comp_specMap_chartAwayHom_eq W 2 k hk
          (chartPointTriple W k φ) (chartPointTriple W k φ 2)⁻¹ 1 hv hu1 hT, ← hg]
        congr 2
        exact congrArg CommRingCat.ofHom (ChartPointTriple.eq_chartHom W k φ hφ hu1 hT).symm
    have hZ : InZChart W g :=
      ⟨Spec.map (CommRingCat.ofHom
        (chartAwayHomOfTriple W 2 (chartPointTriple W k φ) (chartPointTriple W k φ 2)⁻¹
          hv hT).toRingHom), hfac2⟩
    have hcompat₂ : (chartAwayHomOfTriple W 2 (chartPointTriple W k φ)
        (chartPointTriple W k φ 2)⁻¹ hv hT).toRingHom.comp
        ((algebraMap (↥(quotientGrading (projIdeal W) 0))
          (Away (quotientGrading (projIdeal W))
            ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)))).comp
          ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (projIdeal W) 0))) =
        algebraMap R K :=
      (chartAwayHomOfTriple W 2 (chartPointTriple W k φ)
        (chartPointTriple W k φ 2)⁻¹ hv hT).comp_algebraMap
    have hread : chartHomEquiv W 2 K ⟨g, hZ⟩ =
        ⟨(chartAwayHomOfTriple W 2 (chartPointTriple W k φ)
          (chartPointTriple W k φ 2)⁻¹ hv hT).toRingHom, hcompat₂⟩ :=
      chartHomEquiv_eq_of_specMap W 2 ⟨g, hZ⟩ _ hfac2
    have hcoord : ∀ m : {j : Fin 3 // j ≠ 2},
        (chartSolutionsEquiv W 2 K (chartHomEquiv W 2 K ⟨g, hZ⟩)).1 m =
          chartPointTriple W k φ m / chartPointTriple W k φ 2 := by
      intro m
      rw [hread]
      have hidiom : ((chartSolutionsEquiv W 2 K)
          ⟨(chartAwayHomOfTriple W 2 (chartPointTriple W k φ)
            (chartPointTriple W k φ 2)⁻¹ hv hT).toRingHom, hcompat₂⟩).1 =
          fun m : {j : Fin 3 // j ≠ 2} ↦
            (chartAwayHomOfTriple W 2 (chartPointTriple W k φ)
              (chartPointTriple W k φ 2)⁻¹ hv hT).toRingHom
              (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X m))) := rfl
      rw [hidiom]
      show (chartAwayHomOfTriple W 2 (chartPointTriple W k φ)
          (chartPointTriple W k φ 2)⁻¹ hv hT).toRingHom
          (chartCoordEquiv W 2 (Ideal.Quotient.mk _ (MvPolynomial.X m))) = _
      rw [chartCoordEquiv_mk_X, div_eq_mul_inv]
      exact chartAwayHomOfTriple_isLocalizationElem W 2 _ _ hv hT m
    refine (projModelPointsEquiv_some W K g hZ
      (chartPointTriple W k φ 0 / chartPointTriple W k φ 2)
      (chartPointTriple W k φ 1 / chartPointTriple W k φ 2)
      ((WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero hz).mp hNS)
      (hcoord ⟨0, by decide⟩).symm (hcoord ⟨1, by decide⟩).symm).trans rfl

/-- Ring-level compatibility extraction: a chart point that is π-compatible has an R-compatible
ring map (Spec-faithfulness through `chartι_projModelπ`). -/
lemma chartHom_compat_of_specPoint (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K] (φ : chartAway W k →+* K)
    (hπ : (Spec.map (CommRingCat.ofHom φ) ≫ chartι W k) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    φ.comp (algebraMap R (chartAway W k)) = algebraMap R K := by
  rw [Category.assoc, chartι_projModelπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at hπ
  have h2 := Spec.map_inj.mp hπ
  exact congrArg CommRingCat.Hom.hom h2

section DictionaryOfPiece

open WeierstrassCurve.Projective HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Shared law-agnostic core of `Dictionary.fst_of_piece{Z,Y}`: parametrised over the away-triple
element `t`, once the first-projection chart factorisation `hP1` is supplied, `P`'s dictionary value
is `toAffine` of the left tautological image. -/
private lemma Dictionary.fst_of_piece_aux (W : WeierstrassCurve R) [W.IsElliptic] (i j : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P : SpecPoints (projModel W) (projModelπ W) K)
    (t : biChartRing W i j) (ψ : Localization.Away t →+* K)
    (hP1 : Spec.map (CommRingCat.ofHom (ψ.comp
        ((algebraMap (biChartRing W i j) (Localization.Away t)).comp
          ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom
              (A := chartAway W i) (B := chartAway W j)))))) ≫ chartι W i = P.1) :
    projModelPointsEquiv W K P =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away t))) ∘ biChartPointFst W i j) := by
  classical
  set φP : chartAway W i →+* K := ψ.comp
    ((algebraMap (biChartRing W i j) (Localization.Away t)).comp
      ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom
          (A := chartAway W i) (B := chartAway W j)))) with hφPdef
  have hπ : (Spec.map (CommRingCat.ofHom φP) ≫ chartι W i) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [hP1]
    exact P.2
  have hφP : φP.comp (algebraMap R (chartAway W i)) = algebraMap R K :=
    chartHom_compat_of_specPoint W i φP hπ
  rw [Dictionary.eq_toAffine W i φP hφP P hP1]
  congr 1
  funext m
  by_cases hm : m = i
  · subst hm
    rw [ChartPointTriple.self_eq_one]
    show (1 : K) = (ψ.comp (algebraMap _ _)) (biChartPointFst W m j m)
    rw [show biChartPointFst W m j m = 1 from dif_pos rfl, map_one]
  · show φP (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W i) (mk_X_mem_quotientGrading_one W m)) = _
    rw [← chartCoordEquiv_mk_X W i ⟨m, hm⟩, hφPdef]
    show ψ ((algebraMap _ _) (((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom
          (A := chartAway W i) (B := chartAway W j)))
      (chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.X ⟨m, hm⟩))))) = _
    rw [tensorLeftLeg_chartCoord W i j ⟨m, hm⟩]
    rfl

/-- Shared law-agnostic core of `Dictionary.snd_of_piece{Z,Y}`: the mirror of
`Dictionary.fst_of_piece_aux` for the second projection / right tautological image. -/
private lemma Dictionary.snd_of_piece_aux (W : WeierstrassCurve R) [W.IsElliptic] (i j : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (Q : SpecPoints (projModel W) (projModelπ W) K)
    (t : biChartRing W i j) (ψ : Localization.Away t →+* K)
    (hQ1 : Spec.map (CommRingCat.ofHom (ψ.comp
        ((algebraMap (biChartRing W i j) (Localization.Away t)).comp
          ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
            (Algebra.TensorProduct.includeRight
              (R := R) (A := chartAway W i) (B := chartAway W j)).toRingHom)))) ≫
        chartι W j = Q.1) :
    projModelPointsEquiv W K Q =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away t))) ∘ biChartPointSnd W i j) := by
  classical
  set φQ : chartAway W j →+* K := ψ.comp
    ((algebraMap (biChartRing W i j) (Localization.Away t)).comp
      ((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
        (Algebra.TensorProduct.includeRight
          (R := R) (A := chartAway W i) (B := chartAway W j)).toRingHom)) with hφQdef
  have hπ : (Spec.map (CommRingCat.ofHom φQ) ≫ chartι W j) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [hQ1]
    exact Q.2
  have hφQ : φQ.comp (algebraMap R (chartAway W j)) = algebraMap R K :=
    chartHom_compat_of_specPoint W j φQ hπ
  rw [Dictionary.eq_toAffine W j φQ hφQ Q hQ1]
  congr 1
  funext m
  by_cases hm : m = j
  · subst hm
    rw [ChartPointTriple.self_eq_one]
    show (1 : K) = (ψ.comp (algebraMap _ _)) (biChartPointSnd W i m m)
    rw [show biChartPointSnd W i m m = 1 from dif_pos rfl, map_one]
  · show φQ (HomogeneousLocalization.Away.isLocalizationElem
        (mk_X_mem_quotientGrading_one W j) (mk_X_mem_quotientGrading_one W m)) = _
    rw [← chartCoordEquiv_mk_X W j ⟨m, hm⟩, hφQdef]
    show ψ ((algebraMap (biChartRing W i j) (Localization.Away t))
        (((biChartRingAwayTensorEquiv W i j).symm.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := R) (A := chartAway W i) (B := chartAway W j)).toRingHom)
          (chartCoordEquiv W j (Ideal.Quotient.mk _ (MvPolynomial.X ⟨m, hm⟩))))) = _
    rw [tensorRightLeg_chartCoord W i j ⟨m, hm⟩]
    rfl

/-- [e5c-P] Through a law-1 piece presentation of the pair-point, `P`'s dictionary value is
`toAffine` of the first tautological image. -/
lemma Dictionary.fst_of_pieceZ (W : WeierstrassCurve R) [W.IsElliptic] (i j k : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W)
    (ψ : Localization.Away (lawOneTriple W i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k) :
    projModelPointsEquiv W K P =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away (lawOneTriple W i j k)))) ∘ biChartPointFst W i j) := by
  refine Dictionary.fst_of_piece_aux W i j P (lawOneTriple W i j k) ψ ?_
  rw [← pullback.lift_fst P.1 Q.1 w, hgp, Category.assoc, specMap_pieceAwayZι_fst W i j k ψ]
/-- [e5c-Q] Through a law-1 piece presentation of the pair-point, `Q`'s dictionary value is
`toAffine` of the second tautological image. -/
lemma Dictionary.snd_of_pieceZ (W : WeierstrassCurve R) [W.IsElliptic] (i j k : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W)
    (ψ : Localization.Away (lawOneTriple W i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k) :
    projModelPointsEquiv W K Q =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away (lawOneTriple W i j k)))) ∘ biChartPointSnd W i j) := by
  refine Dictionary.snd_of_piece_aux W i j Q (lawOneTriple W i j k) ψ ?_
  rw [← pullback.lift_snd P.1 Q.1 w, hgp, Category.assoc, specMap_pieceAwayZι_snd W i j k ψ]

/-- [e5c-P,Y] Through a law-2 piece presentation of the pair-point, `P`'s dictionary value is
`toAffine` of the first tautological image. -/
lemma Dictionary.fst_of_pieceY (W : WeierstrassCurve R) [W.IsElliptic] (i j k : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W)
    (ψ : Localization.Away (lawTwoTriple W i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k) :
    projModelPointsEquiv W K P =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away (lawTwoTriple W i j k)))) ∘ biChartPointFst W i j) := by
  refine Dictionary.fst_of_piece_aux W i j P (lawTwoTriple W i j k) ψ ?_
  rw [← pullback.lift_fst P.1 Q.1 w, hgp, Category.assoc, specMap_pieceAwayι_fst W i j k ψ]
/-- [e5c-Q,Y] Through a law-2 piece presentation of the pair-point, `Q`'s dictionary value is
`toAffine` of the second tautological image. -/
lemma Dictionary.snd_of_pieceY (W : WeierstrassCurve R) [W.IsElliptic] (i j k : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W)
    (ψ : Localization.Away (lawTwoTriple W i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k) :
    projModelPointsEquiv W K Q =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away (lawTwoTriple W i j k)))) ∘ biChartPointSnd W i j) := by
  refine Dictionary.snd_of_piece_aux W i j Q (lawTwoTriple W i j k) ψ ?_
  rw [← pullback.lift_snd P.1 Q.1 w, hgp, Category.assoc, specMap_pieceAwayι_snd W i j k ψ]

/-- Shared law-agnostic core of `Dictionary.sum_of_piece{Z,Y}`: parametrised over the on-curve
triple `lawT` (with its equation proof `hlaw`), the piece morphism being the `chartAwayHomOfTriple`
of `awayTriple`. The sum-point's dictionary value is `toAffine` of the triple image, obtained via
`toAffine_smul` from the unit `ψ (invSelf (lawT k))`. -/
private lemma Dictionary.sum_of_piece_aux (W : WeierstrassCurve R) [W.IsElliptic] (i j k : Fin 3)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (s : SpecPoints (projModel W) (projModelπ W) K)
    (lawT : Fin 3 → biChartRing W i j)
    (hlaw : (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation lawT)
    (ψ : Localization.Away (lawT k) →+* K)
    (hev : s.1 = Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (chartAwayHomOfTriple W k (awayTriple W i j k lawT)
          (IsLocalization.Away.invSelf (lawT k)) (awayTriple_mul_invSelf W i j k lawT)
          (equation_awayTriple W i j k lawT hlaw)).toRingHom) ≫ chartι W k) :
    projModelPointsEquiv W K s =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j) (Localization.Away (lawT k)))) ∘ lawT) := by
  classical
  set pmHom := chartAwayHomOfTriple W k (awayTriple W i j k lawT)
    (IsLocalization.Away.invSelf (lawT k)) (awayTriple_mul_invSelf W i j k lawT)
    (equation_awayTriple W i j k lawT hlaw) with hpmHom
  set φS : chartAway W k →+* K := ψ.comp pmHom.toRingHom with hφSdef
  have hS1 : Spec.map (CommRingCat.ofHom φS) ≫ chartι W k = s.1 := by
    rw [hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hπ : (Spec.map (CommRingCat.ofHom φS) ≫ chartι W k) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [hS1]; exact s.2
  have hφS : φS.comp (algebraMap R (chartAway W k)) = algebraMap R K :=
    chartHom_compat_of_specPoint W k φS hπ
  rw [Dictionary.eq_toAffine W k φS hφS s hS1]
  -- the triple is a unit multiple of χ∘lawT
  have hc1 : ψ ((algebraMap (biChartRing W i j) (Localization.Away (lawT k)))
      (lawT k)) * ψ (IsLocalization.Away.invSelf (lawT k)) = 1 := by
    rw [← map_mul, ← map_one ψ]
    congr 1
    exact awayTriple_mul_invSelf W i j k lawT
  have hcu : IsUnit (ψ (IsLocalization.Away.invSelf (lawT k))) :=
    ⟨⟨ψ (IsLocalization.Away.invSelf (lawT k)),
      ψ ((algebraMap (biChartRing W i j) (Localization.Away (lawT k))) (lawT k)),
      (mul_comm _ _).trans hc1, hc1⟩, rfl⟩
  have htriple : chartPointTriple W k φS =
      ψ (IsLocalization.Away.invSelf (lawT k)) •
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away (lawT k)))) ∘ lawT) := by
    funext m
    by_cases hm : m = k
    · subst hm
      rw [ChartPointTriple.self_eq_one]
      show (1 : K) = ψ (IsLocalization.Away.invSelf (lawT m)) *
        ψ ((algebraMap (biChartRing W i j) _) (lawT m))
      rw [mul_comm]
      exact hc1.symm
    · show φS (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m)) = _
      rw [hφSdef]
      show ψ (pmHom (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m))) = _
      rw [show (pmHom (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W k)
          (mk_X_mem_quotientGrading_one W (⟨m, hm⟩ : {l : Fin 3 // l ≠ k}).1))) =
        awayTriple W i j k lawT (⟨m, hm⟩ : {l : Fin 3 // l ≠ k}).1 *
          IsLocalization.Away.invSelf (lawT k) from
        chartAwayHomOfTriple_isLocalizationElem W k _ _ _ _ ⟨m, hm⟩]
      rw [map_mul]
      show _ = ψ (IsLocalization.Away.invSelf (lawT k)) *
        ψ ((algebraMap (biChartRing W i j) _) (lawT m))
      rw [awayTriple, mul_comm]
  rw [htriple]
  exact WeierstrassCurve.Projective.Point.toAffine_smul _ hcu

/-- [e5c-S, Z] The sum-point's dictionary value is `toAffine` of the law-1 triple image. -/
lemma Dictionary.sum_of_pieceZ (W : WeierstrassCurve R) [W.IsElliptic]
    [IsJacobsonRing R] (hΔ : IsUnit W.Δ) (i j k : Fin 3)
    [IsDomain (biChartRing W i j)]
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (s : SpecPoints (projModel W) (projModelπ W) K)
    (ψ : Localization.Away (lawOneTriple W i j k) →+* K)
    (hev : s.1 = Spec.map (CommRingCat.ofHom ψ) ≫ addOnZPieceMor W i j k hΔ) :
    projModelPointsEquiv W K s =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away (lawOneTriple W i j k)))) ∘ lawOneTriple W i j) := by
  exact Dictionary.sum_of_piece_aux W i j k s (lawOneTriple W i j)
    (equation_lawOneTriple_of_isDomain W i j hΔ) ψ hev

/-- [e5c-S, Y] The sum-point's dictionary value is `toAffine` of the law-2 triple image. -/
lemma Dictionary.sum_of_pieceY (W : WeierstrassCurve R) [W.IsElliptic]
    [IsJacobsonRing R] (hΔ : IsUnit W.Δ) (i j k : Fin 3)
    [IsDomain (biChartRing W i j)]
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (s : SpecPoints (projModel W) (projModelπ W) K)
    (ψ : Localization.Away (lawTwoTriple W i j k) →+* K)
    (hev : s.1 = Spec.map (CommRingCat.ofHom ψ) ≫ addOnYPieceMor W i j k hΔ) :
    projModelPointsEquiv W K s =
      WeierstrassCurve.Projective.Point.toAffine (W.map (algebraMap R K)).toProjective
        ((ψ.comp (algebraMap (biChartRing W i j)
          (Localization.Away (lawTwoTriple W i j k)))) ∘ lawTwoTriple W i j) := by
  exact Dictionary.sum_of_piece_aux W i j k s (lawTwoTriple W i j)
    (equation_lawTwoTriple_of_isDomain W i j hΔ) ψ hev

/-- [χ-compat, Z] The pair-ring evaluation is R-compatible (from P's π-condition through the
committed piece π-compat). -/
lemma chi_compat_of_pieceZ (W : WeierstrassCurve R) (i j k : Fin 3)
    {K : Type u} [Field K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W)
    (ψ : Localization.Away (lawOneTriple W i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k) :
    (ψ.comp (algebraMap (biChartRing W i j)
        (Localization.Away (lawOneTriple W i j k)))).comp
      (algebraMap R (biChartRing W i j)) = algebraMap R K := by
  have hπ : Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k ≫
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Category.assoc, ← hgp, ← Category.assoc, pullback.lift_fst]
    exact P.2
  rw [pieceAwayZι_fst_projModelπ W i j k, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at hπ
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_inj.mp hπ)
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  exact h2
/-- [χ-compat, Y] The pair-ring evaluation is R-compatible (from P's π-condition through the
committed piece π-compat). -/
lemma chi_compat_of_pieceY (W : WeierstrassCurve R) (i j k : Fin 3)
    {K : Type u} [Field K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W)
    (ψ : Localization.Away (lawTwoTriple W i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k) :
    (ψ.comp (algebraMap (biChartRing W i j)
        (Localization.Away (lawTwoTriple W i j k)))).comp
      (algebraMap R (biChartRing W i j)) = algebraMap R K := by
  have hπ : Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k ≫
      pullback.fst (projModelπ W) (projModelπ W) ≫ projModelπ W =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [← Category.assoc, ← hgp, ← Category.assoc, pullback.lift_fst]
    exact P.2
  rw [pieceAwayι_fst_projModelπ W i j k, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at hπ
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_inj.mp hπ)
  rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  exact h2

/-- The pair images are nonsingular over `K` (coordinate `1` at the chart index). -/
lemma nonsingular_chi_fst (W : WeierstrassCurve R) [W.IsElliptic] (i j : Fin 3)
    {K : Type u} [Field K] [Algebra R K] (χ : biChartRing W i j →+* K)
    (hχ : χ.comp (algebraMap R (biChartRing W i j)) = algebraMap R K) :
    (W.map (algebraMap R K)).toProjective.Nonsingular (χ ∘ biChartPointFst W i j) := by
  have : ((W.map (algebraMap R K)).toProjective).IsElliptic := by
    constructor; rw [map_Δ]; exact W.isUnit_Δ.map _
  have hEq : (W.map (algebraMap R K)).toProjective.Equation (χ ∘ biChartPointFst W i j) := by
    have h := (equation_biChartPointFst W i j).map χ
    rwa [show ((W.map (algebraMap R (biChartRing W i j))).toProjective.map χ) =
      (W.map (algebraMap R K)).toProjective from by
        show ((W.map (algebraMap R (biChartRing W i j))).map χ).toProjective = _
        rw [WeierstrassCurve.map_map, hχ]] at h
  refine WeierstrassCurve.Projective.nonsingular_of_equation_of_ne_zero hEq (fun h0 ↦ ?_)
  have h1 : χ (biChartPointFst W i j i) = 0 := congrFun h0 i
  rw [show biChartPointFst W i j i = 1 from dif_pos rfl, map_one] at h1
  exact one_ne_zero h1

/-- Mirror for the second point. -/
lemma nonsingular_chi_snd (W : WeierstrassCurve R) [W.IsElliptic] (i j : Fin 3)
    {K : Type u} [Field K] [Algebra R K] (χ : biChartRing W i j →+* K)
    (hχ : χ.comp (algebraMap R (biChartRing W i j)) = algebraMap R K) :
    (W.map (algebraMap R K)).toProjective.Nonsingular (χ ∘ biChartPointSnd W i j) := by
  have : ((W.map (algebraMap R K)).toProjective).IsElliptic := by
    constructor; rw [map_Δ]; exact W.isUnit_Δ.map _
  have hEq : (W.map (algebraMap R K)).toProjective.Equation (χ ∘ biChartPointSnd W i j) := by
    have h := (equation_biChartPointSnd W i j).map χ
    rwa [show ((W.map (algebraMap R (biChartRing W i j))).toProjective.map χ) =
      (W.map (algebraMap R K)).toProjective from by
        show ((W.map (algebraMap R (biChartRing W i j))).map χ).toProjective = _
        rw [WeierstrassCurve.map_map, hχ]] at h
  refine WeierstrassCurve.Projective.nonsingular_of_equation_of_ne_zero hEq (fun h0 ↦ ?_)
  have h1 : χ (biChartPointSnd W i j j) = 0 := congrFun h0 j
  rw [show biChartPointSnd W i j j = 1 from dif_pos rfl, map_one] at h1
  exact one_ne_zero h1

end DictionaryOfPiece

end ChartPointTriple

end ChartNaturality

section AtlasFormula

open WeierstrassCurve.Projective

variable {K : Type u} [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- [C6-e5a, Z] With the k-th law-1 coordinate a unit, the images are NOT projectively
equivalent, so the law-1 triple IS mathlib's `add`. -/
lemma descended_lawOne_eq_add (i j : Fin 3) (k : Fin 3)
    (χ : biChartRing universalWeierstrassLocU.{u} i j →+* K)
    (hunit : IsUnit (χ (lawOneTriple universalWeierstrassLocU.{u} i j k))) :
    χ ∘ lawOneTriple universalWeierstrassLocU.{u} i j =
      ((universalWeierstrassLocU.{u}.map
          (algebraMap WeierstrassAtlasRingU.{u} (biChartRing universalWeierstrassLocU.{u} i j))
        ).toProjective.map χ).add
        (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
        (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) := by
  rw [ringHom_lawOneTriple universalWeierstrassLocU.{u} i j χ]
  rw [WeierstrassCurve.Projective.add_of_not_equiv]
  intro heq
  rcases heq with ⟨u, hu⟩
  have hzero : ((universalWeierstrassLocU.{u}.map (algebraMap _ _)).toProjective.map χ).addXYZ
      ((u : K) • (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j))
      (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) = 0 := by
    rw [WeierstrassCurve.Projective.addXYZ_smul_left,
      WeierstrassCurve.Projective.addXYZ_self', smul_zero]
  have hu' : (⇑χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j : Fin 3 → K) =
      (u : K) • (⇑χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) := hu.symm
  have hk := congrFun (ringHom_lawOneTriple universalWeierstrassLocU.{u} i j χ) k
  rw [hu', hzero] at hk
  simp only [Function.comp_apply, Pi.zero_apply] at hk
  exact hunit.ne_zero hk

omit [DecidableEq K] in
/-- [C6-e5b, Y] The law-2 triple is `add` up to a unit square: on the diagonal it is
`u² • dblXYZ = u² • add`; off it the certified minors make it proportional to `addXYZ = add`. -/
lemma descended_lawTwo_smul_add (i j : Fin 3)
    [IsDomain (biChartRing universalWeierstrassLocU.{u} i j)] (k : Fin 3)
    (χ : biChartRing universalWeierstrassLocU.{u} i j →+* K)
    (hunit : IsUnit (χ (lawTwoTriple universalWeierstrassLocU.{u} i j k))) :
    ∃ c : K, c ≠ 0 ∧
      χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j =
        c • ((universalWeierstrassLocU.{u}.map
            (algebraMap WeierstrassAtlasRingU.{u}
              (biChartRing universalWeierstrassLocU.{u} i j))).toProjective.map χ).add
          (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
          (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) := by
  classical
  set WK := (universalWeierstrassLocU.{u}.map
    (algebraMap WeierstrassAtlasRingU.{u}
      (biChartRing universalWeierstrassLocU.{u} i j))).toProjective.map χ with hWK
  have hP : WK.Equation (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j) :=
    (equation_biChartPointFst universalWeierstrassLocU.{u} i j).map χ
  have hQ : WK.Equation (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) :=
    (equation_biChartPointSnd universalWeierstrassLocU.{u} i j).map χ
  have hlaw2 := ringHom_lawTwoTriple universalWeierstrassLocU.{u} i j χ
  by_cases hPQ : (⇑χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j : Fin 3 → K) ≈
      (⇑χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j)
  · rcases hPQ with ⟨c₀, hc₀⟩
    have hc₀' : (⇑χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j : Fin 3 → K) =
        (c₀ : K) • (⇑χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) := hc₀.symm
    refine ⟨((c₀ : K)⁻¹) ^ 2, by simp [c₀.ne_zero], ?_⟩
    rw [hlaw2, hc₀', WeierstrassCurve.Projective.dblAddXYZ_smul_left,
      WeierstrassCurve.Projective.dblAddXYZ_self hQ,
      WeierstrassCurve.Projective.add_of_equiv (by exact ⟨c₀, rfl⟩),
      WeierstrassCurve.Projective.dblXYZ_smul, smul_smul]
    congr 1
    field_simp
  · have hadd := WeierstrassCurve.Projective.add_of_not_equiv (W' := WK) hPQ
    have hNS : WK.Nonsingular (WK.add
        (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
        (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j)) := by
      have : WK.IsElliptic := by
        constructor
        rw [map_Δ, map_Δ]
        exact (universalWeierstrassLocU.{u}.isUnit_Δ.map _).map _
      refine WeierstrassCurve.Projective.nonsingular_add
        (WeierstrassCurve.Projective.nonsingular_of_equation_of_ne_zero hP ?_)
        (WeierstrassCurve.Projective.nonsingular_of_equation_of_ne_zero hQ ?_)
      · intro h0
        have h1 : χ (biChartPointFst universalWeierstrassLocU.{u} i j i) = 0 := congrFun h0 i
        rw [show biChartPointFst universalWeierstrassLocU.{u} i j i = 1 from dif_pos rfl,
          map_one] at h1
        exact one_ne_zero h1
      · intro h0
        have h1 : χ (biChartPointSnd universalWeierstrassLocU.{u} i j j) = 0 := congrFun h0 j
        rw [show biChartPointSnd universalWeierstrassLocU.{u} i j j = 1 from dif_pos rfl,
          map_one] at h1
        exact one_ne_zero h1
    rw [hadd] at hNS
    have h01 : (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 0 *
        WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
          (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 1 =
        (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 1 *
        WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
          (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 0 := by
      rw [hlaw2]
      simp only [WeierstrassCurve.Projective.dblAddXYZ_x, WeierstrassCurve.Projective.dblAddXYZ_y,
        WeierstrassCurve.Projective.addXYZ, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -(WeierstrassCurve.Projective.addX_mul_dblAddY (W' := WK) hP hQ)
    have h02 : (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 0 *
        WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
          (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 2 =
        (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 2 *
        WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
          (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 0 := by
      rw [hlaw2]
      simp only [WeierstrassCurve.Projective.dblAddXYZ_x, WeierstrassCurve.Projective.dblAddXYZ_z,
        WeierstrassCurve.Projective.addXYZ, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      linear_combination -(WeierstrassCurve.Projective.addX_mul_dblAddZ (W' := WK) hP hQ)
    have h12 : (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 1 *
        WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
          (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 2 =
        (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 2 *
        WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j)
          (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 1 := by
      rw [hlaw2]
      simp only [WeierstrassCurve.Projective.dblAddXYZ_y, WeierstrassCurve.Projective.dblAddXYZ_z,
        WeierstrassCurve.Projective.addXYZ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      linear_combination -(WeierstrassCurve.Projective.addY_mul_dblAddZ (W' := WK) hP hQ)
    obtain ⟨c, hc⟩ := exists_eq_smul_of_cross_eq_zero hNS.ne_zero h01 h02 h12
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      have hk := congrFun hc k
      simp only [Pi.zero_apply] at hk
      exact hunit.ne_zero hk
    refine ⟨c, hc0, ?_⟩
    rw [hc, hadd]

/-- Shared prefix of `specPoints_arm_{Z,Y}` (the `hcurve` step): an `R`-compatible evaluation `χ`
transports the projective model over the intermediate ring to the one over `K`
(`map_map` + `hχ`). -/
private lemma toProjective_map_comp_algebraMap {A : Type u} [CommRing A] (W : WeierstrassCurve A)
    {B : Type u} [CommRing B] {K : Type u} [CommRing K] [Algebra A K]
    (f : A →+* B) (χ : B →+* K) (hχ : χ.comp f = algebraMap A K) :
    (W.map f).toProjective.map χ = (W.map (algebraMap A K)).toProjective := by
  show ((W.map f).map χ).toProjective = _
  rw [WeierstrassCurve.map_map, hχ]

/-- Shared prefix of `specPoints_arm_{Z,Y}` (the `hunit` step): the base-changed evaluation of the
`k`-th law-triple coordinate is a unit, inverted by the image of the localization's own inverse. -/
private lemma isUnit_comp_lawTriple (i j k : Fin 3)
    (lawT : Fin 3 → biChartRing universalWeierstrassLocU.{u} i j)
    {K : Type u} [CommRing K]
    (ψ : Localization.Away (lawT k) →+* K) :
    IsUnit ((ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawT k)))) (lawT k)) := by
  refine ⟨⟨(ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawT k)))) (lawT k),
    ψ (IsLocalization.Away.invSelf (lawT k)), ?_, ?_⟩, rfl⟩ <;>
  · first
    | (rw [RingHom.comp_apply, ← map_mul, ← map_one ψ]
       congr 1
       exact awayTriple_mul_invSelf universalWeierstrassLocU.{u} i j k lawT)
    | (rw [RingHom.comp_apply, mul_comm, ← map_mul, ← map_one ψ]
       congr 1
       exact awayTriple_mul_invSelf universalWeierstrassLocU.{u} i j k lawT)

/-- [e5c ARM, Z] The complete per-piece assembly at the atlas: sum = P + Q. -/
lemma SpecPoint.arm_Z {K : Type u} [Field K] [DecidableEq K]
    [Algebra WeierstrassAtlasRingU.{u} K]
    (P Q : SpecPoints (projModel universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) K)
    (w : P.1 ≫ projModelπ universalWeierstrassLocU.{u} =
      Q.1 ≫ projModelπ universalWeierstrassLocU.{u})
    (i j : Fin 3) [IsDomain (biChartRing universalWeierstrassLocU.{u} i j)] (k : Fin 3)
    (ψ : Localization.Away (lawOneTriple universalWeierstrassLocU.{u} i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫
      pieceAwayZι universalWeierstrassLocU.{u} i j k)
    (s : SpecPoints (projModel universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) K)
    (hev : s.1 = Spec.map (CommRingCat.ofHom ψ) ≫
      addOnZPieceMor universalWeierstrassLocU.{u} i j k universalWeierstrassLocU.isUnit_Δ) :
    projModelPointsEquiv universalWeierstrassLocU.{u} K s =
      projModelPointsEquiv universalWeierstrassLocU.{u} K P +
        projModelPointsEquiv universalWeierstrassLocU.{u} K Q := by
  classical

  have hχ : (ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawOneTriple universalWeierstrassLocU.{u} i j k)))).comp
      (algebraMap (WeierstrassAtlasRingU.{u})
      (biChartRing universalWeierstrassLocU.{u} i j)) = algebraMap _ K :=
    chi_compat_of_pieceZ universalWeierstrassLocU.{u} i j k P Q w ψ hgp
  have hcurve : ((universalWeierstrassLocU.{u}.map
      (algebraMap (WeierstrassAtlasRingU.{u})
        (biChartRing universalWeierstrassLocU.{u} i j))).toProjective.map
      (ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
        (Localization.Away (lawOneTriple universalWeierstrassLocU.{u} i j k))))) =
      (universalWeierstrassLocU.{u}.map (algebraMap _ K)).toProjective :=
    toProjective_map_comp_algebraMap universalWeierstrassLocU.{u} _ _ hχ
  have hunit : IsUnit ((ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawOneTriple universalWeierstrassLocU.{u} i j k))))
      (lawOneTriple universalWeierstrassLocU.{u} i j k)) :=
    isUnit_comp_lawTriple i j k (lawOneTriple universalWeierstrassLocU.{u} i j) ψ
  have he5a := descended_lawOne_eq_add i j k
    (ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawOneTriple universalWeierstrassLocU.{u} i j k)))) hunit
  rw [hcurve] at he5a
  rw [Dictionary.sum_of_pieceZ universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ i j k s ψ hev]
  rw [he5a]
  rw [WeierstrassCurve.Projective.Point.toAffine_add
    (nonsingular_chi_fst universalWeierstrassLocU.{u} i j _ hχ)
    (nonsingular_chi_snd universalWeierstrassLocU.{u} i j _ hχ)]
  rw [← Dictionary.fst_of_pieceZ universalWeierstrassLocU.{u} i j k P Q w ψ hgp,
    ← Dictionary.snd_of_pieceZ universalWeierstrassLocU.{u} i j k P Q w ψ hgp]
  rfl
/-- [e5c ARM, Y] The complete per-piece assembly at the atlas: sum = P + Q. -/
lemma SpecPoint.arm_Y {K : Type u} [Field K] [DecidableEq K]
    [Algebra WeierstrassAtlasRingU.{u} K]
    (P Q : SpecPoints (projModel universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) K)
    (w : P.1 ≫ projModelπ universalWeierstrassLocU.{u} =
      Q.1 ≫ projModelπ universalWeierstrassLocU.{u})
    (i j : Fin 3) [IsDomain (biChartRing universalWeierstrassLocU.{u} i j)] (k : Fin 3)
    (ψ : Localization.Away (lawTwoTriple universalWeierstrassLocU.{u} i j k) →+* K)
    (hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫
      pieceAwayι universalWeierstrassLocU.{u} i j k)
    (s : SpecPoints (projModel universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) K)
    (hev : s.1 = Spec.map (CommRingCat.ofHom ψ) ≫
      addOnYPieceMor universalWeierstrassLocU.{u} i j k universalWeierstrassLocU.isUnit_Δ) :
    projModelPointsEquiv universalWeierstrassLocU.{u} K s =
      projModelPointsEquiv universalWeierstrassLocU.{u} K P +
        projModelPointsEquiv universalWeierstrassLocU.{u} K Q := by
  classical

  have hχ : (ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawTwoTriple universalWeierstrassLocU.{u} i j k)))).comp
      (algebraMap (WeierstrassAtlasRingU.{u})
      (biChartRing universalWeierstrassLocU.{u} i j)) = algebraMap _ K :=
    chi_compat_of_pieceY universalWeierstrassLocU.{u} i j k P Q w ψ hgp
  have hcurve : ((universalWeierstrassLocU.{u}.map
      (algebraMap (WeierstrassAtlasRingU.{u})
        (biChartRing universalWeierstrassLocU.{u} i j))).toProjective.map
      (ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
        (Localization.Away (lawTwoTriple universalWeierstrassLocU.{u} i j k))))) =
      (universalWeierstrassLocU.{u}.map (algebraMap _ K)).toProjective :=
    toProjective_map_comp_algebraMap universalWeierstrassLocU.{u} _ _ hχ
  have hunit : IsUnit ((ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawTwoTriple universalWeierstrassLocU.{u} i j k))))
      (lawTwoTriple universalWeierstrassLocU.{u} i j k)) :=
    isUnit_comp_lawTriple i j k (lawTwoTriple universalWeierstrassLocU.{u} i j) ψ
  obtain ⟨c, hc0, he5b⟩ := descended_lawTwo_smul_add i j k
    (ψ.comp (algebraMap (biChartRing universalWeierstrassLocU.{u} i j)
      (Localization.Away (lawTwoTriple universalWeierstrassLocU.{u} i j k)))) hunit
  rw [hcurve] at he5b
  rw [Dictionary.sum_of_pieceY universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ i j k s ψ hev]
  rw [he5b, WeierstrassCurve.Projective.Point.toAffine_smul _ (isUnit_iff_ne_zero.mpr hc0)]
  rw [WeierstrassCurve.Projective.Point.toAffine_add
    (nonsingular_chi_fst universalWeierstrassLocU.{u} i j _ hχ)
    (nonsingular_chi_snd universalWeierstrassLocU.{u} i j _ hχ)]
  rw [← Dictionary.fst_of_pieceY universalWeierstrassLocU.{u} i j k P Q w ψ hgp,
    ← Dictionary.snd_of_pieceY universalWeierstrassLocU.{u} i j k P Q w ψ hgp]
  rfl

/-- Shared assembler for the four law-1 (Z) arms of `mulModelHom_specPoints_atlas`: given the
image-form factorisation `hh₁` of a piece and its multiplication-evaluation `hmul`, descend through
`SpecPoint.factors_addOnZImage` and finish via `SpecPoint.arm_Z`. -/
private lemma mulModelHom_specPoints_atlas_armZ {K : Type u} [Field K] [DecidableEq K]
    [Algebra WeierstrassAtlasRingU.{u} K]
    (P Q : SpecPoints (projModel universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) K)
    (w : P.1 ≫ projModelπ universalWeierstrassLocU.{u} =
      Q.1 ≫ projModelπ universalWeierstrassLocU.{u})
    (i j : Fin 3) [IsDomain (biChartRing universalWeierstrassLocU.{u} i j)]
    (h₁ : Spec (CommRingCat.of K) ⟶
      (blOpenZImage universalWeierstrassLocU.{u} i j).toScheme)
    (hh₁ : h₁ ≫ (blOpenZImage universalWeierstrassLocU.{u} i j).ι = pullback.lift P.1 Q.1 w)
    (hmul : pullback.lift P.1 Q.1 w ≫ WeierstrassCurve.Projective.mulModelHom
          universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ =
        h₁ ≫ addOnZOnImage universalWeierstrassLocU.{u}
          universalWeierstrassLocU.isUnit_Δ i j) :
    projModelPointsEquiv universalWeierstrassLocU.{u} K
        ⟨pullback.lift P.1 Q.1 w ≫
            WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
              universalWeierstrassLocU.isUnit_Δ, by
          rw [Category.assoc, WeierstrassCurve.Projective.mulModelHom_projModelπ,
            ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv universalWeierstrassLocU.{u} K P +
        projModelPointsEquiv universalWeierstrassLocU.{u} K Q := by
  classical
  obtain ⟨k, ψ, hev₂, himm⟩ := SpecPoint.factors_addOnZImage
    universalWeierstrassLocU.{u} i j universalWeierstrassLocU.isUnit_Δ h₁
  have hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫
      pieceAwayZι universalWeierstrassLocU.{u} i j k := by
    rw [himm]
    exact hh₁.symm
  refine SpecPoint.arm_Z P Q w i j k ψ hgp _ ?_
  show pullback.lift P.1 Q.1 w ≫ WeierstrassCurve.Projective.mulModelHom
      universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ = _
  exact hmul.trans hev₂

/-- Shared assembler for the four law-2 (Y) arms of `mulModelHom_specPoints_atlas`: the mirror of
`mulModelHom_specPoints_atlas_armZ`, descending through `SpecPoint.factors_addOnYImage` and
finishing via `SpecPoint.arm_Y`. -/
private lemma mulModelHom_specPoints_atlas_armY {K : Type u} [Field K] [DecidableEq K]
    [Algebra WeierstrassAtlasRingU.{u} K]
    (P Q : SpecPoints (projModel universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) K)
    (w : P.1 ≫ projModelπ universalWeierstrassLocU.{u} =
      Q.1 ≫ projModelπ universalWeierstrassLocU.{u})
    (i j : Fin 3) [IsDomain (biChartRing universalWeierstrassLocU.{u} i j)]
    (h₁ : Spec (CommRingCat.of K) ⟶
      (blOpenYImage universalWeierstrassLocU.{u} i j).toScheme)
    (hh₁ : h₁ ≫ (blOpenYImage universalWeierstrassLocU.{u} i j).ι = pullback.lift P.1 Q.1 w)
    (hmul : pullback.lift P.1 Q.1 w ≫ WeierstrassCurve.Projective.mulModelHom
          universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ =
        h₁ ≫ addOnYOnImage universalWeierstrassLocU.{u}
          universalWeierstrassLocU.isUnit_Δ i j) :
    projModelPointsEquiv universalWeierstrassLocU.{u} K
        ⟨pullback.lift P.1 Q.1 w ≫
            WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
              universalWeierstrassLocU.isUnit_Δ, by
          rw [Category.assoc, WeierstrassCurve.Projective.mulModelHom_projModelπ,
            ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv universalWeierstrassLocU.{u} K P +
        projModelPointsEquiv universalWeierstrassLocU.{u} K Q := by
  classical
  obtain ⟨k, ψ, hev₂, himm⟩ := SpecPoint.factors_addOnYImage
    universalWeierstrassLocU.{u} i j universalWeierstrassLocU.isUnit_Δ h₁
  have hgp : pullback.lift P.1 Q.1 w = Spec.map (CommRingCat.ofHom ψ) ≫
      pieceAwayι universalWeierstrassLocU.{u} i j k := by
    rw [himm]
    exact hh₁.symm
  refine SpecPoint.arm_Y P Q w i j k ψ hgp _ ?_
  show pullback.lift P.1 Q.1 w ≫ WeierstrassCurve.Projective.mulModelHom
      universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ = _
  exact hmul.trans hev₂

/-- **[C6-e5c] The atlas-level specPoints spec** (the c6 core): over the ULift universal atlas the
glued two-law multiplication computes the group law of the dictionary. Proof plan (v10.94f/g):
case split via SpecPoint.factors_blOpen; per case descend by
specPoint_addOn{Z,Y}OnImage_factors' + read out by addOn{Z,Y}PieceHom_coord/tensor legs/piece
projections; identify the triple with `add` by descended_lawOne_eq_add / descended_lawTwo_smul_add;
finish with toAffine_add + toAffine_smul + projModelPointsEquiv_some/_zero. -/
theorem mulModelHom_specPoints_atlas {K : Type u} [Field K] [DecidableEq K]
    [Algebra WeierstrassAtlasRingU.{u} K]
    (P Q : SpecPoints (projModel universalWeierstrassLocU.{u})
      (projModelπ universalWeierstrassLocU.{u}) K)
    (w : P.1 ≫ projModelπ universalWeierstrassLocU.{u} =
      Q.1 ≫ projModelπ universalWeierstrassLocU.{u}) :
    projModelPointsEquiv universalWeierstrassLocU.{u} K
        ⟨pullback.lift P.1 Q.1 w ≫
            WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
              universalWeierstrassLocU.isUnit_Δ, by
          rw [Category.assoc, WeierstrassCurve.Projective.mulModelHom_projModelπ,
            ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv universalWeierstrassLocU.{u} K P +
        projModelPointsEquiv universalWeierstrassLocU.{u} K Q := by
  classical
  rcases SpecPoint.factors_blOpen universalWeierstrassLocU.{u} K
    (pullback.lift P.1 Q.1 w) with ⟨h₀, hh₀⟩ | ⟨h₀, hh₀⟩
  · -- law-1 (Z) case
    obtain ⟨p, h₁, hfam, heval⟩ := SpecPoint.addOnZ_family universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ h₀
    fin_cases p
    · refine mulModelHom_specPoints_atlas_armZ P Q w 1 1 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenZ_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))
    · refine mulModelHom_specPoints_atlas_armZ P Q w 1 2 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenZ_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))
    · refine mulModelHom_specPoints_atlas_armZ P Q w 2 1 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenZ_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))
    · refine mulModelHom_specPoints_atlas_armZ P Q w 2 2 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenZ_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))
  · -- law-2 (Y) case
    obtain ⟨p, h₁, hfam, heval⟩ := SpecPoint.addOnY_family universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ h₀
    fin_cases p
    · refine mulModelHom_specPoints_atlas_armY P Q w 1 1 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenY_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))
    · refine mulModelHom_specPoints_atlas_armY P Q w 1 2 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenY_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))
    · refine mulModelHom_specPoints_atlas_armY P Q w 2 1 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenY_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))
    · refine mulModelHom_specPoints_atlas_armY P Q w 2 2 h₁ ?_ ?_
      · rw [← hh₀, ← hfam]
        exact ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (Scheme.homOfLE_ι _ _))).symm
      · exact (congrArg (· ≫ WeierstrassCurve.Projective.mulModelHom
              universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ) hh₀.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (h₀ ≫ ·)
              (WeierstrassCurve.Projective.blOpenY_ι_mulModelHom universalWeierstrassLocU.{u}
                universalWeierstrassLocU.isUnit_Δ)).trans heval))

section DictionaryNaturality

open WeierstrassCurve.Projective HomogeneousIdeal HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- [e4b] The `eqToHom`-cast of an `Away`-ring along a generator equality carries the
localization coordinates (proof-irrelevant memberships; `subst`).

ForMathlib candidate: a general graded-ring statement, with no elliptic-curve content. -/
lemma eqToHom_hom_isLocalizationElem {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {s t : A} (h : s = t)
    (hs : s ∈ 𝒜 1) (ht : t ∈ 𝒜 1) {g : A} (hg : g ∈ 𝒜 1) :
    (CommRingCat.Hom.hom (eqToHom (congrArg
        (fun x ↦ CommRingCat.of (HomogeneousLocalization.Away 𝒜 x)) h)))
      (HomogeneousLocalization.Away.isLocalizationElem hs hg) =
      HomogeneousLocalization.Away.isLocalizationElem ht hg := by
  subst h
  rfl

variable {U : Type u} [CommRing U]

/-- [e4c] `isLocalizationElem` transported along an equality of the numerator generator.

ForMathlib candidate: a general graded-ring statement, with no elliptic-curve content. -/
lemma isLocalizationElem_congr_right {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {s : A} (hs : s ∈ 𝒜 1)
    {g₁ g₂ : A} (h : g₁ = g₂) (hg₁ : g₁ ∈ 𝒜 1) (hg₂ : g₂ ∈ 𝒜 1) :
    HomogeneousLocalization.Away.isLocalizationElem hs hg₁ =
      HomogeneousLocalization.Away.isLocalizationElem hs hg₂ := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **[D-NAT] Dictionary naturality along base change**: the dictionary of a point over the
base-changed curve equals the dictionary of its push to the base (the affine target curves are
definitionally equal through `map_map` and the composite algebra). -/
lemma Dictionary.baseChange (f : U →+* R) (W₀ : WeierstrassCurve U)
    [W₀.IsElliptic] [(W₀.map f).IsElliptic]
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (x : SpecPoints (projModel (W₀.map f)) (projModelπ (W₀.map f)) K) :
    letI : Algebra U K := ((algebraMap R K).comp f).toAlgebra
    projModelPointsEquiv (W₀.map f) K x =
      projModelPointsEquiv W₀ K ⟨x.1 ≫ projModelBaseChange f W₀, by
        rw [Category.assoc]
        letI : Algebra U R := f.toAlgebra
        rw [show projModelBaseChange f W₀ ≫ projModelπ W₀ =
          projModelπ (W₀.map f) ≫ Spec.map (CommRingCat.ofHom f) from
          projModelBaseChange_π f W₀]
        rw [← Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩ := by
  classical
  letI : Algebra U K := ((algebraMap R K).comp f).toAlgebra
  by_cases hZ : InZChart (W₀.map f) x
  · obtain ⟨h', hh'⟩ := hZ
    have hx1 : Spec.map (CommRingCat.ofHom (CommRingCat.Hom.hom (Spec.preimage h'))) ≫
        chartι (W₀.map f) 2 = x.1 := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
      exact hh'
    set φ : chartAway (W₀.map f) 2 →+* K := CommRingCat.Hom.hom (Spec.preimage h') with hφdef
    have hφc : φ.comp (algebraMap R (chartAway (W₀.map f) 2)) = algebraMap R K :=
      chartHom_compat_of_specPoint (W₀.map f) 2 φ (by rw [hx1]; exact x.2)
    rw [Dictionary.eq_toAffine (W₀.map f) 2 φ hφc x hx1]
    have e : CommRingCat.of (HomogeneousLocalization.Away
        (quotientGrading (projIdeal (W₀.map f)))
        (baseChangeGradedHom f W₀
          ((quotientGradingHom (projIdeal W₀)) (MvPolynomial.X 2)))) =
        CommRingCat.of (chartAway (W₀.map f) 2) := by
      rw [baseChangeGradedHom_chartGen f W₀ 2]
    have hpush : Spec.map (CommRingCat.ofHom ((φ.comp
        (CommRingCat.Hom.hom (eqToHom e))).comp (bcChartAwayMap f W₀ 2))) ≫
        chartι W₀ 2 = x.1 ≫ projModelBaseChange f W₀ := by
      rw [← specMap_chartι_comp_baseChange f W₀ 2 φ e, hx1]
    have hφ₂c : ((φ.comp (CommRingCat.Hom.hom (eqToHom e))).comp
        (bcChartAwayMap f W₀ 2)).comp (algebraMap U (chartAway W₀ 2)) = algebraMap U K :=
      chartHom_compat_of_specPoint W₀ 2 _ (by
        rw [hpush, Category.assoc]
        letI : Algebra U R := f.toAlgebra
        rw [show projModelBaseChange f W₀ ≫ projModelπ W₀ =
          projModelπ (W₀.map f) ≫ Spec.map (CommRingCat.ofHom f) from
          projModelBaseChange_π f W₀]
        rw [← Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    rw [Dictionary.eq_toAffine W₀ 2 _ hφ₂c _ hpush]
    congr 1
    funext m
    show chartPointTriple (W₀.map f) 2 φ m = ((φ.comp
      (CommRingCat.Hom.hom (eqToHom e))).comp (bcChartAwayMap f W₀ 2))
        (HomogeneousLocalization.Away.isLocalizationElem
          (mk_X_mem_quotientGrading_one W₀ 2) (mk_X_mem_quotientGrading_one W₀ m))
    rw [RingHom.comp_apply, bcChartAwayMap_isLocalizationElem f W₀ 2 m,
      RingHom.comp_apply, eqToHom_hom_isLocalizationElem _
        (baseChangeGradedHom_chartGen f W₀ 2) _ (mk_X_mem_quotientGrading_one (W₀.map f) 2)]
    exact (congrArg φ (isLocalizationElem_congr_right
      (mk_X_mem_quotientGrading_one (W₀.map f) 2)
      (baseChangeGradedHom_chartGen f W₀ m)
      ((baseChangeGradedHom f W₀).2 (mk_X_mem_quotientGrading_one W₀ m))
      (mk_X_mem_quotientGrading_one (W₀.map f) m))).symm
  · have hx0 := specPoint_eq_zero_of_not_inZ (W₀.map f) K x hZ
    have hLHS : projModelPointsEquiv (W₀.map f) K x = 0 := by
      rw [← projModelPointsEquiv_zero (W₀.map f) K]
      exact congrArg (projModelPointsEquiv (W₀.map f) K) (Subtype.ext hx0)
    rw [hLHS]
    have hpz : x.1 ≫ projModelBaseChange f W₀ =
        Spec.map (CommRingCat.ofHom (algebraMap U K)) ≫ projModelZero W₀ := by
      rw [hx0, Category.assoc]
      letI : Algebra U R := f.toAlgebra
      rw [show projModelZero (W₀.map f) ≫ projModelBaseChange f W₀ =
        Spec.map (CommRingCat.ofHom f) ≫ projModelZero W₀ from projModelZero_baseChange W₀]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (⟨x.1 ≫ projModelBaseChange f W₀, _⟩ :
        SpecPoints (projModel W₀) (projModelπ W₀) K) =
      ⟨Spec.map (CommRingCat.ofHom (algebraMap U K)) ≫ projModelZero W₀, by
        rw [Category.assoc, projModelZero_projModelπ, Category.comp_id]⟩ from
      Subtype.ext hpz]
    exact (projModelPointsEquiv_zero W₀ K).symm

end DictionaryNaturality

end AtlasFormula

/-- **[C6-U] THE ATLAS BRIDGE** — over the ULift universal atlas, GLC's base-change
multiplication IS the glued two-law multiplication. -/
theorem mulModelHom_universalWeierstrassLocU :
    mulModelHom universalWeierstrassLocU.{u} =
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
  rw [mulModelHom]
  rw [mulModelHomBC_congr (classifyRingHomU universalWeierstrassLocU.{u})
    (RingHom.id _) classifyRingHomU_universalWeierstrassLocU
    universalWeierstrassLocU universalWeierstrassLocU.isUnit_Δ
    universalWeierstrassLocU (universalWeierstrassLocU_map_classifyRingHomU _) rfl]
  exact mulModelHomBC_id universalWeierstrassLocU universalWeierstrassLocU.isUnit_Δ

section OfMap

variable {R : Type u} [CommRing R]

/-- The multiplication at a mapped curve is the `f`-form base-change lift (classify collapses). -/
lemma mulModelHom_map_eq_BC (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic] :
    mulModelHom (universalWeierstrassLocU.{u}.map f) =
      mulModelHomBC f universalWeierstrassLocU.{u} universalWeierstrassLocU.isUnit_Δ
        (universalWeierstrassLocU.{u}.map f) rfl := by
  rw [mulModelHom]
  refine mulModelHomBC_congr _ f ?_ universalWeierstrassLocU.{u}
    universalWeierstrassLocU.isUnit_Δ (universalWeierstrassLocU.{u}.map f) _ rfl
  rw [classifyRingHomU_map f universalWeierstrassLocU.{u},
    classifyRingHomU_universalWeierstrassLocU, RingHom.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-- The c6 spec at a mapped curve: transported from the atlas by D-NAT + the f-form push. -/
theorem mulModelHom_specPoints_of_map (f : WeierstrassAtlasRingU.{u} →+* R)
    [(universalWeierstrassLocU.{u}.map f).IsElliptic]
    (K : Type u) [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel (universalWeierstrassLocU.{u}.map f))
      (projModelπ (universalWeierstrassLocU.{u}.map f)) K)
    (w : P.1 ≫ projModelπ (universalWeierstrassLocU.{u}.map f) =
      Q.1 ≫ projModelπ (universalWeierstrassLocU.{u}.map f)) :
    projModelPointsEquiv (universalWeierstrassLocU.{u}.map f) K
        ⟨pullback.lift P.1 Q.1 w ≫ mulModelHom (universalWeierstrassLocU.{u}.map f), by
          rw [Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv (universalWeierstrassLocU.{u}.map f) K P +
        projModelPointsEquiv (universalWeierstrassLocU.{u}.map f) K Q := by
  classical
  letI : Algebra (WeierstrassAtlasRingU.{u}) K := ((algebraMap R K).comp f).toAlgebra
  rw [Dictionary.baseChange f universalWeierstrassLocU.{u} P,
    Dictionary.baseChange f universalWeierstrassLocU.{u} Q,
    Dictionary.baseChange f universalWeierstrassLocU.{u} _]
  -- identify the pushed sum with the atlas-level sum of the pushed pair
  have hw' : (P.1 ≫ projModelBaseChange f universalWeierstrassLocU.{u}) ≫
      projModelπ universalWeierstrassLocU.{u} =
      (Q.1 ≫ projModelBaseChange f universalWeierstrassLocU.{u}) ≫
      projModelπ universalWeierstrassLocU.{u} := by
    letI : Algebra (WeierstrassAtlasRingU.{u}) R := f.toAlgebra
    rw [Category.assoc, Category.assoc,
      show projModelBaseChange f universalWeierstrassLocU.{u} ≫
        projModelπ universalWeierstrassLocU.{u} =
        projModelπ (universalWeierstrassLocU.{u}.map f) ≫ Spec.map (CommRingCat.ofHom f) from
        projModelBaseChange_π f universalWeierstrassLocU.{u},
      ← Category.assoc, ← Category.assoc, w]
  have hBC : mulModelHomBC f universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ (universalWeierstrassLocU.{u}.map f) rfl ≫
      projModelBaseChange f universalWeierstrassLocU.{u} =
      pullbackMapBaseChangeOf f universalWeierstrassLocU.{u}
        (universalWeierstrassLocU.{u}.map f) rfl ≫
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
    rw [← projModelBaseChangeOf_rfl f universalWeierstrassLocU.{u}]
    exact mulModelHomBC_baseChange f universalWeierstrassLocU.{u}
      universalWeierstrassLocU.isUnit_Δ (universalWeierstrassLocU.{u}.map f) rfl
  have hpush : (pullback.lift P.1 Q.1 w ≫ mulModelHom (universalWeierstrassLocU.{u}.map f)) ≫
      projModelBaseChange f universalWeierstrassLocU.{u} =
      pullback.lift (P.1 ≫ projModelBaseChange f universalWeierstrassLocU.{u})
        (Q.1 ≫ projModelBaseChange f universalWeierstrassLocU.{u}) hw' ≫
        WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
          universalWeierstrassLocU.isUnit_Δ := by
    rw [mulModelHom_map_eq_BC f, Category.assoc, hBC, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [pullbackMapBaseChangeOf]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [projModelBaseChangeOf_rfl]
    · rw [pullbackMapBaseChangeOf]
      simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [projModelBaseChangeOf_rfl]
  refine Eq.trans (congrArg (projModelPointsEquiv universalWeierstrassLocU.{u} K)
    (Subtype.ext ?_))
    (mulModelHom_specPoints_atlas
      ⟨P.1 ≫ projModelBaseChange f universalWeierstrassLocU.{u}, ?_⟩
      ⟨Q.1 ≫ projModelBaseChange f universalWeierstrassLocU.{u}, ?_⟩ hw')
  · exact hpush
  · rw [Category.assoc]
    letI : Algebra (WeierstrassAtlasRingU.{u}) R := f.toAlgebra
    rw [show projModelBaseChange f universalWeierstrassLocU.{u} ≫
        projModelπ universalWeierstrassLocU.{u} =
        projModelπ (universalWeierstrassLocU.{u}.map f) ≫ Spec.map (CommRingCat.ofHom f) from
        projModelBaseChange_π f universalWeierstrassLocU.{u}]
    rw [← Category.assoc, P.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rw [Category.assoc]
    letI : Algebra (WeierstrassAtlasRingU.{u}) R := f.toAlgebra
    rw [show projModelBaseChange f universalWeierstrassLocU.{u} ≫
        projModelπ universalWeierstrassLocU.{u} =
        projModelπ (universalWeierstrassLocU.{u}.map f) ≫ Spec.map (CommRingCat.ofHom f) from
        projModelBaseChange_π f universalWeierstrassLocU.{u}]
    rw [← Category.assoc, Q.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- The c6 spec against an equality witness `universalWeierstrassLocU.map f = W`: the
`subst`-friendly form (`f` and `W` independent, tied only by `h`), so instantiating at
`f := classifyRingHomU W`, `h := universalWeierstrassLocU_map_classifyRingHomU W` yields
the spec for EVERY elliptic `W` with no dependent-rewrite pain. -/
theorem mulModelHom_specPoints_of_eq (f : WeierstrassAtlasRingU.{u} →+* R)
    (W : WeierstrassCurve R) [W.IsElliptic] (h : universalWeierstrassLocU.{u}.map f = W)
    (K : Type u) [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W) :
    projModelPointsEquiv W K
        ⟨pullback.lift P.1 Q.1 w ≫ mulModelHom W, by
          rw [Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv W K P + projModelPointsEquiv W K Q := by
  subst h
  exact mulModelHom_specPoints_of_map f K P Q w

/-- **(T-W7.0c·c6, THE SPEC — [C6] COMPLETE)** On field points, `mulModelHom` is mathlib's
`Point.add` through the dictionary — for EVERY pair over EVERY ring (the B–L laws compute
the chord–tangent sum wherever each is defined, the two opens cover, and base change
transports the universal atlas case). This single spec is what every group axiom consumes.
Source: B–L Thm 2 ("addition law" = computes the sum in `E(K)`); mathlib
`Affine.Point.add`; §5 formulas vs `Affine.slope`/`addX`/`addY` on the secant locus. -/
theorem mulModelHom_specPoints (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K
        ⟨pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W, by
          rw [Category.assoc, mulModelHom_π, ← Category.assoc, pullback.lift_fst, P.2]⟩ =
      projModelPointsEquiv W K P + projModelPointsEquiv W K Q :=
  mulModelHom_specPoints_of_eq (classifyRingHomU W) W
    (universalWeierstrassLocU_map_classifyRingHomU W) K P Q (P.2.trans Q.2.symm)

end OfMap

end ModularCurves
