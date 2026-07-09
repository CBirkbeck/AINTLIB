import ModularCurves.EllipticCurve.GroupLawConstruction

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

/-- [C6-a'] A field-valued point of an `iSup`-of-opens subscheme factors through one of the
members: the unique point of `Spec K` lies in some member, and the member inclusion is an open
immersion. -/
theorem specPoint_factors_iSup {X : Scheme.{u}} {ι : Type*} (U : ι → X.Opens)
    (K : Type u) [Field K] (g : Spec (CommRingCat.of K) ⟶ (⨆ i, U i).toScheme) :
    ∃ (i : ι) (h : Spec (CommRingCat.of K) ⟶ (U i).toScheme),
      h ≫ X.homOfLE (le_iSup U i) = g := by
  have hmem : (⨆ i, U i).ι.base (g.base default) ∈ (⨆ i, U i : X.Opens) := by
    have h1 : (⨆ i, U i).ι.base (g.base default) ∈ Set.range (⨆ i, U i).ι.base := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at h1
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨i, IsOpenImmersion.lift (X.homOfLE (le_iSup U i)) g ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rw [Set.range_unique (f := g.base)]
  refine Set.singleton_subset_iff.mpr ?_
  have hor : (X.homOfLE (le_iSup U i)).opensRange =
      (⨆ j, U j).ι ⁻¹ᵁ (U i) := Scheme.opensRange_homOfLE _
  have : g.base default ∈ (X.homOfLE (le_iSup U i)).opensRange := by
    rw [hor]
    exact hi
  exact this
/-- [C6-a] A field-valued point of `E ×_R E` factors through `blOpenZ` or `blOpenY`. -/
theorem specPoint_factors_blOpenZ_or_blOpenY (W : WeierstrassCurve R) [W.IsElliptic]
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

/-- [C6-b, Z] Through a blOpenZ factorisation, `mulModelHom` evaluates as `addOnZ`. -/
theorem specPoint_mulModelHom_of_blOpenZ (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [CommRing K]
    {g : Spec (CommRingCat.of K) ⟶ pullback (projModelπ W) (projModelπ W)}
    {h : Spec (CommRingCat.of K) ⟶ (blOpenZ W).toScheme} (hh : h ≫ (blOpenZ W).ι = g) :
    g ≫ mulModelHom W = h ≫ addOnZ W := by
  rw [← hh, Category.assoc, blOpenZ_ι_mulModelHom]

/-- [C6-b, Y] Mirror. -/
theorem specPoint_mulModelHom_of_blOpenY (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [CommRing K]
    {g : Spec (CommRingCat.of K) ⟶ pullback (projModelπ W) (projModelπ W)}
    {h : Spec (CommRingCat.of K) ⟶ (blOpenY W).toScheme} (hh : h ≫ (blOpenY W).ι = g) :
    g ≫ mulModelHom W = h ≫ addOnY W := by
  rw [← hh, Category.assoc, blOpenY_ι_mulModelHom]

section Descent

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) [IsDomain R] [IsJacobsonRing R]

/-- [C6-d1a, Z] Family-level descent: a field point through `addOnZ` evaluates through some
chart-product family member. -/
theorem specPoint_addOnZ_family (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (WeierstrassCurve.Projective.blOpenZ W).toScheme) :
    ∃ (p : Fin 2 × Fin 2) (h₁ : Spec (CommRingCat.of K) ⟶ (blOpenZFamily W p).toScheme),
      h ≫ WeierstrassCurve.Projective.addOnZ W hΔ = h₁ ≫ addOnZFamily W hΔ p := by
  obtain ⟨p, h₁, hh₁⟩ := specPoint_factors_iSup (blOpenZFamily W) K h
  exact ⟨p, h₁, (congrArg (· ≫ WeierstrassCurve.Projective.addOnZ W hΔ) hh₁.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (homOfLE_le_addOnZ W hΔ p)))⟩

variable (i j : Fin 3) [IsDomain (biChartRing W i j)]

/-- [C6-d1b, Z] Within-chart descent: a field point through `addOnZOnImage` evaluates through
some affine law-1 piece — where it is a ring map. -/
theorem specPoint_addOnZOnImage_factors (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (blOpenZImage W i j).toScheme) :
    ∃ (k : Fin 3) (ψ : Localization.Away (lawOneTriple W i j k) →+* K),
      h ≫ addOnZOnImage W hΔ i j = Spec.map (CommRingCat.ofHom ψ) ≫ addOnZPieceMor W i j k hΔ := by
  -- move to the chart-product side through isoImage, then descend the k-pieces
  obtain ⟨k, h₂, hh₂⟩ := specPoint_factors_iSup (blOpenZPieceFamily W i j) K
    (h ≫ (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenZPieceFamily W i j k)).inv)
  refine ⟨k, CommRingCat.Hom.hom (Spec.preimage (h₂ ≫ morphismRestrict (chartPieceIso W i j).hom
      (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)) ≫
    (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawOneTriple W i j k)).inv)), ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  -- LHS: h ≫ (isoImage.inv ≫ addOnZOnSup) = (h ≫ isoImage.inv) ≫ addOnZOnSup = ...
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

/-- [C6-d1a, Y] Family-level descent: a field point through `addOnY` evaluates through some
chart-product family member. -/
theorem specPoint_addOnY_family (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (WeierstrassCurve.Projective.blOpenY W).toScheme) :
    ∃ (p : Fin 2 × Fin 2) (h₁ : Spec (CommRingCat.of K) ⟶ (blOpenYFamily W p).toScheme),
      h ≫ WeierstrassCurve.Projective.addOnY W hΔ = h₁ ≫ addOnYFamily W hΔ p := by
  obtain ⟨p, h₁, hh₁⟩ := specPoint_factors_iSup (blOpenYFamily W) K h
  exact ⟨p, h₁, (congrArg (· ≫ WeierstrassCurve.Projective.addOnY W hΔ) hh₁.symm).trans
    ((Category.assoc _ _ _).trans (congrArg (h₁ ≫ ·) (homOfLE_le_addOnY W hΔ p)))⟩

variable (i j : Fin 3) [IsDomain (biChartRing W i j)]

/-- [C6-d1b, Y] Within-chart descent: a field point through `addOnYOnImage` evaluates through
some affine law-2 piece — where it is a ring map. -/
theorem specPoint_addOnYOnImage_factors (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (blOpenYImage W i j).toScheme) :
    ∃ (k : Fin 3) (ψ : Localization.Away (lawTwoTriple W i j k) →+* K),
      h ≫ addOnYOnImage W hΔ i j = Spec.map (CommRingCat.ofHom ψ) ≫ addOnYPieceMor W i j k hΔ := by
  -- move to the chart-product side through isoImage, then descend the k-pieces
  obtain ⟨k, h₂, hh₂⟩ := specPoint_factors_iSup (blOpenYPieceFamily W i j) K
    (h ≫ (Scheme.Hom.isoImage (pieceι W i j) (⨆ k, blOpenYPieceFamily W i j k)).inv)
  refine ⟨k, CommRingCat.Hom.hom (Spec.preimage (h₂ ≫ morphismRestrict (chartPieceIso W i j).hom
      (specBasicOpen (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)) ≫
    (specBasicOpenIsoAway (CommRingCat.of (biChartRing W i j)) (lawTwoTriple W i j k)).inv)), ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  -- LHS: h ≫ (isoImage.inv ≫ addOnYOnSup) = (h ≫ isoImage.inv) ≫ addOnYOnSup = ...
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

end Descent


section Readout

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) [IsDomain R] [IsJacobsonRing R]
variable (i j : Fin 3) [IsDomain (biChartRing W i j)]

/-- [C6-d2, Z] Coordinate readout of a descended point: the total ring map evaluates the chart
coordinates to `ψ`-images of the law-1 ratios. Uniform in the chart index `k`. -/
lemma addOnZPieceHom_coord (hΔ : IsUnit W.Δ) {K : Type u} [Field K] [Algebra R K]
    (k : Fin 3) (ψ : Localization.Away (lawOneTriple W i j k) →+* K)
    (m : {l : Fin 3 // l ≠ k}) :
    (ψ.comp (addOnZPieceHom W i j k hΔ).toRingHom)
        (chartCoordEquiv W k (Ideal.Quotient.mk _ (MvPolynomial.X m))) =
      ψ ((algebraMap (biChartRing W i j) (Localization.Away (lawOneTriple W i j k)))
          (lawOneTriple W i j m) *
        IsLocalization.Away.invSelf (lawOneTriple W i j k)) := by
  rw [RingHom.comp_apply]
  congr 1
  unfold addOnZPieceHom chartAwayHomOfTriple
  have hround : (chartCoordAlgEquiv W k).symm (chartCoordEquiv W k (Ideal.Quotient.mk _
      (MvPolynomial.X m))) = Ideal.Quotient.mk _ (MvPolynomial.X m) :=
    (chartCoordEquiv W k).symm_apply_apply _
  show (chartHomOfTriple W k (awayTriple W i j k (lawOneTriple W i j))
      (IsLocalization.Away.invSelf (lawOneTriple W i j k)) (awayTriple_mul_invSelf W i j k _)
      (equation_awayTriple W i j k _ (equation_lawOneTriple_of_isDomain W i j hΔ)))
      ((chartCoordAlgEquiv W k).symm ((chartCoordEquiv W k)
        (Ideal.Quotient.mk _ (MvPolynomial.X m)))) = _
  rw [hround, chartHomOfTriple_coord]
  rfl

/-- [C6-d2, Y] Coordinate readout of a descended point: the total ring map evaluates the chart
coordinates to `ψ`-images of the law-2 ratios. Uniform in the chart index `k`. -/
lemma addOnYPieceHom_coord (hΔ : IsUnit W.Δ) {K : Type u} [Field K] [Algebra R K]
    (k : Fin 3) (ψ : Localization.Away (lawTwoTriple W i j k) →+* K)
    (m : {l : Fin 3 // l ≠ k}) :
    (ψ.comp (addOnYPieceHom W i j k hΔ).toRingHom)
        (chartCoordEquiv W k (Ideal.Quotient.mk _ (MvPolynomial.X m))) =
      ψ ((algebraMap (biChartRing W i j) (Localization.Away (lawTwoTriple W i j k)))
          (lawTwoTriple W i j m) *
        IsLocalization.Away.invSelf (lawTwoTriple W i j k)) := by
  rw [RingHom.comp_apply]
  congr 1
  unfold addOnYPieceHom chartAwayHomOfTriple
  have hround : (chartCoordAlgEquiv W k).symm (chartCoordEquiv W k (Ideal.Quotient.mk _
      (MvPolynomial.X m))) = Ideal.Quotient.mk _ (MvPolynomial.X m) :=
    (chartCoordEquiv W k).symm_apply_apply _
  show (chartHomOfTriple W k (awayTriple W i j k (lawTwoTriple W i j))
      (IsLocalization.Away.invSelf (lawTwoTriple W i j k)) (awayTriple_mul_invSelf W i j k _)
      (equation_awayTriple W i j k _ (equation_lawTwoTriple_of_isDomain W i j hΔ)))
      ((chartCoordAlgEquiv W k).symm ((chartCoordEquiv W k)
        (Ideal.Quotient.mk _ (MvPolynomial.X m)))) = _
  rw [hround, chartHomOfTriple_coord]
  rfl

end Readout

section StrengthenedDescent

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) [IsDomain R] [IsJacobsonRing R]
variable (i j : Fin 3) [IsDomain (biChartRing W i j)]

/-- Standalone collapse: the image inclusion through `isoImage.inv`. -/
lemma blOpenZImage_ι_eq (k : Fin 3) :
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

/-- [C6-d3, Z] The strengthened within-chart descent: the factoring ψ ALSO satisfies the
immersion equation — `Spec.map ψ ≫ pieceAwayZι` is the original point's total immersion. -/
theorem specPoint_addOnZOnImage_factors' (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (blOpenZImage W i j).toScheme) :
    ∃ (k : Fin 3) (ψ : Localization.Away (lawOneTriple W i j k) →+* K),
      h ≫ addOnZOnImage W hΔ i j = Spec.map (CommRingCat.ofHom ψ) ≫ addOnZPieceMor W i j k hΔ ∧
      Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayZι W i j k = h ≫ (blOpenZImage W i j).ι := by
  obtain ⟨k, h₂, hh₂⟩ := specPoint_factors_iSup (blOpenZPieceFamily W i j) K
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
      (congrArg (h ≫ ·) (blOpenZImage_ι_eq W i j k)).trans
        (((Category.assoc _ _ _).symm).trans
          ((congrArg (· ≫ (⨆ k, blOpenZPieceFamily W i j k).ι ≫ pieceι W i j) hh₂.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (h₂ ≫ ·)
                ((Category.assoc _ _ _).symm.trans
                  (congrArg (· ≫ pieceι W i j) (Scheme.homOfLE_ι _ _)))))))
    rw [hR]
    exact (Category.assoc _ _ _).trans (congrArg (h₂ ≫ ·) (mR_isoAway_pieceAwayZι W i j k))

/-- Standalone collapse: the image inclusion through `isoImage.inv`. -/
lemma blOpenYImage_ι_eq (k : Fin 3) :
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

/-- [C6-d3, Y] The strengthened within-chart descent: the factoring ψ ALSO satisfies the
immersion equation — `Spec.map ψ ≫ pieceAwayι` is the original point's total immersion. -/
theorem specPoint_addOnYOnImage_factors' (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (h : Spec (CommRingCat.of K) ⟶ (blOpenYImage W i j).toScheme) :
    ∃ (k : Fin 3) (ψ : Localization.Away (lawTwoTriple W i j k) →+* K),
      h ≫ addOnYOnImage W hΔ i j = Spec.map (CommRingCat.ofHom ψ) ≫ addOnYPieceMor W i j k hΔ ∧
      Spec.map (CommRingCat.ofHom ψ) ≫ pieceAwayι W i j k = h ≫ (blOpenYImage W i j).ι := by
  obtain ⟨k, h₂, hh₂⟩ := specPoint_factors_iSup (blOpenYPieceFamily W i j) K
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
      (congrArg (h ≫ ·) (blOpenYImage_ι_eq W i j k)).trans
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
end ModularCurves
