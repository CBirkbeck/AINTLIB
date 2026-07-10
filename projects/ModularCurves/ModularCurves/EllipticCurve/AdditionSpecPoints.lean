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

/-- [C6-c'0] `Proj.awayι` transported across an element equality (`eqToHom` quarantine). -/
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
    {K : Type u} [CommRing K] (φ : chartAway W k →+* K) : Fin 3 → K := fun m =>
  φ (HomogeneousLocalization.Away.isLocalizationElem
    (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W m))

lemma chartPointTriple_self (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] (φ : chartAway W k →+* K) :
    chartPointTriple W k φ k = φ (HomogeneousLocalization.Away.isLocalizationElem
      (mk_X_mem_quotientGrading_one W k) (mk_X_mem_quotientGrading_one W k)) := rfl

/-- The k-th coordinate of the φ-triple is 1. -/
lemma chartPointTriple_self_eq_one (W : WeierstrassCurve R) (k : Fin 3)
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
lemma chartPointTriple_eq_comp (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] (φ : chartAway W k →+* K) :
    chartPointTriple W k φ =
      (φ.comp (chartCoordAlgEquiv W k).toRingHom) ∘ affineChartPoint W k := by
  funext m
  by_cases hm : m = k
  · subst hm
    rw [chartPointTriple_self_eq_one]
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
lemma equation_chartPointTriple (W : WeierstrassCurve R) (k : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K] (φ : chartAway W k →+* K)
    (hφ : φ.comp (algebraMap R (chartAway W k)) = algebraMap R K) :
    (W.map (algebraMap R K)).toProjective.Equation (chartPointTriple W k φ) := by
  rw [chartPointTriple_eq_comp]
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
lemma eq_chartAwayHomOfTriple_chartPointTriple (W : WeierstrassCurve R) (k : Fin 3)
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

end ChartPointTriple

end ChartNaturality

section AtlasPush

open WeierstrassCurve.Projective

variable (W : WeierstrassCurve R) [W.IsElliptic]
variable {K : Type u} [Field K] [Algebra R K]

/-- [C6-e1] The multiplication point pushed to the atlas: through the base change, the K-point of
`mulModelHom W` is the atlas-side two-law evaluation of the pushed pair. -/
theorem lift_mulModelHom_comp_baseChangeOf
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W) :
    (pullback.lift P.1 Q.1 w ≫ mulModelHom W) ≫
        projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
          (universalWeierstrassLocU_map_classifyRingHomU W) =
      (pullback.lift P.1 Q.1 w ≫
          pullbackMapBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
            (universalWeierstrassLocU_map_classifyRingHomU W)) ≫
        WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU
          universalWeierstrassLocU.isUnit_Δ := by
  rw [mulModelHom]
  simp only [Category.assoc]
  rw [mulModelHomBC_baseChange]

/-- [C6-e2, fst] The pushed pair's first projection is `P` pushed to the atlas. -/
theorem lift_pullbackMap_fst
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W) :
    (pullback.lift P.1 Q.1 w ≫
        pullbackMapBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
          (universalWeierstrassLocU_map_classifyRingHomU W)) ≫
        pullback.fst (projModelπ universalWeierstrassLocU) (projModelπ universalWeierstrassLocU) =
      P.1 ≫ projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
        (universalWeierstrassLocU_map_classifyRingHomU W) := by
  rw [pullbackMapBaseChangeOf]
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]

/-- [C6-e2, snd] Mirror. -/
theorem lift_pullbackMap_snd
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W) :
    (pullback.lift P.1 Q.1 w ≫
        pullbackMapBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
          (universalWeierstrassLocU_map_classifyRingHomU W)) ≫
        pullback.snd (projModelπ universalWeierstrassLocU) (projModelπ universalWeierstrassLocU) =
      Q.1 ≫ projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
        (universalWeierstrassLocU_map_classifyRingHomU W) := by
  rw [pullbackMapBaseChangeOf]
  simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]


/-- [C6-e3] The pushed pair-point is the atlas-side lift of the pushed points. -/
theorem lift_pullbackMap_eq_lift
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    (w : P.1 ≫ projModelπ W = Q.1 ≫ projModelπ W)
    (w' : (P.1 ≫ projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
        (universalWeierstrassLocU_map_classifyRingHomU W)) ≫
          projModelπ universalWeierstrassLocU =
      (Q.1 ≫ projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
        (universalWeierstrassLocU_map_classifyRingHomU W)) ≫
          projModelπ universalWeierstrassLocU) :
    pullback.lift P.1 Q.1 w ≫
        pullbackMapBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
          (universalWeierstrassLocU_map_classifyRingHomU W) =
      pullback.lift
        (P.1 ≫ projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
          (universalWeierstrassLocU_map_classifyRingHomU W))
        (Q.1 ≫ projModelBaseChangeOf (classifyRingHomU W) universalWeierstrassLocU W
          (universalWeierstrassLocU_map_classifyRingHomU W)) w' := by
  apply pullback.hom_ext
  · rw [lift_pullbackMap_fst W P Q w, pullback.lift_fst]
  · rw [lift_pullbackMap_snd W P Q w, pullback.lift_snd]

end AtlasPush

section AtlasFormula

open WeierstrassCurve.Projective

variable {K : Type u} [Field K] [DecidableEq K]

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
      haveI : WK.IsElliptic := by
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
        WeierstrassCurve.Projective.addXYZ, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
      linear_combination -(WeierstrassCurve.Projective.addX_mul_dblAddY (W' := WK) hP hQ)
    have h02 : (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 0 * WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j) (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 2 = (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 2 * WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j) (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 0 := by
      rw [hlaw2]
      simp only [WeierstrassCurve.Projective.dblAddXYZ_x, WeierstrassCurve.Projective.dblAddXYZ_z,
        WeierstrassCurve.Projective.addXYZ, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      linear_combination -(WeierstrassCurve.Projective.addX_mul_dblAddZ (W' := WK) hP hQ)
    have h12 : (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 1 * WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j) (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 2 = (χ ∘ lawTwoTriple universalWeierstrassLocU.{u} i j) 2 * WK.addXYZ (χ ∘ biChartPointFst universalWeierstrassLocU.{u} i j) (χ ∘ biChartPointSnd universalWeierstrassLocU.{u} i j) 1 := by
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



/-- **[C6-e5c] The atlas-level specPoints spec** (the c6 core): over the ULift universal atlas the
glued two-law multiplication computes the group law of the dictionary. Proof plan (v10.94f/g):
case split via specPoint_factors_blOpenZ_or_blOpenY; per case descend by
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
  sorry

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
end ModularCurves
