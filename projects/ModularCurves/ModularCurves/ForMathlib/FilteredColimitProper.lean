/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.FilteredColimitOpenImmersion
import ModularCurves.ForMathlib.NoetherianChowCover
import ModularCurves.ForMathlib.ProperAffineIntersectionModel

/-!
# Properness over filtered colimits

A finitely presented, quasi-compact, separated scheme over a Noetherian stage whose
scalar extension to a filtered colimit is proper becomes proper after scalar extension
to some later stage.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {S : ι → Type u} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (S i →ₐ[R] S j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, S i →ₐ[R] A}

/-- Properness of the scalar extension of a finitely presented separated scheme to a
filtered colimit descends to one later scalar-extension stage. -/
theorem Scheme.Hom.exists_isProper_scalarExtension_of_isProper_baseChange
    (H : Algebra.IsFilteredAlgColimit R S t A uA)
    {i : ι} [IsNoetherianRing (S i)] {Y : Scheme.{u}}
    (yπ : Y ⟶ Spec (.of (S i))) [LocallyOfFinitePresentation yπ]
    [QuasiCompact yπ] [IsSeparated yπ]
    (hproper :
      letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
      IsProper
        (pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap (S i) A))) yπ)) :
    ∃ (j : ι) (hij : i ≤ j),
      letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
      IsProper
        (pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))) yπ) := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian yπ
  letI : CompactSpace Y := (quasiCompact_iff_compactSpace yπ).mp inferInstance
  letI : IsNoetherian Y := IsNoetherian.mk
  obtain ⟨X', Z, cover, immersion, zπ, hcoverProper, hcoverSurjective,
      himmersionOpen, hzProper, hsquare⟩ := yπ.exists_chowCover_of_isNoetherian
  letI : IsProper cover := hcoverProper
  letI : Surjective cover := hcoverSurjective
  letI : IsOpenImmersion immersion := himmersionOpen
  letI : IsProper zπ := hzProper
  letI : Algebra (S i) A := (uA i).toRingHom.toAlgebra
  let gA := Spec.map (CommRingCat.ofHom (algebraMap (S i) A))
  let yπA := pullback.fst gA yπ
  let pYA := pullback.snd gA yπ
  let coverA := pullback.snd cover pYA
  let zπA := pullback.fst gA zπ
  let pZA := pullback.snd gA zπ
  let immersionA := pullback.snd immersion pZA
  letI : IsProper yπA := hproper
  letI : IsProper coverA := inferInstance
  have hcoverCompositeA : IsProper (coverA ≫ yπA) := by infer_instance
  let eCoverA := pullbackSymmetry cover pYA ≪≫
    pullbackLeftPullbackSndIso gA yπ cover
  have heCoverA : eCoverA.hom ≫ pullback.fst gA (cover ≫ yπ) =
      coverA ≫ yπA := by
    simp [eCoverA, coverA, yπA, pYA]
  have hproperDirectCoverA : IsProper (pullback.fst gA (cover ≫ yπ)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper eCoverA.hom]
    rw [heCoverA]
    exact hcoverCompositeA
  let eSquareA := pullback.congrHom (rfl : gA = gA) hsquare
  have heSquareA : eSquareA.hom ≫ pullback.fst gA (immersion ≫ zπ) =
      pullback.fst gA (cover ≫ yπ) := by
    simp only [eSquareA, pullback.congrHom_hom, pullback.map, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hproperDirectImmersionA : IsProper (pullback.fst gA (immersion ≫ zπ)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper eSquareA.hom]
    rw [heSquareA]
    exact hproperDirectCoverA
  let eImmersionA := pullbackSymmetry immersion pZA ≪≫
    pullbackLeftPullbackSndIso gA zπ immersion
  have heImmersionA : eImmersionA.hom ≫ pullback.fst gA (immersion ≫ zπ) =
      immersionA ≫ zπA := by
    simp [eImmersionA, immersionA, zπA, pZA]
  letI : IsProper (pullback.fst gA (immersion ≫ zπ)) := hproperDirectImmersionA
  have hproperImmersionCompositeA : IsProper (immersionA ≫ zπA) := by
    have h : IsProper (eImmersionA.hom ≫ pullback.fst gA (immersion ≫ zπ)) := by
      infer_instance
    rw [heImmersionA] at h
    exact h
  letI : IsProper (immersionA ≫ zπA) := hproperImmersionCompositeA
  have hclosedA : IsClosedImmersion immersionA :=
    IsClosedImmersion.of_isOpenImmersion_comp_isProper immersionA zπA
  obtain ⟨j, hij, hclosedj⟩ :=
    Scheme.Hom.exists_isClosedImmersion_scalarExtension_of_isOpenImmersion_of_isProperTarget
      H zπ immersion hclosedA
  letI : Algebra (S i) (S j) := (t hij).toRingHom.toAlgebra
  let gj := Spec.map (CommRingCat.ofHom (algebraMap (S i) (S j)))
  let yπj := pullback.fst gj yπ
  let pYj := pullback.snd gj yπ
  let coverj := pullback.snd cover pYj
  let zπj := pullback.fst gj zπ
  let pZj := pullback.snd gj zπ
  let immersionj := pullback.snd immersion pZj
  letI : IsClosedImmersion immersionj := hclosedj
  letI : IsProper immersionj := inferInstance
  letI : IsProper zπj := inferInstance
  have hproperXj : IsProper (immersionj ≫ zπj) := by infer_instance
  let eCoverj := pullbackSymmetry cover pYj ≪≫
    pullbackLeftPullbackSndIso gj yπ cover
  have heCoverj : eCoverj.hom ≫ pullback.fst gj (cover ≫ yπ) =
      coverj ≫ yπj := by
    simp [eCoverj, coverj, yπj, pYj]
  let eSquarej := pullback.congrHom (rfl : gj = gj) hsquare
  have heSquarej : eSquarej.hom ≫ pullback.fst gj (immersion ≫ zπ) =
      pullback.fst gj (cover ≫ yπ) := by
    simp only [eSquarej, pullback.congrHom_hom, pullback.map, Category.comp_id]
    exact pullback.lift_fst _ _ _
  let eImmersionj := pullbackSymmetry immersion pZj ≪≫
    pullbackLeftPullbackSndIso gj zπ immersion
  have heImmersionj : eImmersionj.hom ≫ pullback.fst gj (immersion ≫ zπ) =
      immersionj ≫ zπj := by
    simp [eImmersionj, immersionj, zπj, pZj]
  have heImmersionjInv : eImmersionj.inv ≫ (immersionj ≫ zπj) =
      pullback.fst gj (immersion ≫ zπ) := by
    rw [← heImmersionj, Iso.inv_hom_id_assoc]
  let eStage := eCoverj ≪≫ eSquarej ≪≫ eImmersionj.symm
  have heStage : eStage.hom ≫ (immersionj ≫ zπj) = coverj ≫ yπj := by
    simp only [eStage, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      heImmersionjInv, heSquarej, heCoverj]
  letI : IsProper (immersionj ≫ zπj) := hproperXj
  have hproperCoverCompositej : IsProper (coverj ≫ yπj) := by
    have h : IsProper (eStage.hom ≫ (immersionj ≫ zπj)) := by infer_instance
    rw [heStage] at h
    exact h
  letI : IsProper (coverj ≫ yπj) := hproperCoverCompositej
  letI : Surjective coverj := inferInstance
  have hproperYj : IsProper yπj := IsProper.of_comp_surjective coverj yπj
  exact ⟨j, hij, hproperYj⟩

end

end AlgebraicGeometry
