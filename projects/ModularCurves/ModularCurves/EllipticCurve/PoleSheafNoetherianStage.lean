/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafPointedIso
import ModularCurves.Picard.InvertibleSheafNoetherianSmoothStage

/-!
# Noetherian models of pole sheaves

This file combines Noetherian-stage descent for invertible sheaves with transport
of pole sheaves along compatible isomorphisms of pointed families.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace ModularCurves

/-- The simple-pole sheaf of a smooth proper fibrewise elliptic family over an
arbitrary affine base descends to an invertible sheaf on a smooth proper
Noetherian-stage family. After returning to the original affine base, the stage
family retains its section, relative dimension, fibrewise ellipticity, and
simple-pole sheaf. -/
theorem FibrewiseElliptic.exists_noetherianPoleSheafModel
    {X S : Scheme.{u}} {π : X ⟶ S} [IsAffine S] [IsProper π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ X) (hz : z ≫ π = 𝟙 S)
    (h : FibrewiseElliptic π z hz) :
    let A : Type u := Γ(S, (⊤ : S.Opens))
    letI : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
    ∃ (j : Algebra.PresentationSystem.Index (ULift.{u} ℤ) A)
      (Y : Scheme.{u})
      (yπ : Y ⟶ Spec (.of
        (Algebra.PresentationSystem.stage (ULift.{u} ℤ) A j)))
      (L : Y.Modules),
      LocallyOfFinitePresentation yπ ∧ IsProper yπ ∧ Smooth yπ ∧
        Scheme.Modules.IsInvertible L ∧
        (let B :=
            Algebra.PresentationSystem.stage (ULift.{u} ℤ) A j;
          letI : Algebra B A :=
            (Algebra.PresentationSystem.colimMap
              (ULift.{u} ℤ) A j).toRingHom.toAlgebra;
          let gA := Spec.map (CommRingCat.ofHom (algebraMap B A));
          let πA := pullback.snd yπ gA;
          ∃ (φ : pullback yπ gA ≅ X)
            (zA : Spec (.of A) ⟶ pullback yπ gA)
            (hzA : zA ≫ πA = 𝟙 _)
            (hproperA : IsProper πA),
            letI : IsProper πA := hproperA
            φ.hom ≫ π ≫ S.isoSpec.hom = πA ∧
              zA ≫ φ.hom = S.isoSpec.inv ≫ z ∧
              SmoothOfRelativeDimension 1 πA ∧
              FibrewiseElliptic πA zA hzA ∧
              Nonempty
                ((Scheme.Modules.pullback
                    (pullback.fst yπ gA)).obj L ≅
                  sectionPoleSheafPower πA zA hzA 1)) := by
  classical
  dsimp only
  letI : SmoothOfRelativeDimension 1 π := hsm
  letI : Smooth π := SmoothOfRelativeDimension.smooth 1 π
  let hN : Scheme.Modules.IsInvertible
      (sectionPoleSheafPower π z hz 1) :=
    sectionPoleSheafPower_isInvertible hsm z hz 1
  obtain ⟨j, Y, yπ, L, hfp, hproper, hsmooth, hL, φ, hφ, E⟩ :=
    hN.exists_noetherianProperSmoothModelBaseChangeIso_with_base_comp_of_isProper
      (π := π)
  letI : LocallyOfFinitePresentation yπ := hfp
  letI : IsProper yπ := hproper
  letI : Smooth yπ := hsmooth
  letI : Scheme.Modules.IsInvertible L := hL
  refine ⟨j, Y, yπ, L, hfp, hproper, hsmooth, hL, ?_⟩
  let A : Type u := Γ(S, (⊤ : S.Opens))
  letI : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
  let B := Algebra.PresentationSystem.stage (ULift.{u} ℤ) A j
  letI : Algebra B A :=
    (Algebra.PresentationSystem.colimMap
      (ULift.{u} ℤ) A j).toRingHom.toAlgebra
  let gA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let πA := pullback.snd yπ gA
  let hproperA : IsProper πA := inferInstance
  letI : IsProper πA := hproperA
  letI : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  letI : MorphismProperty.RespectsIso
      (@SmoothOfRelativeDimension 1) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let z₀ : Spec (.of A) ⟶ X := S.isoSpec.inv ≫ z
  let zA : Spec (.of A) ⟶ pullback yπ gA := z₀ ≫ φ.inv
  have hπφ : φ.hom ≫ (π ≫ S.isoSpec.hom) = πA := by
    simpa only [Category.assoc] using hφ
  have hz₀ : z₀ ≫ (π ≫ S.isoSpec.hom) = 𝟙 _ := by
    calc
      z₀ ≫ (π ≫ S.isoSpec.hom) =
          S.isoSpec.inv ≫ (z ≫ π) ≫ S.isoSpec.hom := by
        simp only [z₀, Category.assoc]
      _ = S.isoSpec.inv ≫ S.isoSpec.hom := by rw [hz]; simp
      _ = 𝟙 _ := S.isoSpec.inv_hom_id
  have hzA : zA ≫ πA = 𝟙 _ := by
    rw [← hπφ]
    simpa only [zA, Category.assoc, Iso.inv_hom_id_assoc] using hz₀
  have hzφ : zA ≫ φ.hom = S.isoSpec.inv ≫ z := by
    calc
      zA ≫ φ.hom = z₀ ≫ (φ.inv ≫ φ.hom) := by
        simp only [zA, Category.assoc]
      _ = z₀ := by rw [Iso.inv_hom_id, Category.comp_id]
      _ = S.isoSpec.inv ≫ z := rfl
  have hsmSpec :
      SmoothOfRelativeDimension 1 (π ≫ S.isoSpec.hom) := by
    rw [MorphismProperty.cancel_right_of_respectsIso
      (P := @SmoothOfRelativeDimension 1)]
    exact hsm
  have hsmA : SmoothOfRelativeDimension 1 πA := by
    rw [← hπφ, MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1)]
    exact hsmSpec
  have hfibSpec :
      FibrewiseElliptic (π ≫ S.isoSpec.hom) z₀ hz₀ := by
    apply h.of_iso (Iso.refl X) S.isoSpec.symm
    · change π = (π ≫ S.isoSpec.hom) ≫ S.isoSpec.inv
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · simp only [Iso.symm_hom, z₀, Iso.refl_hom, Category.comp_id]
  have hfibA : FibrewiseElliptic πA zA hzA := by
    apply hfibSpec.of_iso_over φ hπφ
    simpa only [z₀] using hzφ
  let ePole :=
    sectionPoleSheafPowerPointedIsoOfBaseIso
      zA hzA z hz hsm φ S.isoSpec.symm hzφ.symm 1
  refine ⟨φ, zA, hzA, hproperA, hφ, hzφ, hsmA, hfibA, ?_⟩
  exact ⟨Classical.choice E ≪≫ ePole⟩

end ModularCurves
