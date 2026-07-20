/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Picard.InvertibleSheafGlueBaseChange
import ModularCurves.ForMathlib.FilteredColimitProper

/-!
# Noetherian finite-stage models of invertible sheaves

The canonical presentation system over the universe-lifted integers writes the coordinate ring
of an affine base as a filtered colimit of Noetherian finitely presented rings. Specializing the
existing finite-stage descent theorem to this system gives a Noetherian separated model of a
proper family and its invertible sheaf. Properness descends after moving to one later stage.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private theorem isProper_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (hf : IsProper f) (hfg : f = g) : IsProper g :=
  hfg ▸ hf

private theorem isProper_cancel_iso {W X Y : Scheme.{u}} (e : W ≅ X) (f : X ⟶ Y)
    (h : IsProper (e.hom ≫ f)) : IsProper f :=
  (MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom f).mp h

private theorem exists_later_proper_model_with_invertible_base_change_iso
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    (H : Algebra.IsFilteredAlgColimit R Sstage t A uA)
    {i : ι} [IsNoetherianRing (Sstage i)] {Y X : Scheme.{u}}
    (yπ : Y ⟶ Spec (.of (Sstage i))) [LocallyOfFinitePresentation yπ]
    [QuasiCompact yπ] [IsSeparated yπ]
    {L : Y.Modules} (hL : IsInvertible L) {N : X.Modules}
    (hproper :
      letI : Algebra (Sstage i) A := (uA i).toRingHom.toAlgebra
      IsProper (pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap (Sstage i) A))) yπ))
    (hbase :
      letI : Algebra (Sstage i) A := (uA i).toRingHom.toAlgebra
      let stageToBase := Spec.map (CommRingCat.ofHom
        (algebraMap (Sstage i) A))
      ∃ φ : CategoryTheory.Limits.pullback yπ stageToBase ≅ X,
        Nonempty
          ((AlgebraicGeometry.Scheme.Modules.pullback
              (pullback.fst yπ stageToBase)).obj L ≅
            (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj N)) :
    ∃ (j : ι) (Yj : Scheme.{u}) (yπj : Yj ⟶ Spec (.of (Sstage j)))
      (Lj : Yj.Modules),
      LocallyOfFinitePresentation yπj ∧ IsProper yπj ∧ IsInvertible Lj ∧
        (letI : Algebra (Sstage j) A := (uA j).toRingHom.toAlgebra
          let stageToBase := Spec.map (CommRingCat.ofHom
            (algebraMap (Sstage j) A))
          ∃ φ : CategoryTheory.Limits.pullback yπj stageToBase ≅ X,
            Nonempty
              ((AlgebraicGeometry.Scheme.Modules.pullback
                  (pullback.fst yπj stageToBase)).obj Lj ≅
                (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj N)) := by
  classical
  letI : Algebra (Sstage i) A := (uA i).toRingHom.toAlgebra
  let gA := Spec.map (CommRingCat.ofHom (algebraMap (Sstage i) A))
  obtain ⟨φ, E⟩ := hbase
  let Ei := Classical.choice E
  obtain ⟨j, hij, hproperj⟩ :=
    Scheme.Hom.exists_isProper_scalarExtension_of_isProper_baseChange H yπ hproper
  letI : Algebra (Sstage i) (Sstage j) := (t hij).toRingHom.toAlgebra
  let gj := Spec.map (CommRingCat.ofHom (algebraMap (Sstage i) (Sstage j)))
  let Yj := CategoryTheory.Limits.pullback gj yπ
  let yπj := pullback.fst gj yπ
  let qj := pullback.snd gj yπ
  let Lj := (AlgebraicGeometry.Scheme.Modules.pullback qj).obj L
  letI : Algebra (Sstage j) A := (uA j).toRingHom.toAlgebra
  let gAj := Spec.map (CommRingCat.ofHom (algebraMap (Sstage j) A))
  have halg : (uA j).comp (t hij) = uA i := by
    apply AlgHom.ext
    intro x
    exact H.compat (i := i) (j := j) hij x
  have hg : gAj ≫ gj = gA := by
    change Spec.map (CommRingCat.ofHom (uA j).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (t hij).toRingHom) =
      Spec.map (CommRingCat.ofHom (uA i).toRingHom)
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) halg
  let e : CategoryTheory.Limits.pullback yπj gAj ≅
      CategoryTheory.Limits.pullback yπ gA :=
    pullbackSymmetry yπj gAj ≪≫
      pullbackRightPullbackFstIso gj yπ gAj ≪≫
      pullbackSymmetry (gAj ≫ gj) yπ ≪≫
      pullback.congrHom rfl hg
  have he : e.hom ≫ pullback.fst yπ gA =
      pullback.fst yπj gAj ≫ qj := by
    have hcongr : (pullback.congrHom (rfl : yπ = yπ) hg).hom ≫
        pullback.fst yπ gA = pullback.fst yπ (gAj ≫ gj) := by
      simp only [pullback.congrHom_hom, pullback.map, Category.comp_id]
      exact pullback.lift_fst _ _ _
    calc
      e.hom ≫ pullback.fst yπ gA =
          (pullbackSymmetry yπj gAj).hom ≫
            (pullbackRightPullbackFstIso gj yπ gAj).hom ≫
              (pullbackSymmetry (gAj ≫ gj) yπ).hom ≫
                pullback.fst yπ (gAj ≫ gj) := by
        simp only [e, Iso.trans_hom, Category.assoc, hcongr]
      _ = (pullbackSymmetry yπj gAj).hom ≫
            (pullbackRightPullbackFstIso gj yπ gAj).hom ≫
              pullback.snd (gAj ≫ gj) yπ := by
        rw [pullbackSymmetry_hom_comp_fst]
      _ = (pullbackSymmetry yπj gAj).hom ≫
            pullback.snd gAj yπj ≫ pullback.snd gj yπ := by
        rw [pullbackRightPullbackFstIso_hom_snd]
      _ = pullback.fst yπj gAj ≫ pullback.snd gj yπ := by
        rw [pullbackSymmetry_hom_comp_snd_assoc]
  let φj := e ≪≫ φ
  let Ej :
      (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.fst yπj gAj)).obj Lj ≅
        (AlgebraicGeometry.Scheme.Modules.pullback φj.hom).obj N :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp
        (pullback.fst yπj gAj) qj).app L ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr he.symm).app L) ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        e.hom (pullback.fst yπ gA)).app L).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback e.hom).mapIso Ei ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom φ.hom).app N
  refine ⟨j, Yj, yπj, Lj, ?_, hproperj, hL.pullback qj, φj, ⟨Ej⟩⟩
  infer_instance

/-- An invertible sheaf on a proper, locally finitely presented family over an affine base
descends to a separated finite-presentation model over a Noetherian ring. The model and sheaf
recover the original pair after base change. -/
theorem IsInvertible.exists_noetherianStageModelOfFinitePresentationSeparatedBaseChangeIso_of_isProper
    {X S : Scheme.{u}} {π : X ⟶ S} [IsProper π] [IsAffine S]
    [LocallyOfFinitePresentation π] {N : X.Modules} (hN : IsInvertible N) :
    let A : Type u := Γ(S, (⊤ : S.Opens))
    letI : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
    let H := Algebra.PresentationSystem.isFilteredAlgColimit (ULift.{u} ℤ) A
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens)
      (hcover : IsOpenCover U)
      (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
      (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
      (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
      (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
      (_hsepM : Scheme.GlueData.IsSeparatedAffineIntersectionFunctor M.toFunctor)
      (cM : AffineIntersectionUnitCocycle M.toFunctor),
      LocallyOfFinitePresentation
          (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM) ∧
        QuasiCompact
          (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM) ∧
        IsSeparated
          (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM) ∧
        IsInvertible (cM.gluedModule hopenM hpushM) ∧
          Nonempty
            (letI : Algebra
                (Algebra.PresentationSystem.stage (ULift.{u} ℤ) A M.stage) A :=
                (Algebra.PresentationSystem.colimMap (ULift.{u} ℤ) A M.stage).toRingHom.toAlgebra
              let stageToBase := Spec.map (CommRingCat.ofHom
                (algebraMap
                  (Algebra.PresentationSystem.stage (ULift.{u} ℤ) A M.stage) A))
              let p := CategoryTheory.Limits.pullback.fst
                (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM)
                stageToBase
              let φ := π.affineIntersectionModelBaseChangeIso
                U hcover hU M hopenM hpushM
              (AlgebraicGeometry.Scheme.Modules.pullback p).obj
                  (cM.gluedModule hopenM hpushM) ≅
                (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj N) := by
  dsimp only
  letI : Algebra (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)) :=
    ULift.algebra' ℤ Γ(S, (⊤ : S.Opens))
  exact hN.exists_finiteStageModelOfFinitePresentationSeparatedBaseChangeIso_of_isProper
    (R := ULift.{u} ℤ)
    (Sstage := Algebra.PresentationSystem.stage
      (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)))
    (t := Algebra.PresentationSystem.transition
      (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)))
    (uS := Algebra.PresentationSystem.colimMap
      (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)))
    (Algebra.PresentationSystem.isFilteredAlgColimit
      (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)))

/-- An invertible sheaf on a proper, locally finitely presented family over an affine base
descends to an invertible sheaf on a proper finite-presentation model over a Noetherian ring.
The family and sheaf both recover the original pair after base change. -/
theorem IsInvertible.exists_noetherianStageModelOfFinitePresentationProperBaseChangeIso_of_isProper
    {X S : Scheme.{u}} {π : X ⟶ S} [IsProper π] [IsAffine S]
    [LocallyOfFinitePresentation π] {N : X.Modules} (hN : IsInvertible N) :
    let A : Type u := Γ(S, (⊤ : S.Opens))
    letI : Algebra (ULift.{u} ℤ) A := ULift.algebra' ℤ A
    ∃ (j : Algebra.PresentationSystem.Index (ULift.{u} ℤ) A)
      (Y : Scheme.{u})
      (yπ : Y ⟶ Spec (.of
        (Algebra.PresentationSystem.stage (ULift.{u} ℤ) A j)))
      (L : Y.Modules),
      LocallyOfFinitePresentation yπ ∧ IsProper yπ ∧ IsInvertible L ∧
        (letI : Algebra
            (Algebra.PresentationSystem.stage (ULift.{u} ℤ) A j) A :=
            (Algebra.PresentationSystem.colimMap (ULift.{u} ℤ) A j).toRingHom.toAlgebra
          let stageToBase := Spec.map (CommRingCat.ofHom
            (algebraMap
              (Algebra.PresentationSystem.stage (ULift.{u} ℤ) A j) A))
          ∃ φ : CategoryTheory.Limits.pullback yπ stageToBase ≅ X,
            Nonempty
              ((AlgebraicGeometry.Scheme.Modules.pullback
                  (pullback.fst yπ stageToBase)).obj L ≅
                (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj N)) := by
  classical
  dsimp only
  letI : Algebra (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens)) :=
    ULift.algebra' ℤ Γ(S, (⊤ : S.Opens))
  let H := Algebra.PresentationSystem.isFilteredAlgColimit
    (ULift.{u} ℤ) Γ(S, (⊤ : S.Opens))
  obtain ⟨J, hJ, U, hcover, hU, M, hopenM, hpushM, hsepM, cM,
      hfpM, hqcM, hsepπM, hcM, hbaseM⟩ :=
    hN.exists_noetherianStageModelOfFinitePresentationSeparatedBaseChangeIso_of_isProper
      (π := π)
  letI : Finite J := hJ
  let A := Γ(S, (⊤ : S.Opens))
  let B := Algebra.PresentationSystem.stage (ULift.{u} ℤ) A M.stage
  let yπM := Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM
  let LM := cM.gluedModule hopenM hpushM
  letI : LocallyOfFinitePresentation yπM := hfpM
  letI : QuasiCompact yπM := hqcM
  letI : IsSeparated yπM := hsepπM
  letI : Algebra B A :=
    (Algebra.PresentationSystem.colimMap (ULift.{u} ℤ) A M.stage).toRingHom.toAlgebra
  let gA := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let φM := π.affineIntersectionModelBaseChangeIso
    U hcover hU M hopenM hpushM
  have hφM : φM.hom ≫ π ≫ S.isoSpec.hom = pullback.snd yπM gA := by
    let ψ := M.affineIntersectionGluedBaseChangeIso
        (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
        (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU)
        hopenM hpushM
    calc
      φM.hom ≫ π ≫ S.isoSpec.hom =
          ψ.hom ≫ (π.affineIntersectionGluedToOriginal U hU ≫
            π ≫ S.isoSpec.hom) := rfl
      _ = ψ.hom ≫ Scheme.GlueData.affineIntersectionToSpec
          (π.affineIntersectionFunctor U)
          (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
          (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU) := by
        rw [π.affineIntersectionGluedToOriginal_comp_toSpec U hU]
      _ = pullback.snd yπM gA :=
        M.affineIntersectionGluedBaseChangeIso_hom_snd
          (π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU)
          (π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU)
          hopenM hpushM
  have hproperMBaseChange : IsProper (pullback.snd yπM gA) := by
    have hcomp : IsProper (φM.hom ≫ π ≫ S.isoSpec.hom) := by
      infer_instance
    exact isProper_of_eq
      (f := φM.hom ≫ π ≫ S.isoSpec.hom)
      (g := pullback.snd yπM gA) hcomp hφM
  have hproperMBaseChange' : IsProper (pullback.fst gA yπM) := by
    let eSym := pullbackSymmetry yπM gA
    have hsym : eSym.hom ≫ pullback.fst gA yπM =
        pullback.snd yπM gA :=
      pullbackSymmetry_hom_comp_fst yπM gA
    have hcomp : IsProper (eSym.hom ≫ pullback.fst gA yπM) := by
      exact isProper_of_eq hproperMBaseChange hsym.symm
    exact isProper_cancel_iso eSym (pullback.fst gA yπM) hcomp
  exact exists_later_proper_model_with_invertible_base_change_iso
    H yπM hcM hproperMBaseChange' ⟨φM, hbaseM⟩

end

end AlgebraicGeometry.Scheme.Modules
