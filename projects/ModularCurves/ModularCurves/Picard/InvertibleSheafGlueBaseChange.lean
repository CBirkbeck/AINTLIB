import ModularCurves.Picard.InvertibleSheafGlueEffectivity

/-!
# Base change of affine-intersection line-bundle descent

This file compares the concrete Cech-glued invertible sheaf attached to a finite-stage
unit cocycle with its pullback to the filtered-colimit base.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Mapping every transition unit through its stage-to-colimit homomorphism sends a
finite-stage affine-intersection cocycle to the original affine-intersection functor. -/
noncomputable def AffineIntersectionUnitCocycle.mapToColimit
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor) :
    AffineIntersectionUnitCocycle G where
  transition i j :=
    Units.map ((M.object
      (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
        ⟨M.stage, M.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)⟩).toMonoidHom
      (cM.transition i j)
  cocycle i j k := by
    have hc := cM.cocycle i j k
    simp only [M.toFunctor_map_hom] at hc
    rw [← M.map_unit_colimit
      (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)
      (cM.transition i j)]
    rw [← M.map_unit_colimit
      (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)
      (cM.transition j k)]
    rw [← M.map_unit_colimit
      (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)
      (cM.transition i k)]
    rw [← map_mul]
    exact congrArg
      (Units.map ((M.object
        (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageToColimit H
          ⟨M.stage, M.le_stage
            (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩).toMonoidHom) hc

/-- The pullback of a finite-stage glued module has its canonical trivialization on every
base-changed singleton chart. -/
noncomputable def AffineIntersectionUnitCocycle.baseChangeGluedModuleChartTrivialization
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
    (pullback (DG.ι i)).obj
        ((pullback g).obj (cM.gluedModule hopenM hpushM)) ≅ unitObj (DG.U i) := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
  let g := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  let chartMap : DG.U i ⟶ DM.U i :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
        (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i)
  let h : DG.ι i ≫ g = chartMap ≫ DM.ι i :=
    M.affineIntersectionGluedBaseChange_ι hopenG hpushG hopenM hpushM i
  letI : IsOpenImmersion (DM.ι i) := DM.ι_isOpenImmersion i
  let tM : (pullback (DM.ι i)).obj (cM.gluedModule hopenM hpushM) ≅
      unitObj (DM.U i) :=
    (restrictFunctorIsoPullback (DM.ι i)).symm.app
        (cM.gluedModule hopenM hpushM) ≪≫
      cM.gluedModuleRestrictIso hopenM hpushM i
  exact pullbackSquareTrivialization (DG.ι i) g chartMap (DM.ι i) h
    (cM.gluedModule hopenM hpushM) tM

end

end AlgebraicGeometry.Scheme.Modules
