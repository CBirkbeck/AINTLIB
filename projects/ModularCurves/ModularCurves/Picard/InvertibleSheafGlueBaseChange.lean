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

/-- The local affine base-change map sends a finite-stage overlap transition section
to the overlap transition section of the colimit cocycle. -/
theorem AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionSection
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor) (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let q :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Sstage M.stage)
              (M.toFunctor.obj
                (Scheme.GlueData.affineIntersectionPairIndex i j)))))
    Units.map q.appTop.hom.toMonoidHom (cM.overlapTransitionSection i j) =
      (AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionSection i j := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let X := Scheme.GlueData.affineIntersectionPairIndex i j
  let f := CommRingCat.ofHom
    ((M.baseChangeIso.app X).hom.hom.toRingHom.comp
      (Algebra.TensorProduct.includeRight
        (R := Sstage M.stage) (A := A)
        (B := M.toFunctor.obj X)).toRingHom)
  rw [M.baseChangeSpecIso_inv_snd X]
  apply Units.ext
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality f) (cM.transition i j : M.toFunctor.obj X)
  change
    (Spec.map f).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (M.toFunctor.obj X))).inv.hom
          (cM.transition i j : M.toFunctor.obj X)) =
      (Scheme.ΓSpecIso (CommRingCat.of (G.obj X))).inv.hom
        ((M.object X).stageToColimit H ⟨M.stage, M.le_stage X⟩
          (cM.transition i j : M.toFunctor.obj X))
  have hnat' :
      (Spec.map f).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of (M.toFunctor.obj X))).inv.hom
            (cM.transition i j : M.toFunctor.obj X)) =
        (Scheme.ΓSpecIso (CommRingCat.of (G.obj X))).inv.hom
          (f.hom (cM.transition i j : M.toFunctor.obj X)) := by
    simpa only [CommRingCat.comp_apply, ConcreteCategory.comp_apply] using hnat.symm
  rw [hnat']
  congr 1
  exact (M.object X).baseChangeColimEquiv_tmul (M.le_stage X) H
    (cM.transition i j : M.toFunctor.obj X)

/-- Pulling back the scalar overlap transition of a finite-stage cocycle gives the
scalar overlap transition of its colimit cocycle. -/
theorem AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionIso
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} {G : Functor (Finset J) (CommAlgCat.{u} A)}
    {H : Algebra.IsFilteredAlgColimit R Sstage t A uA}
    (M : Algebra.SpreadData.FunctorModel G H)
    (cM : AffineIntersectionUnitCocycle M.toFunctor) (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let q :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Sstage M.stage)
              (M.toFunctor.obj
                (Scheme.GlueData.affineIntersectionPairIndex i j)))))
    (pullbackUnitIso q).inv ≫
        (pullback q).map (cM.overlapTransitionIso i j).hom ≫
        (pullbackUnitIso q).hom =
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  rw [AffineIntersectionUnitCocycle.overlapTransitionIso,
    ModularCurves.unitAutomorphismOfTopUnit_hom,
    ModularCurves.pullback_unitEndomorphismOfTopSection]
  change ModularCurves.unitEndomorphismOfTopSection
      (((M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A)))
          (Spec.map (CommRingCat.ofHom
            (algebraMap (Sstage M.stage)
              (M.toFunctor.obj
                (Scheme.GlueData.affineIntersectionPairIndex i j)))))).appTop.hom
        (cM.overlapTransitionSection i j : _)) =
    ModularCurves.unitEndomorphismOfTopSection
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionSection i j : _)
  have h := congrArg Units.val
    (AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionSection M cM i j)
  exact congrArg ModularCurves.unitEndomorphismOfTopSection h

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
  exact pullbackSquareTrivialization (DG.ι i) g chartMap (DM.ι i) h
    (cM.gluedModule hopenM hpushM) (cM.gluedModuleLocalIso hopenM hpushM i)

private theorem AffineIntersectionUnitCocycle.baseChangeGluedModuleTail_transition
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
    (i j : J) :
    letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
    let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
    let chartMap (k : J) : DG.U k ⟶ DM.U k :=
      (M.baseChangeSpecIso
          (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
        pullback.snd base
          (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
    let leftMap : DG.V (i, j) ⟶ DM.U i := DG.f i j ≫ chartMap i
    let rightMap : DG.V (i, j) ⟶ DM.U j :=
      (DG.t i j ≫ DG.f j i) ≫ chartMap j
    let q : DG.V (i, j) ⟶ DM.glued := leftMap ≫ DM.ι i
    ∀ (hqRight : rightMap ≫ DM.ι j = q),
    (pullbackCompositeTrivialization leftMap (DM.ι i) q rfl
          (cM.gluedModule hopenM hpushM)
          (cM.gluedModuleLocalIso hopenM hpushM i)).inv ≫
        (pullbackCompositeTrivialization rightMap (DM.ι j) q hqRight
          (cM.gluedModule hopenM hpushM)
          (cM.gluedModuleLocalIso hopenM hpushM j)).hom =
      ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom := by
  classical
  letI : Algebra (Sstage M.stage) A := (uA M.stage).toRingHom.toAlgebra
  dsimp only
  intro hqRight
  let DG := Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := Scheme.GlueData.ofAffineIntersectionFunctor M.toFunctor hopenM hpushM
  let base := Spec.map (CommRingCat.ofHom (algebraMap (Sstage M.stage) A))
  let chartMap (k : J) : DG.U k ⟶ DM.U k :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
      pullback.snd base
        (Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
  let overlapMap (k l : J) : DG.V (k, l) ⟶ DM.V (k, l) :=
    (M.baseChangeSpecIso
        (Scheme.GlueData.affineIntersectionPairIndex k l)).inv ≫
      pullback.snd base
        (Spec.map (CommRingCat.ofHom
          (algebraMap (Sstage M.stage)
            (M.toFunctor.obj
              (Scheme.GlueData.affineIntersectionPairIndex k l)))))
  let leftMap : DG.V (i, j) ⟶ DM.U i := DG.f i j ≫ chartMap i
  let rightMap : DG.V (i, j) ⟶ DM.U j :=
    (DG.t i j ≫ DG.f j i) ≫ chartMap j
  have hleft : overlapMap i j ≫ DM.f i j = leftMap := by
    exact (M.baseChangeSpecIso_inv_affineIntersectionOverlapι i j).symm
  have hright : overlapMap i j ≫ (DM.t i j ≫ DM.f j i) = rightMap := by
    have ht := M.baseChangeSpecIso_inv_affineIntersectionTransition
      hopenG hpushG hopenM hpushM i j
    have hj := M.baseChangeSpecIso_inv_affineIntersectionOverlapι j i
    have ht' : overlapMap i j ≫ DM.t i j = DG.t i j ≫ overlapMap j i := by
      dsimp only [overlapMap, DG, DM]
      simpa only [Category.assoc] using ht
    have hj' : overlapMap j i ≫ DM.f j i = DG.f j i ≫ chartMap j := by
      dsimp only [overlapMap, chartMap, DG, DM]
      simpa only [Category.assoc] using hj.symm
    calc
      overlapMap i j ≫ (DM.t i j ≫ DM.f j i) =
          (overlapMap i j ≫ DM.t i j) ≫ DM.f j i :=
        (Category.assoc _ _ _).symm
      _ = (DG.t i j ≫ overlapMap j i) ≫ DM.f j i :=
        congrArg (· ≫ DM.f j i) ht'
      _ = DG.t i j ≫ (overlapMap j i ≫ DM.f j i) := Category.assoc _ _ _
      _ = DG.t i j ≫ (DG.f j i ≫ chartMap j) :=
        congrArg (DG.t i j ≫ ·) hj'
      _ = rightMap := (Category.assoc _ _ _).symm
  let q : DG.V (i, j) ⟶ DM.glued := leftMap ≫ DM.ι i
  have hqLeft : leftMap ≫ DM.ι i = q := rfl
  have htransition := cM.gluedModuleCompositeTrivialization_transition
    hopenM hpushM i j q (overlapMap i j) leftMap rightMap
    hqLeft hqRight hleft hright
  calc
    _ = cM.chartTransitionIsoCoordinatePullback hopenM hpushM i j
          (overlapMap i j) := htransition
    _ = (pullbackUnitIso (overlapMap i j)).inv ≫
          (pullback (overlapMap i j)).map (cM.overlapTransitionIso i j).hom ≫
          (pullbackUnitIso (overlapMap i j)).hom :=
      cM.chartTransitionIsoCoordinatePullback_eq hopenM hpushM i j (overlapMap i j)
    _ = ((AffineIntersectionUnitCocycle.mapToColimit M cM).overlapTransitionIso i j).hom :=
      AffineIntersectionUnitCocycle.mapToColimit_overlapTransitionIso M cM i j

end

end AlgebraicGeometry.Scheme.Modules
