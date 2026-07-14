import Mathlib.AlgebraicGeometry.Pullbacks
import ModularCurves.ForMathlib.FinitePresentationFunctorBaseChange
import ModularCurves.ForMathlib.FinitePresentationSchemeGlueData

/-!
# Scheme base change of spread functor models

The affine spectrum of each object in a spread functor model recovers the corresponding
original affine scheme after extension to the filtered-colimit base. The comparison is
natural in the modeled diagram and specializes to the singleton charts of the associated
affine-intersection glue data.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

noncomputable section

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
  {J : Type u} [SmallCategory J] {F : J ⥤ CommAlgCat.{u} A}
  {H : IsFilteredAlgColimit R 𝒮 t A uA}

/-- The affine scheme of a spread functor object recovers the original affine scheme
after base change to the filtered colimit. -/
noncomputable def SpreadData.FunctorModel.baseChangeSpecIso
    (M : SpreadData.FunctorModel F H) (X : J) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))) ≅
      AlgebraicGeometry.Spec (CommRingCat.of (F.obj X)) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  exact AlgebraicGeometry.pullbackSpecIso (𝒮 M.stage) A (M.toFunctor.obj X) ≪≫
    AlgebraicGeometry.Scheme.Spec.mapIso
      ((forget₂ (CommAlgCat A) CommRingCat).mapIso (M.baseChangeIso.app X)).symm.op

/-- A modeled restriction map induces the corresponding map between affine base changes. -/
noncomputable def SpreadData.FunctorModel.baseChangeSpecMap
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap (𝒮 M.stage) (M.toFunctor.obj Y)))) ⟶
      pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))) :=
  pullback.map _ _ _ _ (𝟙 _)
    (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom))
    (𝟙 _) (by simp) (by
      have hbase :
          CommRingCat.ofHom
              (algebraMap (𝒮 M.stage) (M.toFunctor.obj Y)) =
              CommRingCat.ofHom
                (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)) ≫
              CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom := by
        ext x
        exact ((M.toFunctor.map f).hom.commutes x).symm
      simpa only [Category.comp_id, ← AlgebraicGeometry.Spec.map_comp] using
        congrArg AlgebraicGeometry.Spec.map hbase)

private theorem SpreadData.FunctorModel.pullbackSpecIso_inv_baseChangeSpecMap
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    (AlgebraicGeometry.pullbackSpecIso (𝒮 M.stage) A (M.toFunctor.obj Y)).inv ≫
        M.baseChangeSpecMap f =
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.map (AlgHom.id A A)
              (M.toFunctor.map f).hom).toRingHom) ≫
        (AlgebraicGeometry.pullbackSpecIso
          (𝒮 M.stage) A (M.toFunctor.obj X)).inv := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  apply pullback.hom_ext
  · simp only [SpreadData.FunctorModel.baseChangeSpecMap, Category.assoc,
      pullback.lift_fst, Category.comp_id,
      AlgebraicGeometry.pullbackSpecIso_inv_fst]
    rw [← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext a
    change a ⊗ₜ[(𝒮 M.stage)] (1 : M.toFunctor.obj Y) =
      Algebra.TensorProduct.map (AlgHom.id A A) (M.toFunctor.map f).hom
        (a ⊗ₜ[(𝒮 M.stage)] (1 : M.toFunctor.obj X))
    rw [Algebra.TensorProduct.map_tmul]
    rw [map_one, AlgHom.id_apply]
  · simp only [SpreadData.FunctorModel.baseChangeSpecMap, Category.assoc,
      pullback.lift_snd]
    rw [← Category.assoc, AlgebraicGeometry.pullbackSpecIso_inv_snd]
    rw [AlgebraicGeometry.pullbackSpecIso_inv_snd]
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
    congr 1

/-- The affine-scheme base-change comparisons commute with every modeled restriction map. -/
@[reassoc]
theorem SpreadData.FunctorModel.baseChangeSpecIso_naturality
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    M.baseChangeSpecMap f ≫ (M.baseChangeSpecIso X).hom =
      (M.baseChangeSpecIso Y).hom ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (F.map f).hom.toRingHom) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  rw [← cancel_epi
    (AlgebraicGeometry.pullbackSpecIso
      (𝒮 M.stage) A (M.toFunctor.obj Y)).inv]
  rw [← Category.assoc, M.pullbackSpecIso_inv_baseChangeSpecMap f]
  simp only [SpreadData.FunctorModel.baseChangeSpecIso, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Functor.mapIso_hom, Iso.symm_hom,
    Iso.op_hom, AlgebraicGeometry.Scheme.Spec_map]
  rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  exact congrArg (fun q => CommRingCat.ofHom q.hom.toRingHom)
    (M.baseChangeIso.inv.naturality f).symm

/-- The inverses of the affine base-change comparisons commute with the overlap legs
of affine-intersection functors. -/
theorem SpreadData.FunctorModel.baseChangeSpecIso_inv_affineIntersectionOverlapι
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H) (i j : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    AlgebraicGeometry.Scheme.GlueData.affineIntersectionOverlapι G i j ≫
          (M.baseChangeSpecIso
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
            pullback.snd
              (AlgebraicGeometry.Spec.map
                (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
              (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
                M.toFunctor i) =
      (M.baseChangeSpecIso
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
          pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom
                (algebraMap (𝒮 M.stage)
                  (M.toFunctor.obj
                    (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex i j))))) ≫
        AlgebraicGeometry.Scheme.GlueData.affineIntersectionOverlapι M.toFunctor i j := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let f := AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonToPair i j
  have hIso :
      AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (G.map f).hom.toRingHom) ≫
          (M.baseChangeSpecIso
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv =
        (M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
          M.baseChangeSpecMap f := by
    rw [← cancel_mono
      (M.baseChangeSpecIso
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [M.baseChangeSpecIso_naturality f]
    simp
  change AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (G.map f).hom.toRingHom) ≫
        (M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
          pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom
                (algebraMap (𝒮 M.stage)
                  (M.toFunctor.obj
                    (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i))))) =
      (M.baseChangeSpecIso
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
          pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom
                (algebraMap (𝒮 M.stage)
                  (M.toFunctor.obj
                    (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex i j))))) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom)
  rw [← Category.assoc, hIso, Category.assoc]
  dsimp only [SpreadData.FunctorModel.baseChangeSpecMap, pullback.map]
  rw [pullback.lift_snd]

/-- The pullback of a singleton chart of the stage glue is the corresponding original
affine-intersection chart. -/
noncomputable def SpreadData.FunctorModel.affineIntersectionGluedChartBaseChangeIso
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopen : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor
      M.toFunctor)
    (hpush : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor
      M.toFunctor)
    (i : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    pullback
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
        ((AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
            M.toFunctor hopen hpush).ι i ≫
          AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
            M.toFunctor hopen hpush) ≅
      AlgebraicGeometry.Scheme.GlueData.affineIntersectionChart G i := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  exact pullback.congrHom rfl
      (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor_ι_affineIntersectionToSpec
        M.toFunctor hopen hpush i) ≪≫
    M.baseChangeSpecIso
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)

end

end Algebra
