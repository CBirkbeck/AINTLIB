import Mathlib.AlgebraicGeometry.PullbackCarrier
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

/-- The inverse affine base-change comparison followed by the first projection is the
structural morphism of the original affine scheme. -/
theorem SpreadData.FunctorModel.baseChangeSpecIso_inv_fst
    (M : SpreadData.FunctorModel F H) (X : J) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    (M.baseChangeSpecIso X).inv ≫
        pullback.fst
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))) =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap A (F.obj X))) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  simp only [SpreadData.FunctorModel.baseChangeSpecIso, Iso.trans_inv,
    Category.assoc, Functor.mapIso_inv, Iso.symm_inv, Iso.op_inv,
    AlgebraicGeometry.Scheme.Spec_map, AlgebraicGeometry.pullbackSpecIso_inv_fst]
  rw [← AlgebraicGeometry.Spec.map_comp]
  congr 1
  ext a
  exact (M.baseChangeIso.hom.app X).hom.commutes a

/-- The inverse affine base-change comparison exhibits the original affine scheme as the
base change of its modeled affine scheme. -/
theorem SpreadData.FunctorModel.baseChangeSpecIso_inv_isPullback
    (M : SpreadData.FunctorModel F H) (X : J) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    IsPullback
      ((M.baseChangeSpecIso X).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap A (F.obj X))))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (algebraMap (𝒮 M.stage) (M.toFunctor.obj X))))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let base := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))
  let toStage := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom
      (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))
  refine (IsPullback.of_hasPullback base toStage).flip.of_iso
    (M.baseChangeSpecIso X) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · rw [Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]
  · rw [← M.baseChangeSpecIso_inv_fst X]
    rw [Iso.hom_inv_id_assoc, Iso.refl_hom, Category.comp_id]
  · rfl
  · rfl

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

/-- Base change carries every modeled affine restriction square to a pullback square. -/
theorem SpreadData.FunctorModel.baseChangeSpecMap_isPullback
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    IsPullback
      (M.baseChangeSpecMap f)
      (pullback.snd
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap (𝒮 M.stage) (M.toFunctor.obj Y)))))
      (pullback.snd
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom)) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let base := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))
  let toStageX := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom
      (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))
  let toStageY := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom
      (algebraMap (𝒮 M.stage) (M.toFunctor.obj Y)))
  let mapYX := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom)
  have hright : IsPullback
      (pullback.fst base toStageX) (pullback.snd base toStageX)
      base toStageX := IsPullback.of_hasPullback _ _
  have hbase :
      CommRingCat.ofHom
          (algebraMap (𝒮 M.stage) (M.toFunctor.obj Y)) =
        CommRingCat.ofHom
            (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)) ≫
          CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom := by
    ext x
    exact ((M.toFunctor.map f).hom.commutes x).symm
  have hmap_fst :
      M.baseChangeSpecMap f ≫ pullback.fst base toStageX =
        pullback.fst base toStageY := by
    dsimp [SpreadData.FunctorModel.baseChangeSpecMap, pullback.map,
      base, toStageX, toStageY]
    rw [pullback.lift_fst, Category.comp_id]
  have hmap_snd :
      M.baseChangeSpecMap f ≫ pullback.snd base toStageX =
        pullback.snd base toStageY ≫ mapYX := by
    dsimp [SpreadData.FunctorModel.baseChangeSpecMap, pullback.map,
      base, toStageX, toStageY, mapYX]
    rw [pullback.lift_snd]
  have hstage : mapYX ≫ toStageX = toStageY := by
    simpa only [mapYX, toStageX, toStageY, ← AlgebraicGeometry.Spec.map_comp] using
      (congrArg AlgebraicGeometry.Spec.map hbase).symm
  have houter : IsPullback
      (M.baseChangeSpecMap f ≫ pullback.fst base toStageX)
      (pullback.snd base toStageY) base (mapYX ≫ toStageX) := by
    simpa only [hmap_fst, hstage] using IsPullback.of_hasPullback base toStageY
  exact houter.of_right hmap_snd hright

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

/-- The original affine restriction square is cartesian over its modeled restriction square. -/
theorem SpreadData.FunctorModel.baseChangeSpecIso_inv_map_isPullback
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    IsPullback
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (F.map f).hom.toRingHom))
      ((M.baseChangeSpecIso Y).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage) (M.toFunctor.obj Y)))))
      ((M.baseChangeSpecIso X).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage) (M.toFunctor.obj X)))))
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom)) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  refine (M.baseChangeSpecMap_isPullback f).of_iso
    (M.baseChangeSpecIso Y) (M.baseChangeSpecIso X)
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact M.baseChangeSpecIso_naturality f
  · simp
  · simp
  · simp

/-- The inverses of the affine-scheme base-change comparisons are natural in the modeled
diagram. -/
theorem SpreadData.FunctorModel.baseChangeSpecIso_inv_naturality
    (M : SpreadData.FunctorModel F H) {X Y : J} (f : X ⟶ Y) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (F.map f).hom.toRingHom) ≫
        (M.baseChangeSpecIso X).inv =
      (M.baseChangeSpecIso Y).inv ≫ M.baseChangeSpecMap f := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  rw [← cancel_mono (M.baseChangeSpecIso X).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [M.baseChangeSpecIso_naturality f]
  simp

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
  rw [← Category.assoc, M.baseChangeSpecIso_inv_naturality f, Category.assoc]
  dsimp only [SpreadData.FunctorModel.baseChangeSpecMap, pullback.map]
  rw [pullback.lift_snd]

/-- The affine base-change comparisons intertwine the transition maps that exchange
ordered affine intersections. -/
theorem SpreadData.FunctorModel.baseChangeSpecIso_inv_affineIntersectionTransition
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
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
        (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
          M.toFunctor hopenM hpushM).t i j =
      (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
          G hopenG hpushG).t i j ≫
        (M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex j i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage)
                (M.toFunctor.obj
                  (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex j i))))) := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let f := AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairSwap i j
  change (M.baseChangeSpecIso
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
          (CommRingCat.ofHom (M.toFunctor.map f).hom.toRingHom) =
      AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (G.map f).hom.toRingHom) ≫
        (M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex j i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage)
                (M.toFunctor.obj
                  (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex j i)))))
  symm
  rw [← Category.assoc, M.baseChangeSpecIso_inv_naturality f, Category.assoc]
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

private theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChange_compatible
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i j : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
      M.toFunctor hopenM hpushM
    DG.f i j ≫
          (M.baseChangeSpecIso
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
          pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
              M.toFunctor i) ≫
          DM.ι i =
      DG.t i j ≫ DG.f j i ≫
          (M.baseChangeSpecIso
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex j)).inv ≫
          pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
              M.toFunctor j) ≫
          DM.ι j := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
    M.toFunctor hopenM hpushM
  have hi := M.baseChangeSpecIso_inv_affineIntersectionOverlapι i j
  have hj := M.baseChangeSpecIso_inv_affineIntersectionOverlapι j i
  have ht := M.baseChangeSpecIso_inv_affineIntersectionTransition
    hopenG hpushG hopenM hpushM i j
  have hi' := congrArg (fun q => q ≫ DM.ι i) hi
  have hj' := congrArg (fun q => DG.t i j ≫ q ≫ DM.ι j) hj
  have ht' := congrArg (fun q => q ≫ DM.f j i ≫ DM.ι j) ht
  change AlgebraicGeometry.Scheme.GlueData.affineIntersectionOverlapι G i j ≫
          (M.baseChangeSpecIso
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
          pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
              M.toFunctor i) ≫
          DM.ι i =
      DG.t i j ≫
        AlgebraicGeometry.Scheme.GlueData.affineIntersectionOverlapι G j i ≫
          (M.baseChangeSpecIso
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex j)).inv ≫
          pullback.snd
            (AlgebraicGeometry.Spec.map
              (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
            (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
              M.toFunctor j) ≫
          DM.ι j
  simp only [Category.assoc] at hi' hj' ht' ⊢
  rw [hi', ← DM.glue_condition i j, ht', ← hj']

/-- The original affine-intersection glue maps canonically to its finite-stage spread model. -/
noncomputable def SpreadData.FunctorModel.affineIntersectionGluedBaseChange
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
        G hopenG hpushG).glued ⟶
      (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
        M.toFunctor hopenM hpushM).glued := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
    M.toFunctor hopenM hpushM
  change DG.glued ⟶ DM.glued
  letI : HasMulticoequalizer DG.diagram :=
    _root_.AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram DG
  fapply Multicoequalizer.desc DG.diagram
  · intro i
    exact (M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
            M.toFunctor i) ≫
        DM.ι i
  rintro ⟨i, j⟩
  exact M.affineIntersectionGluedBaseChange_compatible
    hopenG hpushG hopenM hpushM i j

/-- On each singleton chart, the global spread morphism is the local affine base-change
comparison followed by the stage chart inclusion. -/
theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChange_ι
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
      M.toFunctor hopenM hpushM
    DG.ι i ≫ M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM =
      (M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
            M.toFunctor i) ≫
        DM.ι i := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
    M.toFunctor hopenM hpushM
  letI : HasMulticoequalizer DG.diagram :=
    _root_.AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram DG
  change Multicoequalizer.π DG.diagram i ≫ _ = _
  exact Multicoequalizer.π_desc _ _ _ _ _

/-- The global spread morphism commutes with the structural morphisms to the affine bases. -/
theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChange_toSpec
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM ≫
        AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
          M.toFunctor hopenM hpushM =
      AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec G hopenG hpushG ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)) := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  apply (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
    G hopenG hpushG).openCover.hom_ext
  rintro (i : K)
  change (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
      G hopenG hpushG).ι i ≫
      (M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM ≫
        AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
          M.toFunctor hopenM hpushM) =
    (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
      G hopenG hpushG).ι i ≫
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec G hopenG hpushG ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
  have hglobal := M.affineIntersectionGluedBaseChange_ι
    hopenG hpushG hopenM hpushM i
  have hstage :=
    AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor_ι_affineIntersectionToSpec
      M.toFunctor hopenM hpushM i
  have horiginal :=
    AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor_ι_affineIntersectionToSpec
      G hopenG hpushG i
  have hglobal' := congrArg (fun q => q ≫
    AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
      M.toFunctor hopenM hpushM) hglobal
  have hstage' := congrArg (fun q =>
    (M.baseChangeSpecIso
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
      pullback.snd
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
          M.toFunctor i) ≫ q) hstage
  have horiginal' := congrArg (fun q => q ≫
    AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))) horiginal
  simp only [Category.assoc] at hglobal' hstage' horiginal' ⊢
  rw [hglobal', hstage']
  change (M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage)
                (M.toFunctor.obj
                  (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i))))) ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap (𝒮 M.stage)
              (M.toFunctor.obj
                (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)))) = _
  rw [← pullback.condition, ← Category.assoc, M.baseChangeSpecIso_inv_fst]
  rw [horiginal']
  rfl

private theorem SpreadData.FunctorModel.baseChangeSpecIso_inv_affineIntersectionOverlapι_isPullback
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H) (i j : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    IsPullback
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionOverlapι G i j)
      ((M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex i j)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (algebraMap (𝒮 M.stage)
                (M.toFunctor.obj
                  (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex i j))))))
      ((M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec
            M.toFunctor i))
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionOverlapι
        M.toFunctor i j) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  exact M.baseChangeSpecIso_inv_map_isPullback
    (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonToPair i j)

private theorem SpreadData.FunctorModel.affineIntersectionChartBaseChange_isPullback
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H) (i : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    IsPullback
      ((M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i))
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec G i)
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i)
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  exact M.baseChangeSpecIso_inv_isPullback
    (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)

private theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChange_preimage_range_ι
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
      M.toFunctor hopenM hpushM
    (M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM).base ⁻¹'
        Set.range (DM.ι i).base =
      Set.range (DG.ι i).base := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
    M.toFunctor hopenM hpushM
  let base := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))
  let chartMap (k : K) : DG.U k ⟶ DM.U k :=
    (M.baseChangeSpecIso
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex k)).inv ≫
      pullback.snd base
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor k)
  let overlapMap (p q : K) : DG.V (p, q) ⟶ DM.V (p, q) :=
    (M.baseChangeSpecIso
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex p q)).inv ≫
      pullback.snd base
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap (𝒮 M.stage)
              (M.toFunctor.obj
                (AlgebraicGeometry.Scheme.GlueData.affineIntersectionPairIndex p q)))))
  have hglobal (k : K) :
      DG.ι k ≫ M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM =
        chartMap k ≫ DM.ι k := by
    exact M.affineIntersectionGluedBaseChange_ι hopenG hpushG hopenM hpushM k
  have hoverlap (p q : K) :
      IsPullback (DG.f p q) (overlapMap p q) (chartMap p) (DM.f p q) := by
    exact M.baseChangeSpecIso_inv_affineIntersectionOverlapι_isPullback p q
  ext x
  constructor
  · intro hx
    obtain ⟨j, y, rfl⟩ := DG.ι_jointly_surjective x
    obtain ⟨xi, hxi⟩ := hx
    have hglobal_apply :
        (M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM).base
            ((DG.ι j).base y) =
          (DM.ι j).base ((chartMap j).base y) := by
      simpa only [AlgebraicGeometry.Scheme.Hom.comp_apply] using
        congrArg (fun q => q.base y) (hglobal j)
    have heq : (DM.ι i).base xi = (DM.ι j).base ((chartMap j).base y) :=
      hxi.trans hglobal_apply
    obtain ⟨v, -, hvj⟩ := (DM.ι_eq_iff i j xi ((chartMap j).base y)).mp heq
    obtain ⟨vg, hvgj, -⟩ :=
      AlgebraicGeometry.Scheme.exists_preimage_of_isPullback
        (hoverlap j i) y ((DM.t i j).base v) (by
          simpa only [AlgebraicGeometry.Scheme.Hom.comp_apply] using hvj.symm)
    refine ⟨(DG.t j i ≫ DG.f i j).base vg, ?_⟩
    calc
      (DG.ι i).base ((DG.t j i ≫ DG.f i j).base vg) =
          (DG.ι j).base ((DG.f j i).base vg) := by
        simpa only [AlgebraicGeometry.Scheme.Hom.comp_apply] using
          congrArg (fun q => q.base vg) (DG.glue_condition j i)
      _ = (DG.ι j).base y := by rw [hvgj]
  · rintro ⟨y, rfl⟩
    refine ⟨(chartMap i).base y, ?_⟩
    simpa only [AlgebraicGeometry.Scheme.Hom.comp_apply] using
      (congrArg (fun q => q.base y) (hglobal i)).symm

/-- Each singleton chart square of the affine-intersection glued base-change morphism is a
pullback. -/
theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChange_chart_isPullback
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor)
    (i : K) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
    let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
      M.toFunctor hopenM hpushM
    IsPullback
      ((M.baseChangeSpecIso
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
        pullback.snd
          (AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A)))
          (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i))
      (DG.ι i) (DM.ι i)
      (M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM) := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
    M.toFunctor hopenM hpushM
  letI : AlgebraicGeometry.IsOpenImmersion (DG.ι i) :=
    AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion DG i
  letI : AlgebraicGeometry.IsOpenImmersion (DM.ι i) :=
    AlgebraicGeometry.Scheme.GlueData.ι_isOpenImmersion DM i
  refine AlgebraicGeometry.IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · exact M.affineIntersectionGluedBaseChange_ι hopenG hpushG hopenM hpushM i
  · apply TopologicalSpace.Opens.ext
    exact M.affineIntersectionGluedBaseChange_preimage_range_ι
      hopenG hpushG hopenM hpushM i

/-- The original glued affine-intersection scheme is the base change of its finite-stage
spread model. -/
theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChange_isPullback
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    IsPullback
      (M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM)
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec G hopenG hpushG)
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
        M.toFunctor hopenM hpushM)
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))) := by
  classical
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let DG := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor G hopenG hpushG
  let DM := AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
    M.toFunctor hopenM hpushM
  let global := M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM
  let toBaseG := AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec G hopenG hpushG
  let toBaseM := AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
    M.toFunctor hopenM hpushM
  let base := AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))
  apply AlgebraicGeometry.Scheme.isPullback_of_openCover
    global toBaseG toBaseM base DM.openCover
  rintro (i : K)
  let chartMap : DG.U i ⟶ DM.U i :=
    (M.baseChangeSpecIso
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).inv ≫
      pullback.snd base
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i)
  have hchart : IsPullback chartMap (DG.ι i) (DM.ι i) global :=
    M.affineIntersectionGluedBaseChange_chart_isPullback
      hopenG hpushG hopenM hpushM i
  have hlocal : IsPullback chartMap
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec G i)
      (AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i)
      base := M.affineIntersectionChartBaseChange_isPullback i
  let e : DG.U i ≅ (DM.openCover.pullback₁ global).X i :=
    hchart.isoPullback ≪≫ pullbackSymmetry (DM.ι i) global
  have e_snd :
      e.hom ≫ pullback.snd global (DM.ι i) = chartMap := by
    change (hchart.isoPullback.hom ≫ (pullbackSymmetry (DM.ι i) global).hom) ≫
      pullback.snd global (DM.ι i) = chartMap
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd,
      hchart.isoPullback_hom_fst]
  have e_fst :
      e.hom ≫ pullback.fst global (DM.ι i) = DG.ι i := by
    change (hchart.isoPullback.hom ≫ (pullbackSymmetry (DM.ι i) global).hom) ≫
      pullback.fst global (DM.ι i) = DG.ι i
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
      hchart.isoPullback_hom_snd]
  refine hlocal.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · change chartMap = e.hom ≫ pullback.snd global (DM.ι i)
    exact e_snd.symm
  · change AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec G i =
      e.hom ≫ pullback.fst global (DM.ι i) ≫ toBaseG
    rw [← Category.assoc, e_fst]
    exact
      (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor_ι_affineIntersectionToSpec
        G hopenG hpushG i).symm
  · change AlgebraicGeometry.Scheme.GlueData.affineIntersectionChartToSpec M.toFunctor i =
      DM.ι i ≫ toBaseM
    exact
      (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor_ι_affineIntersectionToSpec
        M.toFunctor hopenM hpushM i).symm
  · change base = base
    rfl

/-- The canonical comparison from the base change of the finite-stage glued model to the
original glued affine-intersection scheme. -/
noncomputable def SpreadData.FunctorModel.affineIntersectionGluedBaseChangeIso
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    pullback
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
          M.toFunctor hopenM hpushM)
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))) ≅
      (AlgebraicGeometry.Scheme.GlueData.ofAffineIntersectionFunctor
        G hopenG hpushG).glued := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  exact (M.affineIntersectionGluedBaseChange_isPullback
    hopenG hpushG hopenM hpushM).isoPullback.symm

@[reassoc]
theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChangeIso_hom_fst
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    (M.affineIntersectionGluedBaseChangeIso hopenG hpushG hopenM hpushM).hom ≫
        M.affineIntersectionGluedBaseChange hopenG hpushG hopenM hpushM =
      pullback.fst
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
          M.toFunctor hopenM hpushM)
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let h := M.affineIntersectionGluedBaseChange_isPullback
    hopenG hpushG hopenM hpushM
  change h.isoPullback.inv ≫ _ = _
  rw [← cancel_epi h.isoPullback.hom]
  simp only [Iso.hom_inv_id_assoc, h.isoPullback_hom_fst]

@[reassoc]
theorem SpreadData.FunctorModel.affineIntersectionGluedBaseChangeIso_hom_snd
    {K : Type u} {G : Finset K ⥤ CommAlgCat.{u} A}
    (M : SpreadData.FunctorModel G H)
    (hopenG : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hopenM : AlgebraicGeometry.Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
    (hpushM : AlgebraicGeometry.Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor) :
    letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
    (M.affineIntersectionGluedBaseChangeIso hopenG hpushG hopenM hpushM).hom ≫
        AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec G hopenG hpushG =
      pullback.snd
        (AlgebraicGeometry.Scheme.GlueData.affineIntersectionToSpec
          M.toFunctor hopenM hpushM)
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap (𝒮 M.stage) A))) := by
  letI : Algebra (𝒮 M.stage) A := (uA M.stage).toRingHom.toAlgebra
  let h := M.affineIntersectionGluedBaseChange_isPullback
    hopenG hpushG hopenM hpushM
  change h.isoPullback.inv ≫ _ = _
  rw [← cancel_epi h.isoPullback.hom]
  simp only [Iso.hom_inv_id_assoc, h.isoPullback_hom_snd]

end

end Algebra
