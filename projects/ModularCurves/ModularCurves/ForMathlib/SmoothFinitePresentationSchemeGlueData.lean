import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ModularCurves.ForMathlib.FinitePresentationSchemeGlueData
import ModularCurves.ForMathlib.SmoothFinitePresentationDescent

/-!
# Smooth affine-intersection models over filtered-colimit stages

This file transports smoothness of the singleton affine charts of an affine-intersection
functor to its glued structural morphism. It also synchronizes smooth spread models for a
finite family of singleton charts at one stage of a filtered algebra system.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.GlueData

noncomputable section

variable {S J : Type u} [CommRing S]

/-- If every singleton chart algebra of an affine-intersection functor is smooth over the
base, then the structural morphism of the glued scheme is smooth. -/
theorem smooth_affineIntersectionToSpec
    (F : Finset J ⥤ CommAlgCat.{u} S)
    (hopen : IsOpenAffineIntersectionFunctor F)
    (hpush : IsPushoutAffineIntersectionFunctor F)
    (hsmooth : ∀ i : J,
      Algebra.Smooth S (F.obj (affineIntersectionSingletonIndex i))) :
    Smooth (affineIntersectionToSpec F hopen hpush) := by
  letI : IsZariskiLocalAtSource
      (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply IsZariskiLocalAtSource.of_openCover
    (P := (@Smooth : MorphismProperty Scheme.{u}))
    (ofAffineIntersectionFunctor F hopen hpush).openCover
  intro i
  change J at i
  change Smooth
    ((ofAffineIntersectionFunctor F hopen hpush).ι i ≫
      affineIntersectionToSpec F hopen hpush)
  rw [ofAffineIntersectionFunctor_ι_affineIntersectionToSpec]
  change Smooth
    (Spec.map (CommRingCat.ofHom
      (algebraMap S (F.obj (affineIntersectionSingletonIndex i)))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (hsmooth i)

end


end AlgebraicGeometry.Scheme.GlueData

namespace Algebra

noncomputable section

variable {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
  {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
  {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
  {S : Type u} [CommRing S] [Algebra R S] {uS : ∀ i, 𝒮 i →ₐ[R] S}
  {J : Type u} {F : Finset J ⥤ CommAlgCat.{u} S}
  {H : IsFilteredAlgColimit R 𝒮 t S uS}

/-- If the singleton objects of a finite affine-intersection functor are smooth over the
filtered colimit, their chosen spread models are smooth at one common stage and at every
later stage. -/
theorem SpreadData.FunctorModel.exists_smoothSingletonsAtLaterStage
    [Finite J] [IsNoetherianRing R]
    (M : SpreadData.FunctorModel F H)
    (hsmooth : ∀ i : J,
      Smooth S
        (F.obj (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i))) :
    ∃ (j : ι) (hMj : M.stage ≤ j),
      ∀ ⦃k : ι⦄ (hjk : j ≤ k) (i : J),
        Smooth (𝒮 k)
          ((M.object
              (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).spreadStage
            (t := t)
            ((M.le_stage
                (AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i)).trans
              (hMj.trans hjk))) := by
  classical
  let idx (i : J) : Finset J :=
    AlgebraicGeometry.Scheme.GlueData.affineIntersectionSingletonIndex i
  have hstage (i : J) :
      ∃ (j : ι) (hj : (M.object (idx i)).i₀ ≤ j),
        ∀ ⦃k : ι⦄ (hjk : j ≤ k),
          Smooth (𝒮 k)
            ((M.object (idx i)).spreadStage (t := t) (hj.trans hjk)) := by
    letI : Algebra R (F.obj (idx i)) :=
      ((algebraMap S (F.obj (idx i))).comp (algebraMap R S)).toAlgebra
    letI : IsScalarTower R S (F.obj (idx i)) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      rfl
    letI : Smooth S (F.obj (idx i)) := hsmooth i
    exact (M.object (idx i)).exists_smooth_stage H
  let stage (i : J) : ι := (hstage i).choose
  have hobject (i : J) : (M.object (idx i)).i₀ ≤ stage i :=
    (hstage i).choose_spec.1
  have hsmoothLater (i : J) :
      ∀ ⦃k : ι⦄ (hik : stage i ≤ k),
        Smooth (𝒮 k)
          ((M.object (idx i)).spreadStage (t := t) ((hobject i).trans hik)) :=
    (hstage i).choose_spec.2
  letI : Fintype J := Fintype.ofFinite J
  haveI := H.directed
  haveI := H.nonempty
  obtain ⟨j, hj⟩ :=
    (insert M.stage (Finset.univ.image stage)).exists_le
  have hMj : M.stage ≤ j := hj M.stage (Finset.mem_insert_self _ _)
  have hstagej (i : J) : stage i ≤ j :=
    hj (stage i)
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem stage (Finset.mem_univ i)))
  refine ⟨j, hMj, ?_⟩
  intro k hjk i
  exact hsmoothLater i ((hstagej i).trans hjk)

end

end Algebra
