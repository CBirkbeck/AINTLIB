import ModularCurves.ForMathlib.FinitePresentationFunctorCover
import ModularCurves.ForMathlib.FinitePresentationSchemeGlueData

/-!
# Finite-stage affine-intersection unit cocycles

This file defines multiplicative cocycles on finite affine-intersection diagrams and
descends their finite collection of transition units and cocycle equations through a
filtered colimit.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Multiplicative descent data on the pair and triple objects of an affine-intersection
algebra functor. -/
structure AffineIntersectionUnitCocycle
    {A J : Type u} [CommRing A] (F : Finset J ⥤ CommAlgCat.{u} A) where
  transition : ∀ i j,
    (F.obj (Scheme.GlueData.affineIntersectionPairIndex i j))ˣ
  cocycle : ∀ i j k,
    Units.map (F.map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).hom.toMonoidHom
        (transition i j) *
      Units.map (F.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).hom.toMonoidHom
        (transition j k) =
    Units.map (F.map
        (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).hom.toMonoidHom
      (transition i k)

private theorem map_units_mul_eq_of_mul_eq
    {B C : Type u} [Monoid B] [Monoid C] (f : B →* C)
    {x y z : Bˣ} (h : x * y = z) :
    Units.map f x * Units.map f y = Units.map f z := by
  rw [← map_mul, h]

/-- Transport a finite-stage affine-intersection unit cocycle to a later stage. -/
noncomputable def AffineIntersectionUnitCocycle.mapToStage
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A]
    {uA : ∀ i, 𝒮 i →ₐ[R] A} {J : Type u}
    {F : Finset J ⥤ CommAlgCat.{u} A}
    {H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA}
    (M : Algebra.SpreadData.FunctorModel F H)
    (c : AffineIntersectionUnitCocycle M.toFunctor)
    {j : ι} (hMj : M.stage ≤ j) :
    AffineIntersectionUnitCocycle (M.mapToStage hMj).toFunctor := by
  let g (i k : J) :
      ((M.object
        (Scheme.GlueData.affineIntersectionPairIndex i k)).spreadStage (t := t)
          (M.le_stage (Scheme.GlueData.affineIntersectionPairIndex i k)))ˣ :=
    c.transition i k
  refine
    { transition := fun i k =>
        Units.map ((M.object
          (Scheme.GlueData.affineIntersectionPairIndex i k)).stageTransition H
            (P := ⟨M.stage, M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i k)⟩)
            (Q := ⟨j, (M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i k)).trans hMj⟩)
            hMj).toMonoidHom (g i k)
      cocycle := ?_ }
  intro i k l
  have hc := c.cocycle i k l
  change Units.map (M.map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i k l)).toMonoidHom
        (g i k) *
      Units.map (M.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i k l)).toMonoidHom
        (g k l) =
      Units.map (M.map
          (Scheme.GlueData.affineIntersectionPairToTripleRight i k l)).toMonoidHom
        (g i l) at hc
  change Units.map ((M.mapToStage hMj).map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i k l)).toMonoidHom
        (Units.map ((M.object
          (Scheme.GlueData.affineIntersectionPairIndex i k)).stageTransition H
            (P := ⟨M.stage, M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i k)⟩)
            (Q := ⟨j, (M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i k)).trans hMj⟩)
            hMj).toMonoidHom (g i k)) *
      Units.map ((M.mapToStage hMj).map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i k l)).toMonoidHom
        (Units.map ((M.object
          (Scheme.GlueData.affineIntersectionPairIndex k l)).stageTransition H
            (P := ⟨M.stage, M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex k l)⟩)
            (Q := ⟨j, (M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex k l)).trans hMj⟩)
            hMj).toMonoidHom (g k l)) =
      Units.map ((M.mapToStage hMj).map
          (Scheme.GlueData.affineIntersectionPairToTripleRight i k l)).toMonoidHom
        (Units.map ((M.object
          (Scheme.GlueData.affineIntersectionPairIndex i l)).stageTransition H
            (P := ⟨M.stage, M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i l)⟩)
            (Q := ⟨j, (M.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i l)).trans hMj⟩)
            hMj).toMonoidHom (g i l))
  rw [M.mapToStage_map_unitTransition hMj
      (Scheme.GlueData.affineIntersectionPairToTripleLeft i k l),
    M.mapToStage_map_unitTransition hMj
      (Scheme.GlueData.affineIntersectionPairToTripleMiddle i k l),
    M.mapToStage_map_unitTransition hMj
      (Scheme.GlueData.affineIntersectionPairToTripleRight i k l)]
  exact map_units_mul_eq_of_mul_eq
    ((M.object
      (Scheme.GlueData.affineIntersectionTripleIndex i k l)).stageTransition H
        (P := ⟨M.stage, M.le_stage
          (Scheme.GlueData.affineIntersectionTripleIndex i k l)⟩)
        (Q := ⟨j, (M.le_stage
          (Scheme.GlueData.affineIntersectionTripleIndex i k l)).trans hMj⟩)
        hMj).toMonoidHom hc

/-- A finite affine-intersection unit cocycle over a filtered colimit descends to a common
finite stage, retaining both its transition units and all triple equations. -/
theorem AffineIntersectionUnitCocycle.exists_modelAtLaterStage
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A]
    {uA : ∀ i, 𝒮 i →ₐ[R] A} {J : Type u} [Finite J]
    {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA)
    (M : Algebra.SpreadData.FunctorModel F H) :
    ∃ (q : ι) (hiq : M.stage ≤ q) (r : ι) (hqr : q ≤ r)
        (c_r : AffineIntersectionUnitCocycle
          (((M.mapToStage hiq).mapToStage hqr).toFunctor)),
      ∀ i j, Units.map (((M.mapToStage hiq).object
          (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
            ⟨r, ((M.mapToStage hiq).le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩).toMonoidHom
          (c_r.transition i j) = c.transition i j := by
  classical
  let pairObj : J × J → Finset J := fun p =>
    Scheme.GlueData.affineIntersectionPairIndex p.1 p.2
  let pairUnit : ∀ p, (F.obj (pairObj p))ˣ := fun p =>
    c.transition p.1 p.2
  obtain ⟨q, hiq, gq, hgq⟩ :=
    M.exists_common_unit_liftAtLaterStage pairObj pairUnit
  let Mq := M.mapToStage hiq
  let g (i j : J) :
      ((Mq.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
          (Mq.le_stage (Scheme.GlueData.affineIntersectionPairIndex i j)))ˣ :=
    gq (i, j)
  have hg (i j : J) :
      Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
            ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)⟩).toMonoidHom
          (g i j) = c.transition i j := by
    apply Units.ext
    change (M.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
          ⟨q, (M.le_stage
            (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hiq⟩
          (gq (i, j) : (M.object
            (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
              ((M.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hiq)) =
      (c.transition i j : F.obj
        (Scheme.GlueData.affineIntersectionPairIndex i j))
    exact congrArg Units.val (hgq (i, j))
  let tripleObj : J × (J × J) → Finset J := fun p =>
    Scheme.GlueData.affineIntersectionTripleIndex p.1 p.2.1 p.2.2
  let x : ∀ p : J × (J × J),
      ((Mq.object (tripleObj p)).spreadStage (t := t)
        (Mq.le_stage (tripleObj p)))ˣ := fun p =>
    Units.map (Mq.map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft
            p.1 p.2.1 p.2.2)).toMonoidHom (g p.1 p.2.1) *
      Units.map (Mq.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle
            p.1 p.2.1 p.2.2)).toMonoidHom (g p.2.1 p.2.2)
  let y : ∀ p : J × (J × J),
      ((Mq.object (tripleObj p)).spreadStage (t := t)
        (Mq.le_stage (tripleObj p)))ˣ := fun p =>
    Units.map (Mq.map
        (Scheme.GlueData.affineIntersectionPairToTripleRight
          p.1 p.2.1 p.2.2)).toMonoidHom (g p.1 p.2.2)
  have hxy : ∀ p, Units.map ((Mq.object (tripleObj p)).stageToColimit H
        ⟨Mq.stage, Mq.le_stage (tripleObj p)⟩).toMonoidHom (x p) =
      Units.map ((Mq.object (tripleObj p)).stageToColimit H
        ⟨Mq.stage, Mq.le_stage (tripleObj p)⟩).toMonoidHom (y p) := by
    rintro ⟨i, ⟨j, k⟩⟩
    dsimp only [x, y, tripleObj]
    rw [map_mul, Mq.map_unit_colimit, Mq.map_unit_colimit,
      Mq.map_unit_colimit, hg i j, hg j k, hg i k]
    exact c.cocycle i j k
  obtain ⟨r, hqr, hcocycle⟩ :=
    Mq.exists_common_unit_eq_atLaterStage tripleObj x y hxy
  have hcocycle_r (i j k : J) :
      Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)).trans hqr⟩)
            hqr).toMonoidHom
          (Units.map (Mq.map
            (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).toMonoidHom
              (g i j)) *
        Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)).trans hqr⟩)
            hqr).toMonoidHom
          (Units.map (Mq.map
            (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).toMonoidHom
              (g j k)) =
        Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)).trans hqr⟩)
            hqr).toMonoidHom
          (Units.map (Mq.map
            (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).toMonoidHom
              (g i k)) := by
    rw [← map_mul]
    simpa only [x, y, tripleObj] using hcocycle (i, (j, k))
  let gr (i j : J) :
      ((Mq.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
          ((Mq.le_stage
            (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr))ˣ :=
    Units.map ((Mq.object
      (Scheme.GlueData.affineIntersectionPairIndex i j)).stageTransition H
        (P := ⟨Mq.stage, Mq.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)⟩)
        (Q := ⟨r, (Mq.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩)
        hqr).toMonoidHom (g i j)
  let c_r : AffineIntersectionUnitCocycle (Mq.mapToStage hqr).toFunctor := {
    transition := gr
    cocycle := by
      intro i j k
      dsimp only [gr]
      change Units.map ((Mq.mapToStage hqr).map
            (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).toMonoidHom
          (Units.map ((Mq.object
            (Scheme.GlueData.affineIntersectionPairIndex i j)).stageTransition H
              (P := ⟨Mq.stage, Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i j)⟩)
              (Q := ⟨r, (Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩)
              hqr).toMonoidHom (g i j)) *
        Units.map ((Mq.mapToStage hqr).map
            (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).toMonoidHom
          (Units.map ((Mq.object
            (Scheme.GlueData.affineIntersectionPairIndex j k)).stageTransition H
              (P := ⟨Mq.stage, Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex j k)⟩)
              (Q := ⟨r, (Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex j k)).trans hqr⟩)
              hqr).toMonoidHom (g j k)) =
        Units.map ((Mq.mapToStage hqr).map
            (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).toMonoidHom
          (Units.map ((Mq.object
            (Scheme.GlueData.affineIntersectionPairIndex i k)).stageTransition H
              (P := ⟨Mq.stage, Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i k)⟩)
              (Q := ⟨r, (Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i k)).trans hqr⟩)
              hqr).toMonoidHom (g i k))
      rw [Mq.mapToStage_map_unitTransition hqr
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k),
        Mq.mapToStage_map_unitTransition hqr
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k),
        Mq.mapToStage_map_unitTransition hqr
          (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)]
      exact hcocycle_r i j k }
  refine ⟨q, hiq, r, hqr, c_r, fun i j => ?_⟩
  apply Units.ext
  change (Mq.object
      (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
        ⟨r, (Mq.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩
        ((Mq.object
          (Scheme.GlueData.affineIntersectionPairIndex i j)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩)
            hqr (g i j : (Mq.object
              (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
                (Mq.le_stage
                  (Scheme.GlueData.affineIntersectionPairIndex i j)))) =
    (c.transition i j : F.obj
      (Scheme.GlueData.affineIntersectionPairIndex i j))
  exact ((Mq.object
    (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit_stageTransition H
      (Mq.le_stage (Scheme.GlueData.affineIntersectionPairIndex i j)) hqr
      (g i j : (Mq.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
          (Mq.le_stage (Scheme.GlueData.affineIntersectionPairIndex i j)))).trans
          (congrArg Units.val (hg i j))

end

end AlgebraicGeometry.Scheme.Modules
