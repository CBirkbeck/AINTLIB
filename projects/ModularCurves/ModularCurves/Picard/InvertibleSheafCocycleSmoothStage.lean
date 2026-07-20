import ModularCurves.ForMathlib.SmoothFinitePresentationSchemeGlueData
import ModularCurves.Picard.InvertibleSheafCocycleBaseChange

/-!
# Smooth finite-stage affine-intersection cocycle models

This file synchronizes descent of an affine-intersection unit cocycle with smoothness of
the singleton affine charts and the geometric conditions required to glue those charts.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- A cocycle on a smooth separated finite affine-intersection functor descends to one
stage where the open, pushout, separatedness, and smoothness conditions all hold. -/
theorem AffineIntersectionUnitCocycle.exists_modelWithAffineIntersectionConditionsAndSeparatedAndSmooth
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, Sstage i →ₐ[R] A}
    {J : Type u} [Finite J] {G : Functor (Finset J) (CommAlgCat.{u} A)}
    (c : AffineIntersectionUnitCocycle G)
    (H : Algebra.IsFilteredAlgColimit R Sstage t A uA)
    (M : Algebra.SpreadData.FunctorModel G H)
    (hopenG : Scheme.GlueData.IsOpenAffineIntersectionFunctor G)
    (hpushG : Scheme.GlueData.IsPushoutAffineIntersectionFunctor G)
    (hsepG : Scheme.GlueData.IsSeparatedAffineIntersectionFunctor G)
    (hsmoothG : ∀ i : J,
      Algebra.Smooth A
        (G.obj (Scheme.GlueData.affineIntersectionSingletonIndex i))) :
    ∃ (M' : Algebra.SpreadData.FunctorModel G H)
      (hopenM' : Scheme.GlueData.IsOpenAffineIntersectionFunctor M'.toFunctor)
      (hpushM' : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M'.toFunctor)
      (_hsepM' : Scheme.GlueData.IsSeparatedAffineIntersectionFunctor M'.toFunctor)
      (cM' : AffineIntersectionUnitCocycle M'.toFunctor),
      Smooth (Scheme.GlueData.affineIntersectionToSpec
        M'.toFunctor hopenM' hpushM') ∧
        ∀ i j, (AffineIntersectionUnitCocycle.mapToColimit M' cM').transition i j =
          c.transition i j := by
  obtain ⟨M₀, hopenM₀, hpushM₀, hsepM₀, cM₀, htransition⟩ :=
    c.exists_modelWithAffineIntersectionConditionsAndSeparated
      H M hopenG hpushG hsepG
  obtain ⟨q, hM₀q, hsmoothLater⟩ :=
    M₀.exists_smoothSingletonsAtLaterStage hsmoothG
  let Mq := M₀.mapToStage hM₀q
  obtain ⟨r, hqr, hopenMr, hpushMr, hsepMr⟩ :=
    Mq.exists_affineIntersectionConditionsAndSeparatedAtLaterStage
      hopenG hpushG hsepG
  let Mr := Mq.mapToStage hqr
  let cMq := AffineIntersectionUnitCocycle.mapToStage M₀ cM₀ hM₀q
  let cMr := AffineIntersectionUnitCocycle.mapToStage Mq cMq hqr
  have hsmoothMr (i : J) :
      Algebra.Smooth (Sstage Mr.stage)
        (Mr.toFunctor.obj (Scheme.GlueData.affineIntersectionSingletonIndex i)) := by
    change Algebra.Smooth (Sstage r)
      ((M₀.object (Scheme.GlueData.affineIntersectionSingletonIndex i)).spreadStage
        (t := t)
        ((M₀.le_stage (Scheme.GlueData.affineIntersectionSingletonIndex i)).trans
          (hM₀q.trans hqr)))
    exact hsmoothLater hqr i
  have hsmoothMrGlued : Smooth
      (Scheme.GlueData.affineIntersectionToSpec Mr.toFunctor hopenMr hpushMr) :=
    Scheme.GlueData.smooth_affineIntersectionToSpec
      Mr.toFunctor hopenMr hpushMr hsmoothMr
  refine ⟨Mr, hopenMr, hpushMr, hsepMr, cMr, hsmoothMrGlued, fun i j => ?_⟩
  calc
    (AffineIntersectionUnitCocycle.mapToColimit Mr cMr).transition i j =
        (AffineIntersectionUnitCocycle.mapToColimit Mq cMq).transition i j :=
      AffineIntersectionUnitCocycle.mapToColimit_mapToStage_transition
        Mq cMq hqr i j
    _ = (AffineIntersectionUnitCocycle.mapToColimit M₀ cM₀).transition i j :=
      AffineIntersectionUnitCocycle.mapToColimit_mapToStage_transition
        M₀ cM₀ hM₀q i j
    _ = c.transition i j := htransition i j

end

end AlgebraicGeometry.Scheme.Modules
