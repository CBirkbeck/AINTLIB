import ModularCurves.ForMathlib.SmoothFinitePresentationSchemeGlueData
import ModularCurves.Picard.InvertibleSheafGlueBaseChange

/-!
# Smooth finite-stage affine-intersection cocycle models

This file synchronizes descent of an affine-intersection unit cocycle with smoothness of
the singleton affine charts and the geometric conditions required to glue those charts.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

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

/-- An invertible sheaf on a smooth proper, locally finitely presented family descends to
a smooth separated finite-presentation stage model, compatibly with base change. -/
theorem IsInvertible.exists_finiteStageModelOfFinitePresentationSeparatedSmoothBaseChangeIso_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {ι : Type u} [Preorder ι]
    {Sstage : ι → Type u} [∀ i, CommRing (Sstage i)] [∀ i, Algebra R (Sstage i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (Sstage i →ₐ[R] Sstage j)}
    {X S : Scheme.{u}} {π : X ⟶ S} [IsProper π] [Smooth π] [IsAffine S]
    [LocallyOfFinitePresentation π] [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, Sstage i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    {N : X.Modules} (hN : IsInvertible N)
    (H : Algebra.IsFilteredAlgColimit R Sstage t Γ(S, (⊤ : S.Opens)) uS) :
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
        Smooth
          (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM) ∧
        IsInvertible (cM.gluedModule hopenM hpushM) ∧
          Nonempty
            (letI : Algebra (Sstage M.stage) Γ(S, (⊤ : S.Opens)) :=
                (uS M.stage).toRingHom.toAlgebra
              let stageToBase := Spec.map (CommRingCat.ofHom
                (algebraMap (Sstage M.stage) Γ(S, (⊤ : S.Opens))))
              let p := CategoryTheory.Limits.pullback.fst
                (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM)
                stageToBase
              let φ := π.affineIntersectionModelBaseChangeIso
                U hcover hU M hopenM hpushM
              (AlgebraicGeometry.Scheme.Modules.pullback p).obj
                  (cM.gluedModule hopenM hpushM) ≅
                (AlgebraicGeometry.Scheme.Modules.pullback φ.hom).obj N) := by
  classical
  obtain ⟨J, hJ, U, hcover, _, htriv, hU, M₀, _, _, _⟩ :=
    hN.exists_affineIntersectionModelBaseChangeIso_of_isProper (π := π) H
  letI : Finite J := hJ
  let e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme :=
    fun i => Classical.choice (htriv i)
  let c := affineIntersectionUnitCocycle π U e
  let hopenG := π.isOpenAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hpushG := π.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor U hU
  let hsepG :=
    π.isSeparatedAffineIntersectionFunctor_affineIntersectionFunctor_of_isProper
      U hcover hU
  let hsmoothG (i : J) :
      Algebra.Smooth Γ(S, (⊤ : S.Opens))
        ((π.affineIntersectionFunctor U).obj
          (Scheme.GlueData.affineIntersectionSingletonIndex i)) :=
    π.affineIntersectionFunctor_obj_smooth U hU _
  obtain ⟨M, hopenM, hpushM, hsepM, cM, hsmoothM, htransition⟩ :=
    c.exists_modelWithAffineIntersectionConditionsAndSeparatedAndSmooth
      H M₀ hopenG hpushG hsepG hsmoothG
  refine ⟨J, hJ, U, hcover, hU, M, hopenM, hpushM, hsepM, cM,
    _root_.AlgebraicGeometry.Algebra.SpreadData.FunctorModel.locallyOfFinitePresentation_affineIntersectionToSpec
      M hopenM hpushM,
    _root_.AlgebraicGeometry.Algebra.SpreadData.FunctorModel.quasiCompact_affineIntersectionToSpec
      M hopenM hpushM,
    Scheme.GlueData.isSeparated_affineIntersectionToSpec
      M.toFunctor hopenM hpushM hsepM,
    hsmoothM,
    cM.gluedModule_isInvertible hopenM hpushM, ?_⟩
  exact ⟨AffineIntersectionUnitCocycle.baseChangeGluedModuleIsoOnModelPullback
    π U hcover e hU M cM hopenM hpushM htransition⟩

end

end AlgebraicGeometry.Scheme.Modules
