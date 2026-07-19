/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Picard.InvertibleSheafGlueBaseChange

/-!
# Noetherian finite-stage models of invertible sheaves

The canonical presentation system over the universe-lifted integers writes the coordinate ring
of an affine base as a filtered colimit of Noetherian finitely presented rings. Specializing the
existing finite-stage descent theorem to this system gives a Noetherian separated model of a
proper family and its invertible sheaf. Properness of the stage model is not asserted here.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

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

end

end AlgebraicGeometry.Scheme.Modules
