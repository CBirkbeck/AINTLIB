/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpacePositiveTwistCechVanishing
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistPushforward
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-!
# Positive-twist Cech vanishing on projective closed subschemes

The projective-space positive-twist vanishing theorem transfers to a closed
subscheme by pushforward, the projective-twist projection formula, and the
ordered-Cech comparison for an inverse-image cover.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory HomogeneousIdeal MonoidalCategory
  TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance closedPositiveTwistMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

/-- A finite-type quasicoherent module on a closed subscheme of polynomial
projective space has exact inverse-image-cover ordered-Cech complex in each
fixed positive degree after every sufficiently large pulled-back positive
coordinate twist. -/
theorem closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (q : ℕ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N →
      (Scheme.Modules.orderedBaseCechComplex
        (f ≫ homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ (Scheme.Modules.pullback f).obj
          (coordinateHyperplanePoleSheafPower (R := R) j N))
        (fun i => f ⁻¹ᵁ coordinateOpenCover
          (R := R) (σ := σ) i)).ExactAt (q + 1) := by
  let N := (Scheme.Modules.pushforward f).obj M
  letI : N.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  letI : N.IsFiniteType :=
    Scheme.Modules.isFiniteType_pushforward_of_isClosedImmersion f
  obtain ⟨b, hb⟩ :=
    finiteType_eventually_orderedBaseCechComplex_exactAt_succ N j q
  refine ⟨b, fun n hn ↦ ?_⟩
  let P := coordinateHyperplanePoleSheafPower (R := R) j n
  let T : X.Modules := M ⊗ (Scheme.Modules.pullback f).obj P
  let ePF : N ⊗ P ≅ (Scheme.Modules.pushforward f).obj T :=
    (coordinateHyperplanePoleSheafPowerPushforwardTensorIso f j n).app M
  let F := Scheme.Modules.orderedBaseCechComplexFunctor
    (homogeneousProjπ (R := R) (σ := σ))
    (coordinateOpenCover (R := R) (σ := σ))
  let eC :
      Scheme.Modules.orderedBaseCechComplex
          (f ≫ homogeneousProjπ (R := R) (σ := σ)) T
          (fun i => f ⁻¹ᵁ coordinateOpenCover
            (R := R) (σ := σ) i) ≅
        Scheme.Modules.orderedBaseCechComplex
          (homogeneousProjπ (R := R) (σ := σ)) (N ⊗ P)
          (coordinateOpenCover (R := R) (σ := σ)) :=
    Scheme.Modules.orderedBaseCechComplexPushforwardIso f
        (homogeneousProjπ (R := R) (σ := σ)) T
        (coordinateOpenCover (R := R) (σ := σ)) ≪≫
      (F.mapIso ePF).symm
  have hN := hb n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hN ⊢
  exact
    (HomologicalComplex.homologyMapIso eC (q + 1)).isZero_iff.mpr hN

end

end MvPolynomial
