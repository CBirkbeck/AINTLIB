/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import ModularCurves.EllipticCurve.ProjectiveSpacePositiveTwistQuasicoherent
import ModularCurves.EllipticCurve.ProjectiveSpacePositiveTwistTensorCech
import ModularCurves.EllipticCurve.ProjectiveSpaceTwistShiftedPresentation
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechExact
import ModularCurves.ForMathlib.SheafModuleFiniteTypeQuotient
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-!
# Cech vanishing after a sufficiently positive projective twist

Over a Noetherian coefficient ring, every finite-type quasicoherent module
on polynomial projective space has exact ordered-Cech complex in a fixed
positive degree after all sufficiently large positive twists.

The proof uses finite presentations by coordinate twists and shifts
exactness along their kernels. The induction terminates at the cardinality
bound for the finite standard coordinate cover.
-/

namespace MvPolynomial

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
  MonoidalCategory Opposite TopologicalSpace

noncomputable section

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance positiveTwistVanishingMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

private theorem orderedBaseCechComplex_exactAt_of_iso
    [Fintype σ] [LinearOrder σ]
    {M N : (Proj (homogeneousSubmodule σ R)).Modules}
    (e : M ≅ N) (q : ℕ)
    (hN : (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ)) N
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt q) :
    (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
      (homogeneousProjπ (R := R) (σ := σ)) M
      (coordinateOpenCover (R := R) (σ := σ))).ExactAt q := by
  let F :=
    AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplexFunctor
      (homogeneousProjπ (R := R) (σ := σ))
      (coordinateOpenCover (R := R) (σ := σ))
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at hN ⊢
  exact
    (HomologicalComplex.homologyMapIso (F.mapIso e) q).isZero_iff.mpr hN

private theorem shortExact_exactAt_X3_of_exactAt_X2_X1
    {A : Type u} [Category A] [Abelian A]
    {ι : Type} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex A c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
    (h₂ : S.X₂.ExactAt i) (h₁ : S.X₁.ExactAt j) :
    S.X₃.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₁ h₂ ⊢
  exact
    (hS.homology_exact₃ i j hij).isZero_X₂
      (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

private theorem
    finiteType_eventually_orderedBaseCechComplex_exactAt_succ_of_card_le_add
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (q n : ℕ)
    (hcard : Fintype.card (ULift.{u} σ) ≤ (q + 1) + n) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N →
      (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j N)
        (coordinateOpenCover (R := R) (σ := σ))).ExactAt (q + 1) := by
  induction n generalizing M q with
  | zero =>
      refine ⟨0, fun N _ ↦ ?_⟩
      apply
        AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
      simpa using hcard
  | succ n ih =>
      by_cases hq : Fintype.card (ULift.{u} σ) ≤ q + 1
      · refine ⟨0, fun N _ ↦ ?_⟩
        exact
          AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
            (homogeneousProjπ (R := R) (σ := σ))
            (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j N)
            (coordinateOpenCover (R := R) (σ := σ)) (q + 1) hq
      · obtain ⟨r, d, N₀, f, hf⟩ :=
          exists_fin_coordinateNonnegativeTwist_quotient M j
        let L : Fin r → (Proj (homogeneousSubmodule σ R)).Modules :=
          fun i ↦ coordinateHyperplanePoleSheafPower
            (R := R) j (N₀ - d i)
        let Q : (Proj (homogeneousSubmodule σ R)).Modules := ∐ L
        let Y : (Proj (homogeneousSubmodule σ R)).Modules :=
          M ⊗ coordinateHyperplanePoleSheafPower (R := R) j N₀
        letI : Epi f := hf
        letI : Q.IsQuasicoherent := by
          dsimp only [Q]
          apply AlgebraicGeometry.Scheme.Modules.isQuasicoherent_coproduct
          intro i
          exact
            AlgebraicGeometry.Scheme.Modules.IsInvertible.isQuasicoherent
              (coordinateHyperplanePoleSheafPower_isInvertible
                (R := R) j (N₀ - d i))
        letI : Q.IsFiniteType := by
          dsimp only [Q]
          apply
            AlgebraicGeometry.Scheme.Modules.isFiniteType_fin_coproduct L
          · intro i
            exact
              AlgebraicGeometry.Scheme.Modules.IsInvertible.isQuasicoherent
                (coordinateHyperplanePoleSheafPower_isInvertible
                  (R := R) j (N₀ - d i))
          · intro i
            letI : (L i).IsFinitePresentation :=
              AlgebraicGeometry.Scheme.Modules.IsInvertible.isFinitePresentation
                (coordinateHyperplanePoleSheafPower_isInvertible
                  (R := R) j (N₀ - d i))
            refine { exists_localGeneratorsData := ?_ }
            obtain ⟨p, hp⟩ :=
              SheafOfModules.IsFinitePresentation.exists_quasicoherentData
                (L i)
            refine ⟨p.localGeneratorsData, ?_⟩
            constructor
            intro k
            exact (hp.isFinite_presentation k).isFiniteType_generators
        letI : LocallyOfFiniteType
            (homogeneousProjπ (R := R) (σ := σ)) :=
          homogeneousProjπ_locallyOfFiniteType (R := R) (σ := σ)
        letI : IsLocallyNoetherian
            (Proj (homogeneousSubmodule σ R)) :=
          LocallyOfFiniteType.isLocallyNoetherian
            (homogeneousProjπ (R := R) (σ := σ))
        letI : Y.IsQuasicoherent :=
          moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent
            M j N₀
        letI : Y.IsFiniteType :=
          @SheafOfModules.isFiniteType_of_epi
            _ _ _ _ _ _ _ Q Y f hf inferInstance
        letI : (kernel f).IsQuasicoherent :=
          AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel f
        letI : (kernel f).IsFiniteType :=
          AlgebraicGeometry.Scheme.Modules.isFiniteType_kernel f
        have hcard' :
            Fintype.card (ULift.{u} σ) ≤ ((q + 1) + 1) + n := by
          omega
        obtain ⟨b, hb⟩ := ih (kernel f) (q + 1) hcard'
        refine ⟨N₀ + b, fun N hN ↦ ?_⟩
        let N₁ := N - N₀
        have hN₁ : b ≤ N₁ := by
          dsimp only [N₁]
          omega
        have hsum : N₀ + N₁ = N := by
          dsimp only [N₁]
          omega
        have hK := hb N₁ hN₁
        let E :=
          coordinateHyperplanePoleSheafPowerTensorEquivalence
            (R := R) j N₁
        let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
        have hT : T.ShortExact :=
          { exact := ShortComplex.exact_kernel f }
        have hTE : (T.map E.functor).ShortExact :=
          hT.map_of_exact E.functor
        letI : ((T.map E.functor).X₁).IsQuasicoherent := by
          change
            ((kernel f) ⊗
              coordinateHyperplanePoleSheafPower
                (R := R) j N₁).IsQuasicoherent
          exact
            moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent
              (kernel f) j N₁
        letI : ((T.map E.functor).X₂).IsQuasicoherent := by
          change
            (Q ⊗ coordinateHyperplanePoleSheafPower
              (R := R) j N₁).IsQuasicoherent
          exact
            moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent
              Q j N₁
        letI : ((T.map E.functor).X₃).IsQuasicoherent := by
          change
            (Y ⊗ coordinateHyperplanePoleSheafPower
              (R := R) j N₁).IsQuasicoherent
          exact
            moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent
              Y j N₁
        have hTEC :=
          hTE.map_orderedBaseCechComplexFunctor_of_affine_openCover
            (homogeneousProjπ (R := R) (σ := σ))
            (coordinateOpenCover (R := R) (σ := σ))
            (coordinateOpenCover_isAffineOpen (R := R))
        let F :=
          AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplexFunctor
            (homogeneousProjπ (R := R) (σ := σ))
            (coordinateOpenCover (R := R) (σ := σ))
        have hQ :
            (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
              (homogeneousProjπ (R := R) (σ := σ))
              (Q ⊗ coordinateHyperplanePoleSheafPower
                (R := R) j N₁)
              (coordinateOpenCover (R := R) (σ := σ))).ExactAt
                (q + 1) := by
          dsimp only [Q, L]
          exact
            coordinateHyperplanePoleSheafPowerCoproductTensor_orderedBaseCechComplex_exactAt_succ
              (R := R) j (fun i ↦ N₀ - d i) N₁ q
        have hY :
            (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
              (homogeneousProjπ (R := R) (σ := σ))
              (Y ⊗ coordinateHyperplanePoleSheafPower
                (R := R) j N₁)
              (coordinateOpenCover (R := R) (σ := σ))).ExactAt
                (q + 1) := by
          change ((T.map E.functor).map F).X₃.ExactAt (q + 1)
          apply shortExact_exactAt_X3_of_exactAt_X2_X1
            hTEC (q + 1) ((q + 1) + 1)
          · simp [ComplexShape.up_Rel]
          · change
              (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
                (homogeneousProjπ (R := R) (σ := σ))
                (Q ⊗ coordinateHyperplanePoleSheafPower
                  (R := R) j N₁)
                (coordinateOpenCover (R := R) (σ := σ))).ExactAt
                  (q + 1)
            exact hQ
          · change
              (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
                (homogeneousProjπ (R := R) (σ := σ))
                ((kernel f) ⊗
                  coordinateHyperplanePoleSheafPower
                    (R := R) j N₁)
                (coordinateOpenCover (R := R) (σ := σ))).ExactAt
                  ((q + 1) + 1)
            exact hK
        let e :
            Y ⊗ coordinateHyperplanePoleSheafPower (R := R) j N₁ ≅
              M ⊗ coordinateHyperplanePoleSheafPower (R := R) j N :=
          moduleTensorCoordinateHyperplanePoleSheafPowerAddIso
              (R := R) M j N₀ N₁ ≪≫
            eqToIso (congrArg
              (fun k ↦ M ⊗
                coordinateHyperplanePoleSheafPower (R := R) j k)
              hsum)
        exact orderedBaseCechComplex_exactAt_of_iso e.symm (q + 1) hY

/-- A finite-type quasicoherent module on polynomial projective space has
exact ordered-Cech complex in each fixed positive degree after every
sufficiently large positive coordinate twist. -/
theorem finiteType_eventually_orderedBaseCechComplex_exactAt_succ
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    (M : (Proj (homogeneousSubmodule σ R)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (q : ℕ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N →
      (AlgebraicGeometry.Scheme.Modules.orderedBaseCechComplex
        (homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ coordinateHyperplanePoleSheafPower (R := R) j N)
        (coordinateOpenCover (R := R) (σ := σ))).ExactAt (q + 1) := by
  exact
    finiteType_eventually_orderedBaseCechComplex_exactAt_succ_of_card_le_add
      M j q (Fintype.card (ULift.{u} σ)) (by omega)

end

end MvPolynomial
