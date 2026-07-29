/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
Adapted in part from the Apache-licensed `FiniteEventualUniformBound.lean`
in Vilin97/Clawristotle.
-/
import Mathlib.Data.Finset.Lattice.Fold
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

private theorem exists_uniform_eventual_bound
    {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop)
    (hP : ∀ i, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → P i n) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ i, P i n := by
  classical
  choose bound hbound using hP
  let b := Finset.univ.sup bound
  refine ⟨b, fun n hn i ↦ hbound i n ?_⟩
  exact (Finset.le_sup (f := bound) (Finset.mem_univ i)).trans hn

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

/-- A finite-type quasicoherent module on a closed subscheme of polynomial
projective space has exact inverse-image-cover ordered-Cech complex in every
positive degree after one sufficiently large pulled-back positive coordinate
twist. -/
theorem
    closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_of_pos
    [Fintype σ] [LinearOrder σ] [IsNoetherianRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) :
    ∃ b : ℕ, ∀ N : ℕ, b ≤ N → ∀ q : ℕ, 0 < q →
      (Scheme.Modules.orderedBaseCechComplex
        (f ≫ homogeneousProjπ (R := R) (σ := σ))
        (M ⊗ (Scheme.Modules.pullback f).obj
          (coordinateHyperplanePoleSheafPower (R := R) j N))
        (fun i => f ⁻¹ᵁ coordinateOpenCover
          (R := R) (σ := σ) i)).ExactAt q := by
  let d := Fintype.card (ULift.{u} σ)
  let P : Fin d → ℕ → Prop := fun q N ↦
    (Scheme.Modules.orderedBaseCechComplex
      (f ≫ homogeneousProjπ (R := R) (σ := σ))
      (M ⊗ (Scheme.Modules.pullback f).obj
        (coordinateHyperplanePoleSheafPower (R := R) j N))
      (fun i => f ⁻¹ᵁ coordinateOpenCover
        (R := R) (σ := σ) i)).ExactAt (q.1 + 1)
  obtain ⟨b, hb⟩ := exists_uniform_eventual_bound P fun q ↦
    closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_succ
      f M j q.1
  refine ⟨b, fun N hN q hq ↦ ?_⟩
  by_cases hdq : d ≤ q
  · exact Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
      (f ≫ homogeneousProjπ (R := R) (σ := σ))
      (M ⊗ (Scheme.Modules.pullback f).obj
        (coordinateHyperplanePoleSheafPower (R := R) j N))
      (fun i => f ⁻¹ᵁ coordinateOpenCover
        (R := R) (σ := σ) i) q hdq
  · have hqd : q - 1 < d := by omega
    have hP := hb N hN ⟨q - 1, hqd⟩
    simpa [P, Nat.sub_add_cancel hq] using hP

end

end MvPolynomial
