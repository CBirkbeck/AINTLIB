/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectiveSpaceClosedPositiveTwistCechVanishing
import ModularCurves.EllipticCurve.RelativeProjectiveTwistAffineComparison

/-!
# Cech vanishing for relative projective twists

On a Noetherian stage, sufficiently positive chosen relative projective
twists have exact ordered Cech complexes over every affine base open.
-/

open CategoryTheory Limits

noncomputable section

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

open MvPolynomial MonoidalCategory

variable {k : Type u} [CommRing k] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of k)} {f : X ⟶ S}

noncomputable local instance relativeProjectiveTwistCechMonoidalCategory
    (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

private theorem unitObj_isFiniteType (Y : Scheme.{u}) :
    (Scheme.Modules.unitObj Y).IsFiniteType := by
  let h : (Scheme.Modules.unitObj Y).IsFinitePresentation :=
    Scheme.Modules.isInvertible_unit.isFinitePresentation
  let q := h.exists_quasicoherentData.choose
  letI : q.IsFinitePresentation :=
    h.exists_quasicoherentData.choose_spec
  exact
    { exists_localGeneratorsData :=
        ⟨q.localGeneratorsData,
          { isFiniteType := fun i => by
              change (q.presentation i).generators.IsFiniteType
              exact
                (SheafOfModules.QuasicoherentData.IsFinitePresentation.isFinite_presentation
                  i).isFiniteType_generators }⟩ }

private theorem exists_uniform_eventual_bound
    {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop)
    (hP : ∀ i, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → P i n) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ i, P i n := by
  classical
  choose bound hbound using hP
  let b := Finset.univ.sup bound
  refine ⟨b, fun n hn i => hbound i n ?_⟩
  exact (Finset.le_sup (f := bound) (Finset.mem_univ i)).trans hn

/-- Over an affine open in a Noetherian stage, every fixed positive Cech
degree of the chosen relative twist is eventually exact. -/
theorem chosenTwist_eventually_orderedBaseCechComplex_exactAt_succ
    [AlgebraicGeometry.IsNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) (q : ℕ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (Scheme.Modules.orderedBaseCechComplex
        (morphismRestrict f U ≫ hU.isoSpec.hom)
        ((h.chosenTwist (.ofNat n)).restrict (f ⁻¹ᵁ U).ι)
        (fun i : ULift.{u} (Fin (h.chosenDimension + 1)) =>
          h.chosenAffineProjectiveEmbedding U hU ⁻¹ᵁ
            coordinateOpenCover
              (R := Γ(S, U))
              (σ := Fin (h.chosenDimension + 1)) i)).ExactAt
        (q + 1) := by
  letI : IsNoetherianRing Γ(S, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  let g := h.chosenAffineProjectiveEmbedding U hU
  letI : IsClosedImmersion g :=
    h.chosenAffineProjectiveEmbedding_isClosedImmersion U hU
  let P : ℕ →
      (Proj (homogeneousSubmodule
        (Fin (h.chosenDimension + 1)) Γ(S, U))).Modules :=
    fun n => coordinateHyperplanePoleSheafPower
      (R := Γ(S, U)) (0 : Fin (h.chosenDimension + 1)) n
  let C : ULift.{u} (Fin (h.chosenDimension + 1)) →
      ((f ⁻¹ᵁ U).toScheme).Opens :=
    fun i => g ⁻¹ᵁ coordinateOpenCover
      (R := Γ(S, U))
      (σ := Fin (h.chosenDimension + 1)) i
  letI :
      (Scheme.Modules.unitObj
        (f ⁻¹ᵁ U).toScheme).IsQuasicoherent :=
    Scheme.Modules.isInvertible_unit.isQuasicoherent
  letI :
      (Scheme.Modules.unitObj
        (f ⁻¹ᵁ U).toScheme).IsFiniteType := by
    exact unitObj_isFiniteType (f ⁻¹ᵁ U).toScheme
  obtain ⟨b, hb⟩ :=
    closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_succ
      g (Scheme.Modules.unitObj (f ⁻¹ᵁ U).toScheme)
        (0 : Fin (h.chosenDimension + 1)) q
  refine ⟨b, fun n hn => ?_⟩
  have hExact := hb n hn
  have hStructural :
      g ≫ homogeneousProjπ
          (R := Γ(S, U))
          (σ := Fin (h.chosenDimension + 1)) =
        morphismRestrict f U ≫ hU.isoSpec.hom := by
    simpa only [g] using
      h.chosenAffineProjectiveEmbedding_homogeneousProjπ U hU
  rw [hStructural] at hExact
  let eTwist := h.chosenTwistRestrictOfNatAffineIso U hU n
  let e :
      Scheme.Modules.unitObj (f ⁻¹ᵁ U).toScheme ⊗
          (Scheme.Modules.pullback g).obj (P n) ≅
        (h.chosenTwist (.ofNat n)).restrict (f ⁻¹ᵁ U).ι :=
    ((ModularCurves.monoidalUnitObjIso
        (f ⁻¹ᵁ U).toScheme).symm ⊗ᵢ
      Iso.refl ((Scheme.Modules.pullback g).obj (P n))) ≪≫
      λ_ ((Scheme.Modules.pullback g).obj (P n)) ≪≫
      eTwist.symm
  let F := Scheme.Modules.orderedBaseCechComplexFunctor
    (morphismRestrict f U ≫ hU.isoSpec.hom) C
  have hTransport := hExact.of_iso (F.mapIso e)
  exact hTransport

/-- Over an affine open in a Noetherian stage, sufficiently positive chosen
relative twists have exact ordered Cech complexes in every positive degree. -/
theorem chosenTwist_eventually_orderedBaseCechComplex_exactAt_of_pos
    [AlgebraicGeometry.IsNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      (Scheme.Modules.orderedBaseCechComplex
        (morphismRestrict f U ≫ hU.isoSpec.hom)
        ((h.chosenTwist (.ofNat n)).restrict (f ⁻¹ᵁ U).ι)
        (fun i : ULift.{u} (Fin (h.chosenDimension + 1)) =>
          h.chosenAffineProjectiveEmbedding U hU ⁻¹ᵁ
            coordinateOpenCover
              (R := Γ(S, U))
              (σ := Fin (h.chosenDimension + 1)) i)).ExactAt q := by
  let d := Fintype.card
    (ULift.{u} (Fin (h.chosenDimension + 1)))
  let P : Fin d → ℕ → Prop := fun q n =>
    (Scheme.Modules.orderedBaseCechComplex
      (morphismRestrict f U ≫ hU.isoSpec.hom)
      ((h.chosenTwist (.ofNat n)).restrict (f ⁻¹ᵁ U).ι)
      (fun i : ULift.{u} (Fin (h.chosenDimension + 1)) =>
        h.chosenAffineProjectiveEmbedding U hU ⁻¹ᵁ
          coordinateOpenCover
            (R := Γ(S, U))
            (σ := Fin (h.chosenDimension + 1)) i)).ExactAt
      (q.1 + 1)
  obtain ⟨b, hb⟩ := exists_uniform_eventual_bound P fun q =>
    h.chosenTwist_eventually_orderedBaseCechComplex_exactAt_succ
      U hU q.1
  refine ⟨b, fun n hn q hq => ?_⟩
  by_cases hdq : d ≤ q
  · exact Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
      (morphismRestrict f U ≫ hU.isoSpec.hom)
      ((h.chosenTwist (.ofNat n)).restrict (f ⁻¹ᵁ U).ι)
      (fun i : ULift.{u} (Fin (h.chosenDimension + 1)) =>
        h.chosenAffineProjectiveEmbedding U hU ⁻¹ᵁ
          coordinateOpenCover
            (R := Γ(S, U))
            (σ := Fin (h.chosenDimension + 1)) i)
      q hdq
  · have hqd : q - 1 < d := by omega
    have hP := hb n hn ⟨q - 1, hqd⟩
    simpa [P, Nat.sub_add_cancel hq] using hP

end AlgebraicGeometry.IsRelativeProjectiveFactorization
