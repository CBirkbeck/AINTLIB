import ModularCurves.EllipticCurve.RelativeProjectiveTwistCechVanishing
import ModularCurves.ForMathlib.RelativeProjectivePushforwardFiniteType
import ModularCurves.ForMathlib.SchemeModuleOrderedAffineCechCohomology
import ModularCurves.Picard.InvertibleSheafTensorQuasicoherent

/-!
# Cech vanishing for arbitrary relative projective coordinate twists

The existing relative-projective wrapper treats the structure module and coordinate zero. This
file gives the corresponding affine restriction comparison and eventual Cech exactness for an
arbitrary finite-type quasicoherent source module and any projective coordinate.
-/

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.IsRelativeProjectiveFactorization

open MvPolynomial MonoidalCategory

variable {k : Type u} [CommRing k] {X S : Scheme.{u}}
variable {s : S ⟶ Spec (.of k)} {f : X ⟶ S}

noncomputable local instance coordinateTwistCechMonoidalCategory
    (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- Over an affine base open, restriction of a coordinate-twisted module is the corresponding
absolute coordinate twist of the restricted module. -/
noncomputable def coordinateTwistRestrictOfNatAffineIso
    (h : IsRelativeProjectiveFactorization s f)
    (M : X.Modules)
    (j : Fin (h.chosenDimension + 1))
    (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (M ⊗
        (Scheme.Modules.pullback h.chosenProjectiveMap).obj
          (coordinateHyperplanePoleSheafPower (R := k) j n)).restrict
      (f ⁻¹ᵁ U).ι ≅
    M.restrict (f ⁻¹ᵁ U).ι ⊗
      (Scheme.Modules.pullback
        (h.chosenAffineProjectiveEmbedding U hU)).obj
          (coordinateHyperplanePoleSheafPower
            (R := Γ(S, U)) j n) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  let i := (f ⁻¹ᵁ U).ι
  let g := h.chosenAffineProjectiveEmbedding U hU
  let c := coefficientMap
    (algebraMap k Γ(S, U)) h.chosenDimension
  let P :=
    coordinateHyperplanePoleSheafPower (R := k) j n
  let Q :=
    coordinateHyperplanePoleSheafPower
      (R := Γ(S, U)) j n
  let L := (Scheme.Modules.pullback h.chosenProjectiveMap).obj P
  letI : (Scheme.Modules.pullback i).Monoidal :=
    Scheme.Modules.pullbackMonoidal i
  let eM :
      (Scheme.Modules.pullback i).obj M ≅ M.restrict i :=
    (Scheme.Modules.restrictFunctorIsoPullback i).symm.app M
  let eP :
      (Scheme.Modules.pullback i).obj L ≅
        (Scheme.Modules.pullback g).obj Q :=
    (Scheme.Modules.pullbackComp i h.chosenProjectiveMap).app P ≪≫
      ((Scheme.Modules.pullbackCongr
        (h.chosenAffineProjectiveEmbedding_coefficientMap U hU)).app P).symm ≪≫
      (Scheme.Modules.pullbackComp g c).symm.app P ≪≫
      (Scheme.Modules.pullback g).mapIso
        (coordinateHyperplanePoleSheafPowerBaseChangeIso
          (algebraMap k Γ(S, U)) h.chosenDimension j n)
  exact
    (Scheme.Modules.restrictFunctorIsoPullback i).app (M ⊗ L) ≪≫
      (Functor.Monoidal.μIso
        (Scheme.Modules.pullback i) M L).symm ≪≫
      (eM ⊗ᵢ eP)

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

/-- Over an affine open in a Noetherian stage, every fixed positive Cech degree of an arbitrary
coordinate twist of a finite-type quasicoherent module is eventually exact. -/
theorem coordinateTwist_eventually_orderedBaseCechComplex_exactAt_succ
    [IsNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (h.chosenDimension + 1))
    (U : S.Opens) (hU : IsAffineOpen U) (q : ℕ) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      (Scheme.Modules.orderedBaseCechComplex
        (morphismRestrict f U ≫ hU.isoSpec.hom)
        ((M ⊗
          (Scheme.Modules.pullback h.chosenProjectiveMap).obj
            (coordinateHyperplanePoleSheafPower
              (R := k) j n)).restrict (f ⁻¹ᵁ U).ι)
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
  let N := M.restrict (f ⁻¹ᵁ U).ι
  letI : N.IsQuasicoherent := inferInstance
  letI : N.IsFiniteType :=
    Scheme.Modules.isFiniteType_restrict_of_isOpenImmersion
      (f ⁻¹ᵁ U).ι M
  obtain ⟨b, hb⟩ :=
    closedImmersion_finiteType_eventually_orderedBaseCechComplex_exactAt_succ
      g N j q
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
  let eTwist :=
    h.coordinateTwistRestrictOfNatAffineIso M j U hU n
  let C : ULift.{u} (Fin (h.chosenDimension + 1)) →
      ((f ⁻¹ᵁ U).toScheme).Opens :=
    fun i => g ⁻¹ᵁ coordinateOpenCover
      (R := Γ(S, U))
      (σ := Fin (h.chosenDimension + 1)) i
  let F := Scheme.Modules.orderedBaseCechComplexFunctor
    (morphismRestrict f U ≫ hU.isoSpec.hom) C
  exact hExact.of_iso (F.mapIso eTwist.symm)

/-- Over an affine open in a Noetherian stage, sufficiently positive coordinate twists of an
arbitrary finite-type quasicoherent module are exact in every positive Cech degree. -/
theorem coordinateTwist_eventually_orderedBaseCechComplex_exactAt_of_pos
    [IsNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (h.chosenDimension + 1))
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      (Scheme.Modules.orderedBaseCechComplex
        (morphismRestrict f U ≫ hU.isoSpec.hom)
        ((M ⊗
          (Scheme.Modules.pullback h.chosenProjectiveMap).obj
            (coordinateHyperplanePoleSheafPower
              (R := k) j n)).restrict (f ⁻¹ᵁ U).ι)
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
      ((M ⊗
        (Scheme.Modules.pullback h.chosenProjectiveMap).obj
          (coordinateHyperplanePoleSheafPower
            (R := k) j n)).restrict (f ⁻¹ᵁ U).ι)
      (fun i : ULift.{u} (Fin (h.chosenDimension + 1)) =>
        h.chosenAffineProjectiveEmbedding U hU ⁻¹ᵁ
          coordinateOpenCover
            (R := Γ(S, U))
            (σ := Fin (h.chosenDimension + 1)) i)).ExactAt
      (q.1 + 1)
  obtain ⟨b, hb⟩ := exists_uniform_eventual_bound P fun q =>
    h.coordinateTwist_eventually_orderedBaseCechComplex_exactAt_succ
      M j U hU q.1
  refine ⟨b, fun n hn q hq => ?_⟩
  by_cases hdq : d ≤ q
  · exact Scheme.Modules.orderedBaseCechComplex_exactAt_of_card_le
      (morphismRestrict f U ≫ hU.isoSpec.hom)
      ((M ⊗
        (Scheme.Modules.pullback h.chosenProjectiveMap).obj
          (coordinateHyperplanePoleSheafPower
            (R := k) j n)).restrict (f ⁻¹ᵁ U).ι)
      (fun i : ULift.{u} (Fin (h.chosenDimension + 1)) =>
        h.chosenAffineProjectiveEmbedding U hU ⁻¹ᵁ
          coordinateOpenCover
            (R := Γ(S, U))
            (σ := Fin (h.chosenDimension + 1)) i)
      q hdq
  · have hqd : q - 1 < d := by omega
    have hP := hb n hn ⟨q - 1, hqd⟩
    simpa [P, Nat.sub_add_cancel hq] using hP

/-- Over an affine open in a Noetherian stage, every positive intrinsic
cohomology group of a sufficiently positive coordinate twist vanishes. -/
theorem coordinateTwist_eventually_subsingleton_H_of_pos
    [IsNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : Fin (h.chosenDimension + 1))
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∀ q : ℕ, 0 < q →
      Subsingleton (CategoryTheory.Sheaf.H
        ((M ⊗
          (Scheme.Modules.pullback h.chosenProjectiveMap).obj
            (coordinateHyperplanePoleSheafPower
              (R := k) j n)).restrict (f ⁻¹ᵁ U).ι).sheaf q) := by
  obtain ⟨b, hb⟩ :=
    h.coordinateTwist_eventually_orderedBaseCechComplex_exactAt_of_pos
      M j U hU
  refine ⟨b, fun n hn q hq => ?_⟩
  let g := h.chosenAffineProjectiveEmbedding U hU
  letI : IsClosedImmersion g :=
    h.chosenAffineProjectiveEmbedding_isClosedImmersion U hU
  let P :=
    coordinateHyperplanePoleSheafPower (R := k) j n
  let L :=
    (Scheme.Modules.pullback h.chosenProjectiveMap).obj P
  have hP : Scheme.Modules.IsInvertible P :=
    coordinateHyperplanePoleSheafPower_isInvertible j n
  have hL : Scheme.Modules.IsInvertible L :=
    hP.pullback h.chosenProjectiveMap
  let T : X.Modules := M ⊗ L
  letI : T.IsQuasicoherent :=
    hL.tensorObj_isQuasicoherent
  let N := T.restrict (f ⁻¹ᵁ U).ι
  let C : ULift.{u} (Fin (h.chosenDimension + 1)) →
      ((f ⁻¹ᵁ U).toScheme).Opens :=
    fun i => g ⁻¹ᵁ coordinateOpenCover
      (R := Γ(S, U))
      (σ := Fin (h.chosenDimension + 1)) i
  letI : N.IsQuasicoherent := inferInstance
  letI : ((f ⁻¹ᵁ U).toScheme).IsSeparated := ⟨by
    rw [← terminal.comp_from
      (g ≫ homogeneousProjπ
        (R := Γ(S, U))
        (σ := Fin (h.chosenDimension + 1)))]
    infer_instance⟩
  have hC : IsOpenCover C :=
    g.iSup_preimage_eq_top
      (iSup_coordinateOpenCover_eq_top
        (R := Γ(S, U))
        (σ := Fin (h.chosenDimension + 1)))
  have hCaff : ∀ i, IsAffineOpen (C i) :=
    fun i => (coordinateOpenCover_isAffineOpen (R := Γ(S, U)) i).preimage g
  have hExact := hb n hn q hq
  have hVanish :=
    (Scheme.Modules.orderedBaseCechComplex_exactAt_succ_iff_subsingleton_H_of_affine_openCover
        (morphismRestrict f U ≫ hU.isoSpec.hom)
        N C hC hCaff (q - 1)).1
      (by simpa only [Nat.sub_add_cancel hq] using hExact)
  simpa only [Nat.sub_add_cancel hq] using hVanish

end AlgebraicGeometry.IsRelativeProjectiveFactorization
