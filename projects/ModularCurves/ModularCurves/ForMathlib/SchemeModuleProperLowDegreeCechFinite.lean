/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.SchemeModuleCanonicalSupportChowLowDegreeAssembly

/-!
# Low-degree Cech finiteness for proper schemes

Canonical-support Chow comodels and closed-support induction imply
finiteness of ordered base-Cech homology in degrees zero and one for
coherent modules on a Noetherian proper scheme.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

private def CoherentPredicate
    {X : Scheme.{u}} (M : X.Modules) : Prop :=
  M.IsFiniteType ∧ M.IsQuasicoherent

private def LowDegreeGood
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M : X.Modules) : Prop :=
  M.IsFiniteType ∧ M.IsQuasicoherent ∧
    OrderedBaseCechLowDegreeFinite π U M

private theorem exists_zero_lowDegreeComodel
    {X S : Scheme.{u}} [IsLocallyNoetherian X] (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M : X.Modules) (hM : CoherentPredicate M)
    (hzero : IsZero M) :
    ∃ (E : X.Modules) (f : M ⟶ E),
      LowDegreeGood π U E ∧
      CoherentPredicate
        (kernel (Abelian.factorThruImage f)) ∧
      CoherentPredicate
        (cokernel (Abelian.image.ι f)) ∧
      (IsZero (kernel (Abelian.factorThruImage f)) ∨
        closedStalkSupport
            (kernel (Abelian.factorThruImage f)) <
          closedStalkSupport M) ∧
      (IsZero (cokernel (Abelian.image.ι f)) ∨
        closedStalkSupport
            (cokernel (Abelian.image.ι f)) <
          closedStalkSupport M) := by
  letI : M.IsFiniteType := hM.1
  letI : M.IsQuasicoherent := hM.2
  have hresidual :=
    comparisonResidual_isFiniteType_and_isQuasicoherent (𝟙 M)
  refine ⟨M, 𝟙 M, ⟨hM.1, hM.2,
    OrderedBaseCechLowDegreeFinite.of_isZero π U hzero⟩,
    ⟨hresidual.1.1, hresidual.1.2⟩,
    ⟨hresidual.2.1, hresidual.2.2⟩, ?_, ?_⟩
  · exact Or.inl (IsZero.of_mono
      (kernel.ι (Abelian.factorThruImage (𝟙 M))) hzero)
  · exact Or.inl (IsZero.of_epi
      (cokernel.π (Abelian.image.ι (𝟙 M))) hzero)

private theorem exists_nonzero_lowDegreeComodel
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) (hM : CoherentPredicate M)
    (hnonzero : ¬ IsZero M) :
    ∃ (E : X.Modules) (f : M ⟶ E),
      LowDegreeGood xπ U E ∧
      CoherentPredicate
        (kernel (Abelian.factorThruImage f)) ∧
      CoherentPredicate
        (cokernel (Abelian.image.ι f)) ∧
      (IsZero (kernel (Abelian.factorThruImage f)) ∨
        closedStalkSupport
            (kernel (Abelian.factorThruImage f)) <
          closedStalkSupport M) ∧
      (IsZero (cokernel (Abelian.image.ι f)) ∨
        closedStalkSupport
            (cokernel (Abelian.image.ι f)) <
          closedStalkSupport M) := by
  letI : M.IsFiniteType := hM.1
  letI : M.IsQuasicoherent := hM.2
  let A := CanonicalSupportThickening.ofFiniteType M
  obtain ⟨E, f, h⟩ :=
    CanonicalSupportThickening.exists_chowComodel_orderedBaseCechLowDegreeFinite
      (xπ := xπ) (F := M) A U hU hUaff hnonzero
  change E.IsFiniteType ∧ E.IsQuasicoherent ∧
    OrderedBaseCechLowDegreeFinite xπ U E ∧
    (kernel (Abelian.factorThruImage f)).IsFiniteType ∧
    (kernel (Abelian.factorThruImage f)).IsQuasicoherent ∧
    (cokernel (Abelian.image.ι f)).IsFiniteType ∧
    (cokernel (Abelian.image.ι f)).IsQuasicoherent ∧
    (IsZero (kernel (Abelian.factorThruImage f)) ∨
      closedStalkSupport
          (kernel (Abelian.factorThruImage f)) <
        closedStalkSupport M) ∧
    (IsZero (cokernel (Abelian.image.ι f)) ∨
      closedStalkSupport
          (cokernel (Abelian.image.ι f)) <
        closedStalkSupport M) at h
  obtain ⟨hEfinite, hEqc, hEcech, hKfinite, hKqc,
      hQfinite, hQqc, hKdrop, hQdrop⟩ := h
  exact
    ⟨E, f, ⟨hEfinite, hEqc, hEcech⟩,
      ⟨hKfinite, hKqc⟩, ⟨hQfinite, hQqc⟩,
      hKdrop, hQdrop⟩

private theorem exists_lowDegreeComodel
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) (hM : CoherentPredicate M) :
    ∃ (E : X.Modules) (f : M ⟶ E),
      LowDegreeGood xπ U E ∧
      CoherentPredicate
        (kernel (Abelian.factorThruImage f)) ∧
      CoherentPredicate
        (cokernel (Abelian.image.ι f)) ∧
      (IsZero (kernel (Abelian.factorThruImage f)) ∨
        closedStalkSupport
            (kernel (Abelian.factorThruImage f)) <
          closedStalkSupport M) ∧
      (IsZero (cokernel (Abelian.image.ι f)) ∨
        closedStalkSupport
            (cokernel (Abelian.image.ι f)) <
          closedStalkSupport M) := by
  by_cases hzero : IsZero M
  · exact exists_zero_lowDegreeComodel xπ U M hM hzero
  · exact exists_nonzero_lowDegreeComodel
      U hU hUaff M hM hzero

/-- A coherent module on a Noetherian proper scheme has finite ordered
base-Cech homology in degrees zero and one for every finite affine open
cover. -/
theorem orderedBaseCechLowDegreeFinite_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechLowDegreeFinite xπ U M := by
  letI : IsNoetherianRing Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)) :=
    isNoetherianRing_of_ringEquiv (CommRingCat.of R)
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  refine
    OrderedBaseCechLowDegreeFinite.of_closedStalkSupport_comodels
      xπ U hUaff CoherentPredicate (LowDegreeGood xπ U)
      ?_ ?_ ?_ ?_ M ?_
  · intro N hN
    exact hN.2
  · intro E hE
    exact hE.2.1
  · intro N hN
    exact exists_lowDegreeComodel U hU hUaff N hN
  · intro E hE
    exact hE.2.2
  · exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
