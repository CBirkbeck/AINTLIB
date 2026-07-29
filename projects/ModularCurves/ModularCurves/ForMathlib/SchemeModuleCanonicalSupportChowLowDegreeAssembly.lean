/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `CanonicalSupportChowComodel.lean` in
Vilin97/Clawristotle.
-/
import ModularCurves.ForMathlib.SchemeInducingOpenLift
import ModularCurves.ForMathlib.SchemeModuleCanonicalSupportChowLowDegreeFinite
import ModularCurves.ForMathlib.SchemeModuleComparisonCoherent
import ModularCurves.ForMathlib.SchemeModuleComparisonSupport
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforwardFinite
import ModularCurves.ForMathlib.SchemeModulePushforwardMapRestrictionIso
import ModularCurves.ForMathlib.SchemeModulePushforwardPullbackSupport
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent

/-!
# Cech-finite Chow comodels on canonical support thickenings

A positive coordinate comodel on a support-adapted Chow chart is pushed
through the canonical closed support immersion. The resulting coherent
module has finite ordered Cech homology in every degree, while both residuals
of its comparison with the original module have strictly smaller closed stalk
support.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace CanonicalSupportThickening

/-- A coherent comparison target with finite ordered Cech homology in every
degree and support-decreasing residuals. -/
def IsChowComodel
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (F E : X.Modules) (β : F ⟶ E) : Prop :=
  E.IsFiniteType ∧ E.IsQuasicoherent ∧
    OrderedBaseCechHomologyFinite π U E ∧
    (kernel (Abelian.factorThruImage β)).IsFiniteType ∧
    (kernel (Abelian.factorThruImage β)).IsQuasicoherent ∧
    (cokernel (Abelian.image.ι β)).IsFiniteType ∧
    (cokernel (Abelian.image.ι β)).IsQuasicoherent ∧
    (IsZero (kernel (Abelian.factorThruImage β)) ∨
      closedStalkSupport
          (kernel (Abelian.factorThruImage β)) <
        closedStalkSupport F) ∧
    (IsZero (cokernel (Abelian.image.ι β)) ∨
      closedStalkSupport
          (cokernel (Abelian.image.ι β)) <
        closedStalkSupport F)

/-- A coherent comparison target with finite ordered Cech homology in
degrees zero and one and support-decreasing residuals. -/
def IsLowDegreeChowComodel
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (F E : X.Modules) (β : F ⟶ E) : Prop :=
  E.IsFiniteType ∧ E.IsQuasicoherent ∧
    OrderedBaseCechLowDegreeFinite π U E ∧
    (kernel (Abelian.factorThruImage β)).IsFiniteType ∧
    (kernel (Abelian.factorThruImage β)).IsQuasicoherent ∧
    (cokernel (Abelian.image.ι β)).IsFiniteType ∧
    (cokernel (Abelian.image.ι β)).IsQuasicoherent ∧
    (IsZero (kernel (Abelian.factorThruImage β)) ∨
      closedStalkSupport
          (kernel (Abelian.factorThruImage β)) <
        closedStalkSupport F) ∧
    (IsZero (cokernel (Abelian.image.ι β)) ∨
      closedStalkSupport
          (cokernel (Abelian.image.ι β)) <
        closedStalkSupport F)

private def ResidualSupportsLt
    {X : Scheme.{u}} (F : X.Modules)
    {E : X.Modules} (β : F ⟶ E) : Prop :=
  closedStalkSupport
        (kernel (Abelian.factorThruImage β)) <
      closedStalkSupport F ∧
    closedStalkSupport
        (cokernel (Abelian.image.ι β)) <
      closedStalkSupport F

private theorem closedStalkSupport_pushforward_canonicalSupport_le
    {X : Scheme.{u}} {F : X.Modules}
    [F.IsFiniteType] [F.IsQuasicoherent]
    (A : CanonicalSupportThickening F)
    (E₀ : A.supportScheme.Modules) :
    closedStalkSupport ((pushforward A.inclusion).obj E₀) ≤
      closedStalkSupport F := by
  have hpreimage :
      A.inclusion ⁻¹ᵁ closedStalkSupportComplement F = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxSupport :
          A.inclusion x ∈ (closedStalkSupport F : Set X) := by
        rw [← A.range_inclusion]
        exact ⟨x, rfl⟩
      exact (hx hxSupport).elim
    · exact bot_le
  have hzero :
      IsZero
        (E₀.restrict
          (A.inclusion ⁻¹ᵁ
            closedStalkSupportComplement F).ι) := by
    rw [hpreimage]
    apply isZero_of_forall_underlyingStalk_isZero
    intro x
    exact False.elim (by simpa using x.property)
  exact closedStalkSupport_pushforward_le_of_isZero_restrict
    A.inclusion F E₀ hzero

private theorem pushedComparison_residualSupports_lt
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]
    (A : CanonicalSupportThickening F)
    {E₀ : A.supportScheme.Modules}
    [E₀.IsFiniteType] [E₀.IsQuasicoherent]
    (β₀ : A.modelModule ⟶ E₀)
    (V : A.supportScheme.Opens)
    [IsIso ((restrictFunctor V.ι).map β₀)]
    (x : V) :
    let E := (pushforward A.inclusion).obj E₀
    let β : F ⟶ E :=
      A.comparisonIso.hom ≫
        (pushforward A.inclusion).map β₀
    ResidualSupportsLt F β := by
  let E := (pushforward A.inclusion).obj E₀
  let β : F ⟶ E :=
    A.comparisonIso.hom ≫
      (pushforward A.inclusion).map β₀
  letI : E.IsFiniteType :=
    isFiniteType_pushforward_of_isClosedImmersion A.inclusion
  letI : E.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom A.inclusion
  have hresidual :=
    comparisonResidual_isFiniteType_and_isQuasicoherent β
  letI :
      (kernel (Abelian.factorThruImage β)).IsFiniteType :=
    hresidual.1.1
  letI :
      (kernel (Abelian.factorThruImage β)).IsQuasicoherent :=
    hresidual.1.2
  letI :
      (cokernel (Abelian.image.ι β)).IsFiniteType :=
    hresidual.2.1
  letI :
      (cokernel (Abelian.image.ι β)).IsQuasicoherent :=
    hresidual.2.2
  let O := A.inclusion.closedImmersionTargetOpen V
  haveI hβ₀preimage :
      IsIso
        ((restrictFunctor (A.inclusion ⁻¹ᵁ O).ι).map β₀) := by
    rw [show A.inclusion ⁻¹ᵁ O = V by
      exact A.inclusion.preimage_closedImmersionTargetOpen V]
    infer_instance
  haveI hpushforwardβ₀ :
      IsIso
        ((restrictFunctor O.ι).map
          ((pushforward A.inclusion).map β₀)) :=
    isIso_restrict_pushforward_map_of_restrict
      A.inclusion O β₀
  haveI hβopen :
      IsIso ((restrictFunctor O.ι).map β) := by
    dsimp only [β]
    rw [Functor.map_comp]
    infer_instance
  let y : O :=
    ⟨A.inclusion (V.ι x),
      A.inclusion.mem_targetOpenOfIsInducing
        A.inclusion.isClosedEmbedding.isInducing
        V (V.ι x) x.property⟩
  have hy :
      O.ι y ∈ closedStalkSupport F := by
    change A.inclusion (V.ι x) ∈ (closedStalkSupport F : Set X)
    rw [← A.range_inclusion]
    exact ⟨V.ι x, rfl⟩
  exact comparisonResidual_closedStalkSupport_lt
    O.ι β
    (closedStalkSupport_pushforward_canonicalSupport_le A E₀)
    y hy

private structure SupportChowData
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} (xπ : X ⟶ Spec (.of R))
    {F : X.Modules} (A : CanonicalSupportThickening F)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) where
  E₀ : A.supportScheme.Modules
  comparison : A.modelModule ⟶ E₀
  finiteType : E₀.IsFiniteType
  quasicoherent : E₀.IsQuasicoherent
  homologyFinite :
    OrderedBaseCechHomologyFinite
      (A.inclusion ≫ xπ) (fun i => A.inclusion ⁻¹ᵁ U i) E₀
  comparisonOpen : A.supportScheme.Opens
  comparisonIsIso :
    IsIso ((restrictFunctor comparisonOpen.ι).map comparison)
  point : comparisonOpen

private theorem nonempty_canonicalSupportAdaptedChowChart
    {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IsNoetherian X]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]
    (A : CanonicalSupportThickening F)
    (hF : ¬ IsZero F) :
    Nonempty
      (SupportAdaptedChowChart
        (A.inclusion ≫ xπ) A.modelModule) := by
  have hmodel : ¬ IsZero A.modelModule := by
    intro hzero
    apply hF
    apply A.comparisonIso.isZero_iff.mpr
    exact (pushforward A.inclusion).map_isZero hzero
  exact
    A.nonempty_supportAdaptedChowChart_of_not_isZero
      xπ hmodel

private theorem nonempty_supportChowData_of_chart
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}}
    {xπ : X ⟶ Spec (.of R)}
    {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]
    (A : CanonicalSupportThickening F)
    [IsNoetherian A.supportScheme]
    [A.supportScheme.IsSeparated]
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (C : SupportAdaptedChowChart
      (A.inclusion ≫ xπ) A.modelModule) :
    Nonempty (SupportChowData xπ A U) := by
  letI : A.modelModule.IsFiniteType :=
    isFiniteType_pullback A.inclusion F
  letI : A.modelModule.IsQuasicoherent :=
    isQuasicoherent_pullback A.inclusion F
  let W : ι → A.supportScheme.Opens :=
    fun i => A.inclusion ⁻¹ᵁ U i
  have hW : IsOpenCover W :=
    A.inclusion.iSup_preimage_eq_top hU
  have hWaff : ∀ i, IsAffineOpen (W i) := by
    intro i
    exact (hUaff i).preimage A.inclusion
  obtain ⟨n, hn⟩ :=
    C.exists_coordinateComodel_orderedBaseCechHomologyFinite
      W hW hWaff
  let E₀ := C.coordinateComodel n
  let β₀ : A.modelModule ⟶ E₀ :=
    C.coordinateComparison n
  letI : E₀.IsFiniteType :=
    C.coordinateComodel_isFiniteType n
  letI : E₀.IsQuasicoherent :=
    C.coordinateComodel_isQuasicoherent n
  refine ⟨{
    E₀ := E₀
    comparison := β₀
    finiteType := inferInstance
    quasicoherent := inferInstance
    homologyFinite := hn
    comparisonOpen := C.openSubscheme
    comparisonIsIso := C.coordinateComparison_restrict_isIso n
    point := Classical.choose C.supportPoint }⟩

private theorem nonempty_supportChowData
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]
    (A : CanonicalSupportThickening F)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (hF : ¬ IsZero F) :
    Nonempty (SupportChowData xπ A U) := by
  classical
  obtain ⟨C⟩ :=
    nonempty_canonicalSupportAdaptedChowChart
      (xπ := xπ) (F := F) A hF
  letI : A.modelModule.IsFiniteType :=
    isFiniteType_pullback A.inclusion F
  letI : A.modelModule.IsQuasicoherent :=
    isQuasicoherent_pullback A.inclusion F
  letI : IsLocallyNoetherian A.supportScheme :=
    LocallyOfFiniteType.isLocallyNoetherian A.inclusion
  letI : CompactSpace A.supportScheme :=
    A.inclusion.isClosedEmbedding.compactSpace
  letI : IsNoetherian A.supportScheme :=
    IsNoetherian.mk
  letI : A.supportScheme.IsSeparated := ⟨by
    rw [← terminal.comp_from (A.inclusion ≫ xπ)]
    infer_instance⟩
  exact
    nonempty_supportChowData_of_chart
      A U hU hUaff C

/-- A nonzero coherent module on a Noetherian proper scheme admits a
support-decreasing Chow comodel with finite Cech homology in every degree. -/
theorem exists_chowComodel_orderedBaseCechHomologyFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]
    (A : CanonicalSupportThickening F)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (hF : ¬ IsZero F) :
    ∃ (E : X.Modules) (β : F ⟶ E),
      IsChowComodel xπ U F E β := by
  classical
  obtain ⟨D⟩ :=
    nonempty_supportChowData
      (xπ := xπ) (F := F) A U hU hUaff hF
  let E := (pushforward A.inclusion).obj D.E₀
  let β : F ⟶ E :=
    A.comparisonIso.hom ≫
      (pushforward A.inclusion).map D.comparison
  letI : D.E₀.IsFiniteType := D.finiteType
  letI : D.E₀.IsQuasicoherent := D.quasicoherent
  have hEfiniteType : E.IsFiniteType := by
    exact isFiniteType_pushforward_of_isClosedImmersion A.inclusion
  have hEquasicoherent : E.IsQuasicoherent := by
    exact isQuasicoherent_pushforward_of_isAffineHom A.inclusion
  letI : E.IsFiniteType := hEfiniteType
  letI : E.IsQuasicoherent := hEquasicoherent
  have hEcech :
      OrderedBaseCechHomologyFinite xπ U E := by
    exact
      (OrderedBaseCechHomologyFinite.pushforward_iff
        A.inclusion xπ D.E₀ U).1 D.homologyFinite
  have hresidual :=
    comparisonResidual_isFiniteType_and_isQuasicoherent β
  letI :
      (kernel (Abelian.factorThruImage β)).IsFiniteType :=
    hresidual.1.1
  letI :
      (kernel (Abelian.factorThruImage β)).IsQuasicoherent :=
    hresidual.1.2
  letI :
      (cokernel (Abelian.image.ι β)).IsFiniteType :=
    hresidual.2.1
  letI :
      (cokernel (Abelian.image.ι β)).IsQuasicoherent :=
    hresidual.2.2
  haveI hβ₀open :
      IsIso
        ((restrictFunctor D.comparisonOpen.ι).map
          D.comparison) :=
    D.comparisonIsIso
  have hdrops : ResidualSupportsLt F β := by
    exact pushedComparison_residualSupports_lt
      A D.comparison D.comparisonOpen D.point
  refine ⟨E, β, ?_⟩
  exact
    ⟨hEfiniteType, hEquasicoherent, hEcech,
      hresidual.1.1, hresidual.1.2,
      hresidual.2.1, hresidual.2.2,
      Or.inr hdrops.1, Or.inr hdrops.2⟩

/-- A nonzero coherent module on a Noetherian proper scheme admits a
low-degree-finite support-decreasing Chow comodel. -/
theorem exists_chowComodel_orderedBaseCechLowDegreeFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {xπ : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation xπ] [IsProper xπ]
    {F : X.Modules} [F.IsFiniteType] [F.IsQuasicoherent]
    (A : CanonicalSupportThickening F)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (hF : ¬ IsZero F) :
    ∃ (E : X.Modules) (β : F ⟶ E),
      IsLowDegreeChowComodel xπ U F E β := by
  obtain ⟨E, β, h⟩ :=
    exists_chowComodel_orderedBaseCechHomologyFinite
      (xπ := xπ) (F := F) A U hU hUaff hF
  change E.IsFiniteType ∧ E.IsQuasicoherent ∧
    OrderedBaseCechHomologyFinite xπ U E ∧
    (kernel (Abelian.factorThruImage β)).IsFiniteType ∧
    (kernel (Abelian.factorThruImage β)).IsQuasicoherent ∧
    (cokernel (Abelian.image.ι β)).IsFiniteType ∧
    (cokernel (Abelian.image.ι β)).IsQuasicoherent ∧
    (IsZero (kernel (Abelian.factorThruImage β)) ∨
      closedStalkSupport
          (kernel (Abelian.factorThruImage β)) <
        closedStalkSupport F) ∧
    (IsZero (cokernel (Abelian.image.ι β)) ∨
      closedStalkSupport
          (cokernel (Abelian.image.ι β)) <
        closedStalkSupport F) at h
  obtain ⟨hEfinite, hEqc, hEcech, hKfinite, hKqc,
      hQfinite, hQqc, hKdrop, hQdrop⟩ := h
  exact
    ⟨E, β, hEfinite, hEqc, ⟨hEcech 0, hEcech 1⟩,
      hKfinite, hKqc, hQfinite, hQqc, hKdrop, hQdrop⟩

end CanonicalSupportThickening
end AlgebraicGeometry.Scheme.Modules
