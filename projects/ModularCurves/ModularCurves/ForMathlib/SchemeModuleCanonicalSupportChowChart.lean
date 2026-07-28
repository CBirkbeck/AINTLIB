/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.EllipticCurve.ProjectivePointChartShrink
import ModularCurves.ForMathlib.ChowCoverProjective
import ModularCurves.ForMathlib.NoetherianChowCoverOpen
import ModularCurves.ForMathlib.RelativeProjectiveFactorizationChoice
import ModularCurves.ForMathlib.SchemeModuleCanonicalSupportFull

/-!
# Support-adapted Chow charts

A nonzero canonical support model admits a Chow cover whose isomorphism
locus can be shrunk into one standard chart of the cover's chosen relative
projective embedding. The resulting open still meets the model support.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A relative-projective cover, together with an isomorphism open meeting
the support of a module and lying under one standard projective chart. -/
structure SupportAdaptedChowChart
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (xπ : X ⟶ Spec (.of R)) (M : X.Modules) where
  source : Scheme.{u}
  cover : source ⟶ X
  relativeProjective :
    IsRelativeProjectiveFactorization xπ cover
  surjective : Surjective cover
  openSubscheme : X.Opens
  coordinate :
    Fin (relativeProjective.chosenDimension + 1)
  restrictedMorphismIsIso :
    IsIso (cover ∣_ openSubscheme)
  preimage_le_coordinateOpen :
    cover ⁻¹ᵁ openSubscheme ≤
      relativeProjective.chosenProjectiveMap ⁻¹ᵁ
        MvPolynomial.coordinateOpen (R := R) coordinate
  supportPoint :
    ∃ x : openSubscheme,
      openSubscheme.ι x ∈ closedStalkSupport M

namespace CanonicalSupportThickening

variable {X : Scheme.{u}} {F : X.Modules}
  [F.IsFiniteType] [F.IsQuasicoherent]

/-- A nonzero canonical support model has a support-adapted chart on the
existing finite-affine Chow cover. -/
theorem nonempty_supportAdaptedChowChart_of_not_isZero
    {R : Type u} [CommRing R]
    (xπ : X ⟶ Spec (.of R))
    [IsNoetherian X] [LocallyOfFinitePresentation xπ] [IsProper xπ]
    (A : CanonicalSupportThickening F)
    (hzero : ¬ IsZero A.modelModule) :
    Nonempty
      (SupportAdaptedChowChart
        (A.inclusion ≫ xπ) A.modelModule) := by
  classical
  have hSupportNonempty : Nonempty A.supportScheme := by
    apply not_isEmpty_iff.mp
    intro hEmpty
    letI : IsEmpty A.supportScheme := hEmpty
    apply hzero
    apply
      (isZero_iff_closedStalkSupport_eq_bot
        A.modelModule).mpr
    rw [A.modelModule_closedStalkSupport_eq_top]
    apply Closeds.ext
    ext x
    exact isEmptyElim x
  letI : Nonempty A.supportScheme := hSupportNonempty
  let aπ : A.supportScheme ⟶ Spec (.of R) :=
    A.inclusion ≫ xπ
  letI : LocallyOfFiniteType A.inclusion := by
    infer_instance
  letI : IsLocallyNoetherian A.supportScheme := by
    exact
      LocallyOfFiniteType.isLocallyNoetherian
        A.inclusion
  letI : CompactSpace A.supportScheme :=
    A.inclusion.isClosedEmbedding.compactSpace
  letI : IsNoetherian A.supportScheme :=
    IsNoetherian.mk
  letI : LocallyOfFinitePresentation aπ := by
    dsimp only [aπ]
    infer_instance
  letI : IsProper aπ := by
    dsimp only [aπ]
    infer_instance
  letI : IsSeparated aπ := by infer_instance
  obtain ⟨ι, hι, hιnonempty, U, hcover, hU, hDense⟩ :=
    Scheme.exists_nonempty_finite_affine_openCover_dense_iInf_of_isNoetherian
      A.supportScheme
  letI : Finite ι := hι
  letI : Nonempty ι := hιnonempty
  have hcover' : ⨆ i, U i = ⊤ := by
    simpa only [IsOpenCover] using hcover
  let i : ι := Classical.choice hιnonempty
  let cover :=
    Scheme.FiniteAffineImageCover.chowToTarget aπ U hU
  let hrelative :
      IsRelativeProjectiveFactorization aπ cover :=
    Scheme.FiniteAffineImageCover.chowToTarget_isRelativeProjectiveFactorization
      aπ U hU hcover'
  let W : A.supportScheme.Opens :=
    (Scheme.FiniteAffineImageCover.commonOpen U).ι.opensRange
  letI : IsIso (cover ∣_ W) :=
    Scheme.FiniteAffineImageCover.chowToTarget_restrict_commonOpen_isIso
      aπ U hU hcover' i
  have hW : Nonempty W.toScheme := by
    dsimp only [W]
    rw [Scheme.Opens.opensRange_ι]
    exact hDense.nonempty.to_subtype
  let x : W.toScheme := Classical.choice hW
  let V : A.supportScheme.Opens :=
    cover.projectiveChartTargetShrinkAt
      hrelative.chosenProjectiveMap W x
  let j : Fin (hrelative.chosenDimension + 1) :=
    cover.projectiveChartCoordinateAt
      hrelative.chosenProjectiveMap W x
  have hxV : W.ι x ∈ V :=
    cover.mem_projectiveChartTargetShrinkAt
      hrelative.chosenProjectiveMap W x
  let y : V.toScheme := ⟨W.ι x, hxV⟩
  refine ⟨
    { source :=
        Scheme.FiniteAffineImageCover.chowObj aπ U hU
      cover := cover
      relativeProjective := hrelative
      surjective :=
        Scheme.FiniteAffineImageCover.chowToTarget_surjective
          aπ U hU hcover' hDense i
      openSubscheme := V
      coordinate := j
      restrictedMorphismIsIso :=
        cover.isIso_projectiveChartTargetShrinkAt
          hrelative.chosenProjectiveMap W x
      preimage_le_coordinateOpen :=
        cover.preimage_projectiveChartTargetShrinkAt_le_chart
          hrelative.chosenProjectiveMap W x
      supportPoint := ⟨y, ?_⟩ }⟩
  rw [A.modelModule_closedStalkSupport_eq_top]
  trivial

end CanonicalSupportThickening
end AlgebraicGeometry.Scheme.Modules
