/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.AffineModuleCechBaseChange
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechZero

/-!
# Base change for global sections from a Cech kernel

This file turns base change for the first kernel of a finite affine Cech complex into base
change for global sections.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If the first kernel in an ordered finite affine Cech complex commutes with an affine base
change, then global sections commute with that base change. -/
noncomputable def baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (hker :
      letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
        t.appTop.hom.toAlgebra
      Function.Bijective
        (ModularCurves.kerBaseChangeComparison Γ(T, (⊤ : T.Opens))
          ((orderedBaseCechComplex f M U).d 0 1).hom)) :
    letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
      t.appTop.hom.toAlgebra
    Γ(T, (⊤ : T.Opens)) ⊗[Γ(S, (⊤ : S.Opens))] baseSections f M ≃ₗ[
        Γ(T, (⊤ : T.Opens))]
      baseSections (pullback.snd f t) ((pullback (pullback.fst f t)).obj M) := by
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let g := pullback.fst f t
  let f' := pullback.snd f t
  let P := (pullback g).obj M
  let Uf : ι → (Limits.pullback f t).Opens := fun i ↦ g ⁻¹ᵁ U i
  have hUf : IsOpenCover Uf := g.iSup_preimage_eq_top hU
  let C := baseCechComplex f M U
  let eSource := (baseSectionsIsoKernelOrderedBaseCechDifferential
    f M U hU).toLinearEquiv
  let eSourceA := LinearEquiv.baseChange B A _ _ eSource
  let eKernel : A ⊗[B]
        LinearMap.ker ((orderedBaseCechComplex f M U).d 0 1).hom ≃ₗ[A]
      LinearMap.ker
        (((orderedBaseCechComplex f M U).d 0 1).hom.baseChange A) :=
    LinearEquiv.ofBijective
      (ModularCurves.kerBaseChangeComparison A
        ((orderedBaseCechComplex f M U).d 0 1).hom) hker
  let eOrderedNative :=
    (baseCechKernelOrderedBaseChangeLinearEquiv f M U A).symm
  let eCategorical :=
    ModularCurves.HomologicalComplex.baseChangeKernelZeroLinearEquiv C A
  let eComplex :=
    (HomologicalComplex.kernelZeroIsoOfIso
      (baseCechComplexBaseChangeIso f t M U hUaff)).toLinearEquiv
  let eTarget := (baseSectionsIsoKernelBaseCechDifferential
    f' P Uf hUf).toLinearEquiv.symm
  exact eSourceA.trans <| eKernel.trans <| eOrderedNative.trans <|
    eCategorical.trans <| eComplex.trans eTarget

/-- On a pure tensor with coefficient one, the source global-sections and
ordered-Cech transports reduce to the native Cech augmentation. -/
theorem baseSections_orderedCechSourceBaseChange_one_tmul
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U)
    (A : Type u) [CommRing A] [Algebra Γ(S, (⊤ : S.Opens)) A]
    (s : baseSections f M) :
    ((baseCechKernelOrderedBaseChangeLinearEquiv f M U A).symm
      (ModularCurves.kerBaseChangeComparison A
        ((orderedBaseCechComplex f M U).d 0 1).hom
        ((1 : A) ⊗ₜ[Γ(S, (⊤ : S.Opens))]
          ((baseSectionsIsoKernelOrderedBaseCechDifferential
            f M U hU).hom s)))).1 =
      (1 : A) ⊗ₜ[Γ(S, (⊤ : S.Opens))]
        (baseCechAugmentation f M U).hom s := by
  rw [baseCechKernelOrderedBaseChangeLinearEquiv_symm_coe]
  rw [ModularCurves.kerBaseChangeComparison_coe]
  erw [LinearMap.baseChange_tmul]
  change ((orderedToBaseCechAlternatingF f M U 0).hom.baseChange A)
      ((1 : A) ⊗ₜ[Γ(S, (⊤ : S.Opens))]
        ((baseSectionsIsoKernelOrderedBaseCechDifferential
          f M U hU).hom s).1) = _
  erw [LinearMap.baseChange_tmul]
  have hinner :
      (orderedToBaseCechAlternatingF f M U 0).hom
          ((baseSectionsIsoKernelOrderedBaseCechDifferential
            f M U hU).hom s).1 =
        (baseCechAugmentation f M U).hom s := by
    change (orderedToBaseCechAlternatingF f M U 0).hom
        (baseCechKernelOrderedLinearEquiv f M U
          ((baseSectionsIsoKernelBaseCechDifferential
            f M U hU).hom s)).1 = _
    rw [baseCechKernelOrderedLinearEquiv_coe]
    calc
      _ = ((baseSectionsIsoKernelBaseCechDifferential
          f M U hU).hom s).1 := by
        simpa using ConcreteCategory.congr_hom
          (baseCechToOrderedF_comp_orderedToBaseCechAlternatingF_zero
            f M U)
          ((baseSectionsIsoKernelBaseCechDifferential
            f M U hU).hom s).1
      _ = _ := ConcreteCategory.congr_hom
        (baseSectionsIsoKernelBaseCechDifferential_hom_subtype
          f M U hU) s
  exact congrArg
    (fun y => (1 : A) ⊗ₜ[Γ(S, (⊤ : S.Opens))] y) hinner

end AlgebraicGeometry.Scheme.Modules
