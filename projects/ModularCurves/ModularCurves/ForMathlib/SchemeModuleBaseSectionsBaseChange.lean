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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TensorProduct
open scoped ChangeOfRings

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

private theorem baseSections_orderedCechKernelComparison_one_tmul_coe
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U)
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (hker :
      letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
        t.appTop.hom.toAlgebra
      Function.Bijective
        (ModularCurves.kerBaseChangeComparison Γ(T, (⊤ : T.Opens))
          ((orderedBaseCechComplex f M U).d 0 1).hom))
    (s : baseSections f M) :
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
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
    (eOrderedNative (eKernel (eSourceA ((1 : A) ⊗ₜ[B] s)))).1 =
      (1 : A) ⊗ₜ[B] (baseCechAugmentation f M U).hom s := by
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  dsimp only
  rw [LinearEquiv.baseChange_tmul]
  exact baseSections_orderedCechSourceBaseChange_one_tmul f M U hU A s

private theorem affinePullbackUnitTop_restrict
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    (V : Y.Opens) (s : M.presheaf.obj (op (⊤ : X.Opens))) :
    ((pullback g).obj M).presheaf.map
        (homOfLE (show V ≤ (⊤ : Y.Opens) from le_top)).op
        (affinePullbackUnitTop g M s) =
      ((pullback g).obj M).presheaf.map
        (homOfLE (show V ≤ g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op
        ((((pullbackPushforwardAdjunction g).unit.app M).val.app
          (op (⊤ : X.Opens))) s) := by
  let P := (pullback g).obj M
  let htop : (⊤ : Y.Opens) = g ⁻¹ᵁ (⊤ : X.Opens) := by simp
  let unitTop := (((pullbackPushforwardAdjunction g).unit.app M).val.app
    (op (⊤ : X.Opens))) s
  change P.presheaf.map (homOfLE le_top).op
      (P.presheaf.map (eqToHom htop).op unitTop) = _
  have hmaps :
      P.presheaf.map (eqToHom htop).op ≫
          P.presheaf.map (homOfLE le_top).op =
        P.presheaf.map
          (homOfLE (show V ≤ g ⁻¹ᵁ (⊤ : X.Opens) by simp)).op := by
    rw [← P.presheaf.map_comp]
    exact P.presheaf.congr_map (Subsingleton.elim _ _)
  exact ConcreteCategory.congr_hom hmaps unitTop

private theorem baseCechXIsoPi_hom_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (x : (baseCechComplex f M U).X n) (i : Fin (n + 1) → ι) :
    (baseCechXIsoPi f M U n).hom x i =
      Pi.π (fun j : Fin (n + 1) → ι => baseCechFactor f M U n j) i x := by
  calc
    _ = ((baseCechXIsoPi f M U n).hom ≫
        ModuleCat.ofHom (LinearMap.proj i)) x := rfl
    _ = _ := ConcreteCategory.congr_hom
      (baseCechXIsoPi_hom_comp_proj f M U n i) x

private theorem baseCechComplexBaseChange_zero_one_tmul_augmentation
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (hUaff : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    (s : baseSections f M) :
    let g := pullback.fst f t
    let f' := pullback.snd f t
    let P := (pullback g).obj M
    let Uf : ι → (Limits.pullback f t).Opens := fun i ↦ g ⁻¹ᵁ U i
    (baseCechComplexBaseChangeIso f t M U hUaff).hom.f 0
        ((1 : Γ(T, (⊤ : T.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom]
            (baseCechAugmentation f M U).hom s) =
      (baseCechAugmentation f' P Uf).hom
        (affinePullbackUnitTop g M s) := by
  dsimp only
  let g := pullback.fst f t
  let f' := pullback.snd f t
  let P := (pullback g).obj M
  let Uf : ι → (Limits.pullback f t).Opens := fun i ↦ g ⁻¹ᵁ U i
  let x : (baseCechComplex f' P Uf).X 0 :=
    (baseCechComplexBaseChangeIso f t M U hUaff).hom.f 0
      ((1 : Γ(T, (⊤ : T.Opens)))
        ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom]
          (baseCechAugmentation f M U).hom s)
  let y : (baseCechComplex f' P Uf).X 0 :=
    (baseCechAugmentation f' P Uf).hom
      (affinePullbackUnitTop g M s)
  change x = y
  apply (baseCechXIsoPi f' P Uf 0).toLinearEquiv.injective
  change (baseCechXIsoPi f' P Uf 0).hom x =
    (baseCechXIsoPi f' P Uf 0).hom y
  funext i
  rw [baseCechXIsoPi_hom_apply]
  rw [baseCechXIsoPi_hom_apply]
  dsimp only [x, y]
  rw [baseCechComplexBaseChangeIso_hom_f]
  let sourceAug := (baseCechAugmentation f M U).hom s
  let sourcePi := Pi.π (fun j : Fin 1 → ι =>
    (baseModulePresheaf f M).obj
      (op (∏ᶜ fun k : Fin 1 => U (j k)))) i
  let targetPi := Pi.π (fun j : Fin 1 → ι =>
    (baseModulePresheaf f' P).obj
      (op (∏ᶜ fun k : Fin 1 => Uf (j k)))) i
  let targetUnit := affinePullbackUnitTop g M s
  change targetPi
      ((baseCechXBaseChangeIso f t M U hUaff 0).hom
        ((1 : Γ(T, (⊤ : T.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] sourceAug)) =
    targetPi ((baseCechAugmentation f' P Uf).hom targetUnit)
  have hm : sourcePi sourceAug =
      (baseModulePresheaf f M).map
        (homOfLE (show (∏ᶜ fun k : Fin 1 => U (i k)) ≤
          (⊤ : X.Opens) from le_top)).op s := by
    dsimp only [sourcePi, sourceAug]
    exact ConcreteCategory.congr_hom
      (baseCechAugmentation_comp_π f M U i) s
  have hComponent := baseCechXBaseChangeIso_zero_one_tmul_of_projection_eq
    f t M U hUaff sourceAug s i hm
  have hNormalize :
      (baseModulePresheaf f' P).map
          (homOfLE (show (∏ᶜ fun k : Fin 1 => Uf (i k)) ≤
            (⊤ : (Limits.pullback f t).Opens) from le_top)).op
          ((((pullbackPushforwardAdjunction g).unit.app M).val.app
            (op (⊤ : X.Opens))) s) =
        (baseModulePresheaf f' P).map
          (homOfLE (show (∏ᶜ fun k : Fin 1 => Uf (i k)) ≤
            (⊤ : (Limits.pullback f t).Opens) from le_top)).op targetUnit := by
    exact (affinePullbackUnitTop_restrict g M
      (∏ᶜ fun k : Fin 1 => Uf (i k)) s).symm
  have hTarget : targetPi
      ((baseCechAugmentation f' P Uf).hom targetUnit) =
      (baseModulePresheaf f' P).map
        (homOfLE (show (∏ᶜ fun k : Fin 1 => Uf (i k)) ≤
          (⊤ : (Limits.pullback f t).Opens) from le_top)).op targetUnit := by
    dsimp only [targetPi]
    exact ConcreteCategory.congr_hom
      (baseCechAugmentation_comp_π f' P Uf i) targetUnit
  calc
    _ = ((baseCechXBaseChangeIso f t M U hUaff 0).hom ≫ targetPi)
        ((1 : Γ(T, (⊤ : T.Opens)))
          ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] sourceAug) :=
      (CategoryTheory.comp_apply _ _ _).symm
    _ = _ := hComponent
    _ = _ := hNormalize
    _ = _ := hTarget.symm

end AlgebraicGeometry.Scheme.Modules
