/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafProjectiveCech
import ModularCurves.EllipticCurve.PoleSheafPushforwardBaseChange
import ModularCurves.EllipticCurve.PullbackTensorSection
import ModularCurves.ForMathlib.SchemeModuleBaseSectionsBaseChange
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import ModularCurves.ForMathlib.SchemeModuleRestrictPushforward

/-!
# Base change for projectively presented pole-section modules

This file proves formation of global sections of `O(n[0])` commutes with every affine base
change for a projectively presented fibrewise elliptic family over a Noetherian ring.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem pullbackFst_image_top
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    pullback.fst f U.ι ''ᵁ
        (⊤ : (CategoryTheory.Limits.pullback f U.ι).Opens) =
      f ⁻¹ᵁ U := by
  let t := U.ι
  let g := pullback.fst f t
  let fU := pullback.snd f t
  let H : IsPullback fU g t f :=
    (IsPullback.of_hasPullback f t).flip
  have hSquare :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      H (⊤ : U.toScheme.Opens)
  calc
    g ''ᵁ (⊤ : (CategoryTheory.Limits.pullback f t).Opens) =
        f ⁻¹ᵁ (t ''ᵁ (⊤ : U.toScheme.Opens)) := by
      simpa only [Scheme.Hom.preimage_top] using hSquare
    _ = f ⁻¹ᵁ U := by rw [U.ι_image_top]

private noncomputable def baseSectionsOpenRestrictIso
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (M : X.Modules) :
    let t := U.ι
    let g := pullback.fst f t
    baseSections (g ≫ f) (M.restrict g) ≅
      (baseModulePresheaf (𝟙 S) ((pushforward f).obj M)).obj (op U) := by
  dsimp only
  let t := U.ι
  let g := pullback.fst f t
  let ePush := baseModulePresheafPushforwardAppIso f (𝟙 S) M U
  rw [Category.comp_id] at ePush
  exact baseModulePresheafRestrictAppIso f g M
      (⊤ : (CategoryTheory.Limits.pullback f t).Opens) ≪≫
    (baseModulePresheaf f M).mapIso
      (eqToIso (pullbackFst_image_top f U).symm).op ≪≫
    ePush

private theorem baseSectionsOpenRestrictIso_hom_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (M : X.Modules)
    (x : baseSections (pullback.fst f U.ι ≫ f)
      (M.restrict (pullback.fst f U.ι))) :
    (baseSectionsOpenRestrictIso f U M).hom x =
      M.presheaf.map
        (eqToHom (pullbackFst_image_top f U).symm).op
        ((M.restrictAppIso (pullback.fst f U.ι)
          (⊤ : (CategoryTheory.Limits.pullback f U.ι).Opens)).hom x) := by
  rfl

private theorem baseSectionsOpenRestrictIso_hom_pullbackUnit
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (M : X.Modules)
    (m : Γ(M, (⊤ : X.Opens))) :
    let t := U.ι
    let g := pullback.fst f t
    let N := (pushforward f).obj M
    (baseSectionsOpenRestrictIso f U M).hom
        (((restrictFunctorIsoPullback g).app M).inv.val.app (.op ⊤)
          (affinePullbackUnitTop g M m)) =
      (baseModulePresheaf (𝟙 S) N).map U.leTop.op
        (pushforwardTopSection f M m) := by
  dsimp only
  let g := pullback.fst f U.ι
  have hUnit :=
    restrictFunctorIsoPullback_inv_affinePullbackUnitTop g M m
  calc
    _ = (baseSectionsOpenRestrictIso f U M).hom
        ((M.restrict g).presheaf.map
          (eqToHom (Scheme.Hom.preimage_top g).symm).op
          (((restrictAdjunction g).unit.app M).val.app (.op ⊤) m)) :=
      congrArg (fun x =>
        (baseSectionsOpenRestrictIso f U M).hom x) hUnit
    _ = _ := by
      let x := (M.restrict g).presheaf.map
        (eqToHom (Scheme.Hom.preimage_top g).symm).op
        (((restrictAdjunction g).unit.app M).val.app (.op ⊤) m)
      have hOpen := baseSectionsOpenRestrictIso_hom_apply f U M x
      have hTail : M.presheaf.map
          (eqToHom (pullbackFst_image_top f U).symm).op
            ((M.restrictAppIso g
              (⊤ : (CategoryTheory.Limits.pullback f U.ι).Opens)).hom x) =
        M.presheaf.map ((Opens.map f.base).op.map U.leTop.op)
          (M.presheaf.map
            (eqToHom (Scheme.Hom.preimage_top f)).op m) := by
        dsimp only [x]
        let a := (eqToHom (Scheme.Hom.preimage_top g).symm).op
        let unitTop :=
          (((restrictAdjunction g).unit.app M).val.app (.op ⊤)) m
        have hRestrict := ConcreteCategory.congr_hom
          (M.map_restrictAppIso_hom g a) unitTop
        conv_lhs at hRestrict =>
          erw [ConcreteCategory.comp_apply]
        conv_rhs at hRestrict =>
          erw [ConcreteCategory.comp_apply]
        rw [hRestrict]
        change M.presheaf.map
            (eqToHom (pullbackFst_image_top f U).symm).op
              (M.presheaf.map
                (homOfLE (Scheme.Hom.image_mono g
                  (leOfHom a.unop))).op unitTop) =
          M.presheaf.map ((Opens.map f.base).op.map U.leTop.op)
            (M.presheaf.map
              (eqToHom (Scheme.Hom.preimage_top f)).op m)
        dsimp only [unitTop]
        have hAdj := ConcreteCategory.congr_hom
          (restrictAdjunction_unit_app_app g M (⊤ : X.Opens)) m
        change (((restrictAdjunction g).unit.app M).val.app (.op ⊤)) m =
          M.presheaf.map
            (homOfLE (g.image_preimage_le (⊤ : X.Opens))).op m at hAdj
        rw [hAdj]
        rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply,
          ← M.presheaf.map_comp_apply]
        exact ConcreteCategory.congr_hom
          (M.presheaf.congr_map (Subsingleton.elim _ _)) m
      exact hOpen.trans hTail

private theorem baseSectionsEqToIso_hom_apply
    {X S : Scheme.{u}} {q q' : X ⟶ S} (hq : q = q') (M : X.Modules)
    (x : baseSections q M) :
    (eqToIso (congrArg (fun k => baseSections k M) hq)).hom x = x := by
  subst q'
  rfl

private noncomputable def baseSectionsOpenAfterIso
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (M : X.Modules) :
    let t := U.ι
    let g := pullback.fst f t
    let fU := pullback.snd f t
    (ModuleCat.restrictScalars t.appTop.hom).obj
        (baseSections fU (M.restrict g)) ≅
      (baseModulePresheaf (𝟙 S) ((pushforward f).obj M)).obj (op U) := by
  dsimp only
  let t := U.ι
  let g := pullback.fst f t
  let fU := pullback.snd f t
  exact baseSectionsCompIso fU t (M.restrict g) ≪≫
    eqToIso (congrArg (fun q => baseSections q (M.restrict g))
      pullback.condition.symm) ≪≫
    baseSectionsOpenRestrictIso f U M

private theorem baseSectionsOpenAfterIso_hom_apply
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (M : X.Modules)
    (x : baseSections (pullback.snd f U.ι)
      (M.restrict (pullback.fst f U.ι))) :
    (baseSectionsOpenAfterIso f U M).hom x =
      (baseSectionsOpenRestrictIso f U M).hom x := by
  dsimp only [baseSectionsOpenAfterIso]
  conv_lhs =>
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  rw [baseSectionsCompIso_hom_apply]
  have hEq := baseSectionsEqToIso_hom_apply pullback.condition.symm
    (M.restrict (pullback.fst f U.ι)) x
  exact congrArg
    (fun y => (baseSectionsOpenRestrictIso f U M).hom y) hEq

private theorem baseSectionsOpenAfterIso_hom_pullbackUnit
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (M : X.Modules)
    (m : Γ(M, (⊤ : X.Opens))) :
    let g := pullback.fst f U.ι
    (baseSectionsOpenAfterIso f U M).hom
        (((restrictFunctorIsoPullback g).app M).inv.val.app (.op ⊤)
          (affinePullbackUnitTop g M m)) =
      (baseModulePresheaf (𝟙 S) ((pushforward f).obj M)).map U.leTop.op
        (pushforwardTopSection f M m) := by
  dsimp only
  let g := pullback.fst f U.ι
  let x := ((restrictFunctorIsoPullback g).app M).inv.val.app (.op ⊤)
    (affinePullbackUnitTop g M m)
  have hAfter := baseSectionsOpenAfterIso_hom_apply f U M x
  exact hAfter.trans
    (baseSectionsOpenRestrictIso_hom_pullbackUnit f U M m)

private noncomputable def
    baseSectionsRestrictLinearEquivOfOrderedCechKernelComparison
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [IsOpenImmersion t]
    (hker :
      letI : Algebra Γ(S, (⊤ : S.Opens)) Γ(T, (⊤ : T.Opens)) :=
        t.appTop.hom.toAlgebra
      Function.Bijective
        (ModularCurves.kerBaseChangeComparison Γ(T, (⊤ : T.Opens))
          ((orderedBaseCechComplex f M U).d 0 1).hom)) :
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    let g := pullback.fst f t
    let fT := pullback.snd f t
    A ⊗[B] baseSections f M ≃ₗ[A]
      baseSections fT (M.restrict g) := by
  dsimp only
  let g := pullback.fst f t
  let fT := pullback.snd f t
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : IsOpenImmersion g :=
    MorphismProperty.pullback_fst f t inferInstance
  let ePullback :=
    baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison
      f t M U hU hUaff hker
  let eRestrict := (baseSectionsMapIso fT
    ((restrictFunctorIsoPullback g).app M)).symm.toLinearEquiv
  exact ePullback.trans eRestrict

private theorem
    baseSectionsRestrictLinearEquivOfOrderedCechKernelComparison_one_tmul
    {X S T : Scheme.{u}} (f : X ⟶ S) (t : T ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [IsOpenImmersion t]
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
    let g := pullback.fst f t
    baseSectionsRestrictLinearEquivOfOrderedCechKernelComparison
        f t M U hU hUaff hker ((1 : A) ⊗ₜ[B] s) =
      ((restrictFunctorIsoPullback g).app M).inv.val.app (.op ⊤)
        (affinePullbackUnitTop g M s) := by
  dsimp only
  let g := pullback.fst f t
  let fT := pullback.snd f t
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : IsOpenImmersion g :=
    MorphismProperty.pullback_fst f t inferInstance
  let ePullback :=
    baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison
      f t M U hU hUaff hker
  let eRestrictIso := baseSectionsMapIso fT
    ((restrictFunctorIsoPullback g).app M)
  dsimp only [baseSectionsRestrictLinearEquivOfOrderedCechKernelComparison]
  change eRestrictIso.inv (ePullback ((1 : A) ⊗ₜ[B] s)) = _
  rw [baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison_one_tmul]
  rfl

private noncomputable def finiteAffineCoverBasicOpenBaseSectionsEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [M.IsQuasicoherent]
    (r : Γ(S, (⊤ : S.Opens))) :
    let V := S.basicOpen r
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(V.toScheme, (⊤ : V.toScheme.Opens))
    letI : Algebra B A := V.ι.appTop.hom.toAlgebra
    TensorProduct B A (baseSections f M) ≃ₗ[B]
      (baseModulePresheaf (𝟙 S) ((pushforward f).obj M)).obj (op V) := by
  dsimp only
  let V := S.basicOpen r
  let t := V.ι
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(V.toScheme, (⊤ : V.toScheme.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : IsLocalization.Away r A := inferInstance
  letI : Module.Flat B A :=
    IsLocalization.flat A (Submonoid.powers r)
  let hker := ModularCurves.kerBaseChangeComparison_bijective_of_flat
    (A := A) (f := ((orderedBaseCechComplex f M U).d 0 1).hom)
  let eBefore :=
    baseSectionsRestrictLinearEquivOfOrderedCechKernelComparison
      f t M U hU hUaff hker
  let eBeforeB := ((ModuleCat.restrictScalars t.appTop.hom).mapIso
    eBefore.toModuleIso).toLinearEquiv
  let eAfter := (baseSectionsOpenAfterIso f V M).toLinearEquiv
  exact eBeforeB.trans eAfter

private theorem finiteAffineCoverBasicOpenBaseSectionsEquiv_one_tmul
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [M.IsQuasicoherent]
    (r : Γ(S, (⊤ : S.Opens))) (s : baseSections f M) :
    let V := S.basicOpen r
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(V.toScheme, (⊤ : V.toScheme.Opens))
    letI : Algebra B A := V.ι.appTop.hom.toAlgebra
    finiteAffineCoverBasicOpenBaseSectionsEquiv f M U hU hUaff r
        ((1 : A) ⊗ₜ[B] s) =
      (baseModulePresheaf (𝟙 S) ((pushforward f).obj M)).map V.leTop.op
        (pushforwardTopSection f M s) := by
  dsimp only
  let V := S.basicOpen r
  let t := V.ι
  let g := pullback.fst f t
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(V.toScheme, (⊤ : V.toScheme.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : IsLocalization.Away r A := inferInstance
  letI : Module.Flat B A :=
    IsLocalization.flat A (Submonoid.powers r)
  let hker := ModularCurves.kerBaseChangeComparison_bijective_of_flat
    (A := A) (f := ((orderedBaseCechComplex f M U).d 0 1).hom)
  let eBefore :=
    baseSectionsRestrictLinearEquivOfOrderedCechKernelComparison
      f t M U hU hUaff hker
  let eBeforeB := ((ModuleCat.restrictScalars t.appTop.hom).mapIso
    eBefore.toModuleIso).toLinearEquiv
  let eAfter := (baseSectionsOpenAfterIso f V M).toLinearEquiv
  have hBefore :=
    baseSectionsRestrictLinearEquivOfOrderedCechKernelComparison_one_tmul
      f t M U hU hUaff hker s
  have hBeforeB : eBeforeB ((1 : A) ⊗ₜ[B] s) =
      ((restrictFunctorIsoPullback g).app M).inv.val.app (.op ⊤)
        (affinePullbackUnitTop g M s) := hBefore
  have hAfter := baseSectionsOpenAfterIso_hom_pullbackUnit f V M s
  have hMain :
      finiteAffineCoverBasicOpenBaseSectionsEquiv f M U hU hUaff r =
        eBeforeB.trans eAfter := rfl
  have hMainApply := congrArg
    (fun e => e ((1 : A) ⊗ₜ[B] s)) hMain
  have hTrans := LinearEquiv.trans_apply
    (e₁₂ := eBeforeB) (e₂₃ := eAfter) ((1 : A) ⊗ₜ[B] s)
  calc
    _ = eAfter (eBeforeB ((1 : A) ⊗ₜ[B] s)) := hMainApply.trans hTrans
    _ = _ := congrArg (fun x => eAfter x) hBeforeB |>.trans hAfter

end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable def baseModulePresheafIdTopIso
    {S : Scheme.{u}} (N : S.Modules) :
    ModuleCat.of Γ(S, (⊤ : S.Opens)) Γ(N, (⊤ : S.Opens)) ≅
      (Scheme.Modules.baseModulePresheaf (𝟙 S) N).obj
        (.op (⊤ : S.Opens)) := by
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext (x : Γ(N, (⊤ : S.Opens)))
  change
    S.presheaf.map
        ((initialOpOfTerminal isTerminalTop).to
          (.op (⊤ : S.Opens)))
        (Scheme.Hom.appTop (𝟙 S) r) • x = r • x
  rw [Scheme.Hom.id_appTop]
  rw [show (initialOpOfTerminal isTerminalTop).to
    (.op (⊤ : S.Opens)) = 𝟙 _ from Subsingleton.elim _ _]
  simp

/-- Global sections of `O(n[0])` on a projectively presented fibrewise elliptic family commute
with every affine base change. -/
noncomputable def
    FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    A ⊗[B] Scheme.Modules.baseSections π M ≃ₗ[A]
      Scheme.Modules.baseSections πT MT := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : M.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm z hz n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage f
  let hdata :=
    h.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_kernel_data
      f hsm z hz hn
  let ePullback :=
    Scheme.Modules.baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison
      π t M U hU hUaff (hdata.2.2.1 A)
  let ePole := (Scheme.Modules.baseSectionsMapIso πT
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)).toLinearEquiv
  exact ePullback.trans ePole

/-- The projective pole-section base-change equivalence agrees on pure tensors
with the pullback unit followed by the canonical pole-sheaf pullback isomorphism. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv_one_tmul
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R))
    (s : Scheme.Modules.baseSections
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (sectionPoleSheafPower
        (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz n)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let g := pullback.fst π t
    let πT := pullback.snd π t
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
        f hsm z hz hn t ((1 : A) ⊗ₜ[B] s) =
      (Scheme.Modules.baseSectionsMapIso πT
        (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)).hom
          (Scheme.Modules.affinePullbackUnitTop g M s) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : M.IsQuasicoherent := sectionPoleSheafPower_isQuasicoherent hsm z hz n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen (R := R) j).preimage f
  let hdata :=
    h.sectionPoleSheafPower_projectiveClosed_orderedBaseCech_kernel_data
      f hsm z hz hn
  let ePullback :=
    Scheme.Modules.baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison
      π t M U hU hUaff (hdata.2.2.1 A)
  let ePole := (Scheme.Modules.baseSectionsMapIso πT
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)).toLinearEquiv
  dsimp only [
    FibrewiseElliptic.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv]
  change ePole (ePullback ((1 : A) ⊗ₜ[B] s)) = _
  rw [Scheme.Modules.baseSectionsBaseChangeLinearEquivOfOrderedCechKernelComparison_one_tmul]
  rfl

/-- On pure tensors, the projective pole-section base-change equivalence agrees
with the canonical pole-sheaf pushforward base-change morphism. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPowerPushforwardBaseChange_projectiveClosed_app_top_one_tmul
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)) [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R))
    (s : Scheme.Modules.baseSections
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (sectionPoleSheafPower
        (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz n)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    (sectionPoleSheafPowerPushforwardBaseChange hsm z hz t n).app
        (⊤ : T.Opens)
          (Scheme.Modules.affinePullbackUnitTop t
            ((Scheme.Modules.pushforward π).obj M)
              (Scheme.Modules.pushforwardTopSection π M s)) =
      Scheme.Modules.pushforwardTopSection πT MT
        (h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
          f hsm z hz hn t ((1 : A) ⊗ₜ[B] s)) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let e := sectionPoleSheafPowerBaseChangeIso hsm z hz t n
  let fibreUnit := Scheme.Modules.affinePullbackUnitTop g M s
  calc
    _ = Scheme.Modules.pushforwardTopSection πT MT (e.hom.app
        (⊤ : (pullback π t).Opens) fibreUnit) :=
      sectionPoleSheafPowerPushforwardBaseChange_app_top_pullbackUnit
        hsm z hz t n s
    _ = _ := congrArg (Scheme.Modules.pushforwardTopSection πT MT)
      (h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv_one_tmul
        f hsm z hz hn t s).symm

private noncomputable def projectivePoleBaseSectionsRestrictEquiv
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) [IsOpenImmersion t] :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let g := pullback.fst π t
    let πT := pullback.snd π t
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    TensorProduct B A (Scheme.Modules.baseSections π M) ≃ₗ[A]
      Scheme.Modules.baseSections πT (M.restrict g) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let eProjective :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
      f hsm z hz hn t
  let ePole := (Scheme.Modules.baseSectionsMapIso πT
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)).symm.toLinearEquiv
  let eRestrict := (Scheme.Modules.baseSectionsMapIso πT
    ((Scheme.Modules.restrictFunctorIsoPullback g).app M)).symm.toLinearEquiv
  exact eProjective.trans (ePole.trans eRestrict)

private theorem projectivePoleBaseSectionsRestrictEquiv_one_tmul
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) [IsOpenImmersion t]
    (s : Scheme.Modules.baseSections
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (sectionPoleSheafPower
        (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz n)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let g := pullback.fst π t
    let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
    let A := Γ(T, (⊤ : T.Opens))
    letI : Algebra B A := t.appTop.hom.toAlgebra
    projectivePoleBaseSectionsRestrictEquiv f hsm z hz h hn t
        ((1 : A) ⊗ₜ[B] s) =
      ((Scheme.Modules.restrictFunctorIsoPullback g).app M).inv.val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g M
          (s : Γ(M, (⊤ : E.Opens)))) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let eProjective :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
      f hsm z hz hn t
  let ePoleIso := Scheme.Modules.baseSectionsMapIso πT
    (sectionPoleSheafPowerBaseChangeIso hsm z hz t n)
  let eRestrictIso := Scheme.Modules.baseSectionsMapIso πT
    ((Scheme.Modules.restrictFunctorIsoPullback g).app M)
  let sTop : Γ(M, (⊤ : E.Opens)) := s
  let y := Scheme.Modules.affinePullbackUnitTop g M sTop
  have hProjective :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv_one_tmul
      f hsm z hz hn t s
  dsimp only [projectivePoleBaseSectionsRestrictEquiv]
  change eRestrictIso.inv
      (ePoleIso.inv (eProjective ((1 : A) ⊗ₜ[B] s))) = _
  have hProjective' : eProjective ((1 : A) ⊗ₜ[B] s) = ePoleIso.hom y :=
    hProjective
  have hPole : ePoleIso.inv (ePoleIso.hom y) = y :=
    ePoleIso.hom_inv_id_apply y
  calc
    _ = eRestrictIso.inv (ePoleIso.inv (ePoleIso.hom y)) :=
      congrArg (fun x => eRestrictIso.inv (ePoleIso.inv x)) hProjective'
    _ = eRestrictIso.inv y := congrArg (fun x => eRestrictIso.inv x) hPole
    _ = _ := rfl

private noncomputable def projectivePoleBasicOpenBaseSectionsEquiv
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n)
    (r : Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))) :
    let S := Spec (.of R)
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let N := (Scheme.Modules.pushforward π).obj M
    let U := S.basicOpen r
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(U.toScheme, (⊤ : U.toScheme.Opens))
    letI : Algebra B A := U.ι.appTop.hom.toAlgebra
    TensorProduct B A (Scheme.Modules.baseSections π M) ≃ₗ[B]
      (Scheme.Modules.baseModulePresheaf (𝟙 S) N).obj (op U) := by
  dsimp only
  let S := Spec (.of R)
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let U := S.basicOpen r
  let t := U.ι
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(U.toScheme, (⊤ : U.toScheme.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let eBefore := projectivePoleBaseSectionsRestrictEquiv
    f hsm z hz h hn t
  let eBeforeB := ((ModuleCat.restrictScalars t.appTop.hom).mapIso
    eBefore.toModuleIso).toLinearEquiv
  let eAfter :=
    (Scheme.Modules.baseSectionsOpenAfterIso π U M).toLinearEquiv
  exact eBeforeB.trans eAfter

private theorem projectivePoleBasicOpenBaseSectionsEquiv_one_tmul
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n)
    (r : Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)))
    (s : Scheme.Modules.baseSections
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (sectionPoleSheafPower
        (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz n)) :
    let S := Spec (.of R)
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    let N := (Scheme.Modules.pushforward π).obj M
    let U := S.basicOpen r
    let B := Γ(S, (⊤ : S.Opens))
    let A := Γ(U.toScheme, (⊤ : U.toScheme.Opens))
    letI : Algebra B A := U.ι.appTop.hom.toAlgebra
    projectivePoleBasicOpenBaseSectionsEquiv f hsm z hz h hn r
        ((1 : A) ⊗ₜ[B] s) =
      (Scheme.Modules.baseModulePresheaf (𝟙 S) N).map U.leTop.op
        (Scheme.Modules.pushforwardTopSection π M s) := by
  dsimp only
  let S := Spec (.of R)
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let U := S.basicOpen r
  let t := U.ι
  let g := pullback.fst π t
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(U.toScheme, (⊤ : U.toScheme.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  let eBefore := projectivePoleBaseSectionsRestrictEquiv
    f hsm z hz h hn t
  let eBeforeB := ((ModuleCat.restrictScalars t.appTop.hom).mapIso
    eBefore.toModuleIso).toLinearEquiv
  let eAfter :=
    (Scheme.Modules.baseSectionsOpenAfterIso π U M).toLinearEquiv
  have hMain :
      projectivePoleBasicOpenBaseSectionsEquiv f hsm z hz h hn r =
        eBeforeB.trans eAfter := rfl
  have hMainApply := congrArg
    (fun e => e ((1 : A) ⊗ₜ[B] s)) hMain
  have hTrans := LinearEquiv.trans_apply
    (e₁₂ := eBeforeB) (e₂₃ := eAfter) ((1 : A) ⊗ₜ[B] s)
  have hBefore := projectivePoleBaseSectionsRestrictEquiv_one_tmul
    f hsm z hz h hn t s
  have hBeforeB : eBeforeB ((1 : A) ⊗ₜ[B] s) =
      ((Scheme.Modules.restrictFunctorIsoPullback g).app M).inv.val.app (.op ⊤)
        (Scheme.Modules.affinePullbackUnitTop g M
          (s : Γ(M, (⊤ : E.Opens)))) := hBefore
  have hAfter :=
    Scheme.Modules.baseSectionsOpenAfterIso_hom_pullbackUnit π U M s
  calc
    _ = eAfter (eBeforeB ((1 : A) ⊗ₜ[B] s)) := hMainApply.trans hTrans
    _ = _ := congrArg (fun x => eAfter x) hBeforeB |>.trans hAfter

private theorem isQuasicoherent_of_basicOpen_tensorEquiv_of_topEquiv
    {S : Scheme.{u}} [IsAffine S] (N : S.Modules)
    (P : ModuleCat.{u} Γ(S, (⊤ : S.Opens)))
    (eTop : P ≃ₗ[Γ(S, (⊤ : S.Opens))]
      (Scheme.Modules.baseModulePresheaf (𝟙 S) N).obj
        (op (⊤ : S.Opens)))
    (eOpen : ∀ r : Γ(S, (⊤ : S.Opens)),
      let U := S.basicOpen r
      let B := Γ(S, (⊤ : S.Opens))
      let A := Γ(U.toScheme, (⊤ : U.toScheme.Opens))
      letI : Algebra B A := U.ι.appTop.hom.toAlgebra
      TensorProduct B A P ≃ₗ[B]
        (Scheme.Modules.baseModulePresheaf (𝟙 S) N).obj (op U))
    (heOpen : ∀ (r : Γ(S, (⊤ : S.Opens))) (p : P),
      let U := S.basicOpen r
      let B := Γ(S, (⊤ : S.Opens))
      let A := Γ(U.toScheme, (⊤ : U.toScheme.Opens))
      letI : Algebra B A := U.ι.appTop.hom.toAlgebra
      eOpen r ((1 : A) ⊗ₜ[B] p) =
        (Scheme.Modules.baseModulePresheaf (𝟙 S) N).map U.leTop.op
          (eTop p)) :
    N.IsQuasicoherent := by
  apply Scheme.Modules.isQuasicoherent_of_isLocalized_basicOpen N
  intro r
  let U := S.basicOpen r
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(U.toScheme, (⊤ : U.toScheme.Opens))
  letI : Algebra B A := U.ι.appTop.hom.toAlgebra
  let er := eOpen r
  let localizationUnit : P →ₗ[B] TensorProduct B A P :=
    TensorProduct.mk B A P 1
  let target := er.toLinearMap.comp localizationUnit
  let ψ := ((Scheme.Modules.baseModulePresheaf (𝟙 S) N).map U.leTop.op).hom
  let composedRestriction := ψ.comp eTop.toLinearMap
  letI : IsLocalization.Away r A := inferInstance
  letI : IsLocalizedModule.Away r localizationUnit := inferInstance
  letI : IsLocalizedModule.Away r target :=
    IsLocalizedModule.of_linearEquiv
      (Submonoid.powers r) localizationUnit er
  have hTarget : IsLocalizedModule.Away r target := inferInstance
  have hRestriction : target = composedRestriction := by
    ext p
    have hUnit : target p = er ((1 : A) ⊗ₜ[B] p) := by
      dsimp only [target, localizationUnit]
      rw [LinearMap.comp_apply]
      exact congrArg (fun y => er y)
        (TensorProduct.mk_apply (R := B) (M := A) (N := P) (1 : A) p)
    have hGenerator := heOpen r p
    have hComposed : composedRestriction p = ψ (eTop p) := by
      dsimp only [composedRestriction]
      rw [LinearMap.comp_apply]
      rfl
    rw [hUnit, hGenerator]
    exact hComposed.symm
  have hComposedLocalized :
      IsLocalizedModule.Away r composedRestriction := by
    rw [← hRestriction]
    exact hTarget
  exact (IsLocalizedModule.comp_iff_of_bijective_right
    (S := Submonoid.powers r) eTop.toLinearMap eTop.bijective).mp
      hComposedLocalized

private theorem pushforward_isQuasicoherent_of_finiteAffineCover
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} [Fintype ι] [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    [X.IsSeparated] [IsAffine S] [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward f).obj M
  let eTopIso := Scheme.Modules.baseSectionsPushforwardTopIso f M
  let eTop := eTopIso.toLinearEquiv
  let eOpen := fun r =>
    Scheme.Modules.finiteAffineCoverBasicOpenBaseSectionsEquiv
      f M U hU hUaff r
  apply isQuasicoherent_of_basicOpen_tensorEquiv_of_topEquiv N
    (Scheme.Modules.baseSections f M) eTop eOpen
  intro r s
  let V := S.basicOpen r
  let ψ := ((Scheme.Modules.baseModulePresheaf (𝟙 S) N).map V.leTop.op).hom
  have hOpen :=
    Scheme.Modules.finiteAffineCoverBasicOpenBaseSectionsEquiv_one_tmul
      f M U hU hUaff r s
  have hTop : eTopIso.hom s =
      Scheme.Modules.pushforwardTopSection f M s := rfl
  have hTopMapped := congrArg (fun y => ψ y) hTop.symm
  exact hOpen.trans hTopMapped

/-- Positive pole-sheaf pushforwards on a projectively presented fibrewise
elliptic family are quasicoherent. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPowerPushforward_projectiveClosed_isQuasicoherent
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let M := sectionPoleSheafPower π z hz n
    ((Scheme.Modules.pushforward π).obj M).IsQuasicoherent := by
  dsimp only
  let S := Spec (.of R)
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let N := (Scheme.Modules.pushforward π).obj M
  let eTopIso := Scheme.Modules.baseSectionsPushforwardTopIso π M
  let eTop := eTopIso.toLinearEquiv
  let eOpen := fun r => projectivePoleBasicOpenBaseSectionsEquiv
    f hsm z hz h hn r
  apply isQuasicoherent_of_basicOpen_tensorEquiv_of_topEquiv N
    (Scheme.Modules.baseSections π M) eTop eOpen
  intro r s
  let U := S.basicOpen r
  let ψ := ((Scheme.Modules.baseModulePresheaf (𝟙 S) N).map U.leTop.op).hom
  have hOpen := projectivePoleBasicOpenBaseSectionsEquiv_one_tmul
    f hsm z hz h hn r s
  have hTop : eTopIso.hom s =
      Scheme.Modules.pushforwardTopSection π M s := rfl
  have hTopMapped := congrArg (fun y => ψ y) hTop.symm
  exact hOpen.trans hTopMapped

/-- After an arbitrary affine base change, pole-sheaf pushforwards on a
projectively presented smooth relative curve are quasicoherent. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPowerPushforward_baseChange_projectiveClosed_isQuasicoherent
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (n : ℕ) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    let πT := pullback.snd π t
    let zT := sectionBaseChange z hz t
    let hzT := sectionBaseChange_snd z hz t
    let MT := sectionPoleSheafPower πT zT hzT n
    ((Scheme.Modules.pushforward πT).obj MT).IsQuasicoherent := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let g := pullback.fst π t
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  letI : IsSeparated π := by
    dsimp only [π, MvPolynomial.homogeneousProjπ]
    infer_instance
  letI : IsSeparated πT := inferInstance
  letI : (pullback π t).IsSeparated := ⟨by
    rw [← terminal.comp_from πT]
    infer_instance⟩
  have hsmT : SmoothOfRelativeDimension 1 πT :=
    (AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback π t) hsm
  let MT := sectionPoleSheafPower πT zT hzT n
  letI : MT.IsQuasicoherent :=
    sectionPoleSheafPower_isQuasicoherent hsmT zT hzT n
  let U := fun j => f ⁻¹ᵁ MvPolynomial.coordinateOpenCover
    (R := R) (σ := σ) j
  have hU : IsOpenCover U := by
    exact f.iSup_preimage_eq_top
      (MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ))
  have hUaff : ∀ j, IsAffineOpen (U j) := by
    intro j
    exact (MvPolynomial.coordinateOpenCover_isAffineOpen
      (R := R) j).preimage f
  let UT := fun j => g ⁻¹ᵁ U j
  have hUT : IsOpenCover UT := g.iSup_preimage_eq_top hU
  have hUTaff : ∀ j, IsAffineOpen (UT j) := by
    intro j
    exact IsAffineOpen.preimage_pullback_fst π t (hUaff j)
  exact pushforward_isQuasicoherent_of_finiteAffineCover
    πT MT UT hUT hUTaff

/-- The canonical pole-sheaf pushforward base-change morphism is an isomorphism on global
sections for every affine base change of a projectively presented fibrewise elliptic family. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPowerPushforwardBaseChange_projectiveClosed_app_top_isIso
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    IsIso ((sectionPoleSheafPowerPushforwardBaseChange (π := π) hsm z hz t n).val.app
      (.op (⊤ : T.Opens))) := by
  dsimp only
  let S := Spec (.of R)
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let N := (Scheme.Modules.pushforward π).obj M
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let B := Γ(S, (⊤ : S.Opens))
  let A := Γ(T, (⊤ : T.Opens))
  letI : Algebra B A := t.appTop.hom.toAlgebra
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : N.IsQuasicoherent :=
    h.sectionPoleSheafPowerPushforward_projectiveClosed_isQuasicoherent
      f hsm z hz hn
  let ePush := Scheme.Modules.baseSectionsPushforwardTopIso π M
  let eSourceIso :=
    (ModuleCat.extendScalars t.appTop.hom).mapIso ePush ≪≫
      Scheme.Modules.affinePullbackΓIso t N
  let eSource :
      A ⊗[B] Scheme.Modules.baseSections π M ≃ₗ[A]
        Γ((Scheme.Modules.pullback t).obj N, (⊤ : T.Opens)) :=
    eSourceIso.toLinearEquiv
  let eProjective :=
    h.sectionPoleSheafPower_projectiveClosed_baseSectionsBaseChangeLinearEquiv
      f hsm z hz hn t
  let eTargetTopIso :=
    Scheme.Modules.baseSectionsPushforwardTopIso πT MT ≪≫
      (baseModulePresheafIdTopIso
        ((Scheme.Modules.pushforward πT).obj MT)).symm
  let eTargetTop :
      Scheme.Modules.baseSections πT MT ≃ₗ[A]
        Γ((Scheme.Modules.pushforward πT).obj MT, (⊤ : T.Opens)) :=
    eTargetTopIso.toLinearEquiv
  let eTarget := eProjective.trans eTargetTop
  let φ := sectionPoleSheafPowerPushforwardBaseChange hsm z hz t n
  let φTop :
      Γ((Scheme.Modules.pullback t).obj N, (⊤ : T.Opens)) →ₗ[A]
        Γ((Scheme.Modules.pushforward πT).obj MT, (⊤ : T.Opens)) :=
    (φ.val.app (.op (⊤ : T.Opens))).hom
  have hSource (s : Scheme.Modules.baseSections π M) :
      eSource ((1 : A) ⊗ₜ[B] s) =
        Scheme.Modules.affinePullbackUnitTop t N
          (Scheme.Modules.pushforwardTopSection π M s) := by
    change (Scheme.Modules.affinePullbackΓIso t N).hom
        (((ModuleCat.extendScalars t.appTop.hom).map ePush.hom)
          ((1 : Γ(T, (⊤ : T.Opens)))
            ⊗ₜ[Γ(S, (⊤ : S.Opens)), t.appTop.hom] s)) = _
    rw [ModuleCat.ExtendScalars.map_tmul
      (f := t.appTop.hom) ePush.hom
        (1 : Γ(T, (⊤ : T.Opens))) s]
    rw [Scheme.Modules.baseSectionsPushforwardTopIso_hom_apply]
    exact Scheme.Modules.affinePullbackΓIso_hom_one_tmul t N
      (Scheme.Modules.pushforwardTopSection π M s)
  have hTarget (s : Scheme.Modules.baseSections π M) :
      eTarget ((1 : A) ⊗ₜ[B] s) =
        Scheme.Modules.pushforwardTopSection πT MT
          (eProjective ((1 : A) ⊗ₜ[B] s)) := by
    change (baseModulePresheafIdTopIso
        ((Scheme.Modules.pushforward πT).obj MT)).inv
        ((Scheme.Modules.baseSectionsPushforwardTopIso πT MT).hom
          (eProjective ((1 : A) ⊗ₜ[B] s))) = _
    rw [Scheme.Modules.baseSectionsPushforwardTopIso_hom_apply]
    rfl
  have hOne (s : Scheme.Modules.baseSections π M) :
      (φTop.comp eSource.toLinearMap) ((1 : A) ⊗ₜ[B] s) =
        eTarget ((1 : A) ⊗ₜ[B] s) := by
    rw [LinearMap.comp_apply]
    change φTop (eSource ((1 : A) ⊗ₜ[B] s)) =
      eTarget ((1 : A) ⊗ₜ[B] s)
    rw [hSource, hTarget]
    exact h.sectionPoleSheafPowerPushforwardBaseChange_projectiveClosed_app_top_one_tmul
      f hsm z hz hn t s
  have hcomp : φTop.comp eSource.toLinearMap = eTarget.toLinearMap := by
    ext q
    induction q using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a s =>
        rw [show a ⊗ₜ[B] s = a • ((1 : A) ⊗ₜ[B] s) by
          rw [TensorProduct.smul_tmul']
          simp]
        simp only [map_smul]
        exact congrArg (fun y => a • y) (hOne s)
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective φTop
  apply (Function.Bijective.of_comp_iff φTop eSource.bijective).mp
  have hfun : φTop ∘ eSource = eTarget := by
    funext q
    exact LinearMap.congr_fun hcomp q
  rw [hfun]
  exact eTarget.bijective

/-- The canonical pole-sheaf pushforward base-change morphism is an
isomorphism for every affine base change of a projectively presented
fibrewise elliptic family. -/
theorem
    FibrewiseElliptic.sectionPoleSheafPowerPushforwardBaseChange_projectiveClosed_isIso
    {R : Type u} {σ : Type} [CommRing R]
    [Fintype σ] [LinearOrder σ] [Nontrivial σ] [IsNoetherianRing R]
    {E : Scheme.{u}}
    (f : E ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    [IsClosedImmersion f]
    (hsm : SmoothOfRelativeDimension 1
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)))
    (z : Spec (.of R) ⟶ E)
    (hz : z ≫ (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) =
      𝟙 (Spec (.of R)))
    (h : FibrewiseElliptic
      (f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) z hz)
    {n : ℕ} (hn : 1 ≤ n) {T : Scheme.{u}} [IsAffine T]
    (t : T ⟶ Spec (.of R)) :
    let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
    IsIso (sectionPoleSheafPowerPushforwardBaseChange
      (π := π) hsm z hz t n) := by
  dsimp only
  let π := f ≫ MvPolynomial.homogeneousProjπ (R := R) (σ := σ)
  let M := sectionPoleSheafPower π z hz n
  let N := (Scheme.Modules.pushforward π).obj M
  let πT := pullback.snd π t
  let zT := sectionBaseChange z hz t
  let hzT := sectionBaseChange_snd z hz t
  let MT := sectionPoleSheafPower πT zT hzT n
  let NT := (Scheme.Modules.pushforward πT).obj MT
  let φ := sectionPoleSheafPowerPushforwardBaseChange hsm z hz t n
  letI : E.IsSeparated := ⟨by
    rw [← terminal.comp_from π]
    infer_instance⟩
  letI : N.IsQuasicoherent :=
    h.sectionPoleSheafPowerPushforward_projectiveClosed_isQuasicoherent
      f hsm z hz hn
  letI : ((Scheme.Modules.pullback t).obj N).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback_of_isAffine t N
  letI : NT.IsQuasicoherent :=
    FibrewiseElliptic.sectionPoleSheafPowerPushforward_baseChange_projectiveClosed_isQuasicoherent
      f hsm z hz n t
  exact Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top φ
    (h.sectionPoleSheafPowerPushforwardBaseChange_projectiveClosed_app_top_isIso
      f hsm z hz hn t)

end ModularCurves
