/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.PullbackUnitMonoidal
import ModularCurves.Picard.DualPullback.OverRestriction
import ModularCurves.Picard.DualPullback.RestrictComp
import ModularCurves.Picard.DualPullback.UnitComp
import ModularCurves.Picard.DualPullback.UnitSquare

/-!
# Restricting local trivializations

This file proves coherence for restricting module trivializations through nested opens.
It compares the direct restriction-functor construction with the pullback construction,
and identifies both with restriction on the over-site. It also records compatibility with
sheaf duals.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u u₁ v₁

namespace ModularCurves.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

private theorem restrictOverTrivialization_comp_inv_app_apply
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    (restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z).inv.val.app T x =
      e.inv.val.app
        (.op ((Over.map V.hom).obj ((Over.map Z.hom).obj T.unop))) x := by
  rw [restrictOverTrivialization_inv_app_apply]
  erw [restrictOverTrivialization_inv_app_apply]

private theorem restrictOverTrivialization_direct_inv_app_apply
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    (restrictOverTrivialization R M U e
        ((Over.map V.hom).obj Z)).inv.val.app T x =
      e.inv.val.app
        (.op ((Over.map ((Over.map V.hom).obj Z).hom).obj T.unop)) x := by
  erw [restrictOverTrivialization_inv_app_apply]

private theorem trivialization_inv_overMap_assoc
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    e.inv.val.app
        (.op ((Over.map V.hom).obj ((Over.map Z.hom).obj T.unop))) x =
      e.inv.val.app
        (.op ((Over.map ((Over.map V.hom).obj Z).hom).obj T.unop)) x := by
  let A := (Over.map V.hom).obj ((Over.map Z.hom).obj T.unop)
  let B := (Over.map ((Over.map V.hom).obj Z).hom).obj T.unop
  let k : A ⟶ B := Over.homMk (𝟙 T.unop.left) (by
    dsimp only [A, B]
    simp only [Over.map_obj_left, Over.map_obj_hom]
    rw [Category.id_comp]
    exact (Category.assoc T.unop.hom Z.hom V.hom).symm)
  have hnat := PresheafOfModules.naturality_apply e.inv.val k.op x
  change e.inv.val.app (.op A) ((R.over U).obj.map k.op x) =
    (M.over U).val.map k.op (e.inv.val.app (.op B) x) at hnat
  have hk : k.left = 𝟙 T.unop.left := rfl
  change e.inv.val.app (.op A) (R.obj.map k.left.op x) =
    M.val.map k.left.op (e.inv.val.app (.op B) x) at hnat
  have hRmap : R.obj.map k.left.op x = x := by
    rw [hk]
    change R.obj.map (𝟙 (.op T.unop.left)) x = x
    rw [R.obj.map_id]
    rfl
  have hMmap : M.val.map k.left.op (e.inv.val.app (.op B) x) =
      e.inv.val.app (.op B) x := by
    rw [hk]
    change M.val.map (𝟙 (.op T.unop.left)) (e.inv.val.app (.op B) x) = _
    rw [M.val.map_id]
    rfl
  rw [hRmap, hMmap] at hnat
  simpa only [A, B] using hnat

private theorem restrictOverTrivialization_comp_inv_eq
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) (T : (Over Z.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over Z.left)).val.obj T) :
    (restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z).inv.val.app T x =
      (restrictOverTrivialization R M U e
        ((Over.map V.hom).obj Z)).inv.val.app T x := by
  rw [restrictOverTrivialization_comp_inv_app_apply]
  rw [trivialization_inv_overMap_assoc]
  exact (restrictOverTrivialization_direct_inv_app_apply
    R M U e V Z T x).symm

theorem restrictOverTrivialization_comp
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) (Z : Over V.left) :
    restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z =
      restrictOverTrivialization R M U e ((Over.map V.hom).obj Z) := by
  apply Iso.ext
  rw [← Iso.inv_eq_inv]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact restrictOverTrivialization_comp_inv_eq R M U e V Z T x

theorem restrictOverTrivialization_dualOverIsoOfIso
    [∀ U, IsMulCommutative (R.obj.obj U)]
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (V : Over U) :
    restrictOverTrivialization R (dual R M) U
        (dualOverIsoOfIso R M U e) V =
      dualOverIsoOfIso R M V.left
        (restrictOverTrivialization R M U e V) := by
  apply Iso.ext
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro alpha
  change dualTrivializationLinearEquiv R M Z.unop.left
      (restrictOverTrivialization R M U e
        ((Over.map V.hom).obj Z.unop)) alpha =
    dualTrivializationLinearEquiv R M Z.unop.left
      (restrictOverTrivialization R M V.left
        (restrictOverTrivialization R M U e V) Z.unop) alpha
  rw [restrictOverTrivialization_comp R M U e V Z.unop]

end ModularCurves.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem cancel_iso_inv_right
    {D : Type u₁} [Category.{v₁} D]
    {A B C : D} (e : A ≅ B) (p : C ⟶ B) (q : C ⟶ A)
    (h : p ≫ e.inv = q) : p = q ≫ e.hom :=
  e.comp_inv_eq.mp h

noncomputable def restrictOpenTrivialization
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    M.restrict V.ι ≅ unitObj V.toScheme :=
  (restrictOpenCompIso (homOfLE hVU)).app M ≪≫
    (restrictFunctor (X.homOfLE hVU)).mapIso e ≪≫
    restrictUnitIso (X.homOfLE hVU)

noncomputable def restrictOpenTrivializationPullback
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    M.restrict V.ι ≅ unitObj V.toScheme :=
  (restrictFunctorIsoPullback V.ι).app M ≪≫
    restrictTrivialization hVU
      ((restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e)

theorem restrictFunctorIsoPullback_comp_inv_cancel
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : C.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫
        (pullbackComp f g).inv.app M ≫
        (pullback f).map ((restrictFunctorIsoPullback g).inv.app M) =
      (restrictFunctorComp f g).hom.app M ≫
        (restrictFunctorIsoPullback f).hom.app
          ((restrictFunctor g).obj M) := by
  let eP := (pullbackComp f g).app M
  let eG := (pullback f).mapIso ((restrictFunctorIsoPullback g).app M)
  let eF := (restrictFunctorIsoPullback f).app ((restrictFunctor g).obj M)
  let eC := (restrictFunctorIsoPullback (f ≫ g)).app M
  let eR := (restrictFunctorComp f g).app M
  have hci := restrictFunctorIsoPullback_comp_inv f g M
  change eP.inv ≫ eG.inv ≫ eF.inv = eC.inv ≫ eR.hom at hci
  have hci' : (eP.inv ≫ eG.inv) ≫ eF.inv = eC.inv ≫ eR.hom :=
    (Category.assoc eP.inv eG.inv eF.inv).trans hci
  have hPG : eP.inv ≫ eG.inv = eC.inv ≫ eR.hom ≫ eF.hom :=
    cancel_iso_inv_right eF (eP.inv ≫ eG.inv)
      (eC.inv ≫ eR.hom) hci'
  change eC.hom ≫ eP.inv ≫ eG.inv = eR.hom ≫ eF.hom
  calc
    eC.hom ≫ eP.inv ≫ eG.inv =
        eC.hom ≫ (eP.inv ≫ eG.inv) := Category.assoc _ _ _
    _ = eC.hom ≫ (eC.inv ≫ eR.hom ≫ eF.hom) :=
      congrArg (fun q => eC.hom ≫ q) hPG
    _ = eR.hom ≫ eF.hom := eC.hom_inv_id_assoc _

theorem restrictOpenTrivialization_hom_eq_pullback
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    (restrictOpenTrivialization hVU e).hom =
      (restrictOpenTrivializationPullback hVU e).hom := by
  simp only [restrictOpenTrivialization,
    restrictOpenTrivializationPullback, restrictTrivialization,
    restrictOpenCompIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  let j := X.homOfLE hVU
  let hcomp := X.homOfLE_ι hVU
  have hc := restrictFunctorIsoPullback_congr hcomp.symm M
  have hcore := restrictFunctorIsoPullback_comp_inv_cancel j U.ι M
  have hnat := (restrictFunctorIsoPullback j).hom.naturality e.hom
  dsimp only [j] at hc hcore hnat
  rw [Functor.map_comp]
  let a := (restrictFunctorCongr hcomp.symm).hom.app M
  let b := (restrictFunctorComp (X.homOfLE hVU) U.ι).hom.app M
  let c := (restrictFunctor (X.homOfLE hVU)).map e.hom
  let d := (restrictUnitIso (X.homOfLE hVU)).hom
  let A := (restrictFunctorIsoPullback V.ι).hom.app M
  let P := (pullbackCongr hcomp.symm).hom.app M
  let Q := (pullbackComp (X.homOfLE hVU) U.ι).inv.app M
  let T := (pullback (X.homOfLE hVU)).map
    ((restrictFunctorIsoPullback U.ι).inv.app M)
  let s := (pullback (X.homOfLE hVU)).map e.hom
  let t := (pullbackUnitIso (X.homOfLE hVU)).hom
  let E := (restrictFunctorIsoPullback (X.homOfLE hVU ≫ U.ι)).hom.app M
  let J := (restrictFunctorIsoPullback (X.homOfLE hVU)).hom.app
    ((restrictFunctor U.ι).obj M)
  let JO := (restrictFunctorIsoPullback (X.homOfLE hVU)).hom.app
    (unitObj U.toScheme)
  change a ≫ b ≫ c ≫ d = A ≫ P ≫ Q ≫ T ≫ s ≫ t
  change a ≫ E = A ≫ P at hc
  change E ≫ Q ≫ T = b ≫ J at hcore
  change c ≫ JO = J ≫ s at hnat
  have hprefix : A ≫ P ≫ Q ≫ T = a ≫ b ≫ J := by
    calc
      A ≫ P ≫ Q ≫ T = (A ≫ P) ≫ (Q ≫ T) := by
        simp only [Category.assoc]
      _ = (a ≫ E) ≫ (Q ≫ T) :=
        congrArg (fun k => k ≫ (Q ≫ T)) hc.symm
      _ = a ≫ (E ≫ Q ≫ T) := by simp only [Category.assoc]
      _ = a ≫ (b ≫ J) := congrArg (fun k => a ≫ k) hcore
      _ = a ≫ b ≫ J := rfl
  have hunit : JO ≫ t = d :=
    restrictFunctorIsoPullback_hom_comp_pullbackUnitIsoG
      (X.homOfLE hVU)
  symm
  calc
    A ≫ P ≫ Q ≫ T ≫ s ≫ t = (A ≫ P ≫ Q ≫ T) ≫ (s ≫ t) := by
      simp only [Category.assoc]
    _ = (a ≫ b ≫ J) ≫ (s ≫ t) :=
      congrArg (fun k => k ≫ (s ≫ t)) hprefix
    _ = a ≫ b ≫ (J ≫ s) ≫ t := by simp only [Category.assoc]
    _ = a ≫ b ≫ (c ≫ JO) ≫ t :=
      congrArg (fun k => a ≫ b ≫ k ≫ t) hnat.symm
    _ = a ≫ b ≫ c ≫ (JO ≫ t) := by simp only [Category.assoc]
    _ = a ≫ b ≫ c ≫ d := congrArg (fun k => a ≫ b ≫ c ≫ k) hunit

theorem restrictOpenTrivialization_eq_pullback
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    restrictOpenTrivialization hVU e =
      restrictOpenTrivializationPullback hVU e := by
  apply Iso.ext
  exact restrictOpenTrivialization_hom_eq_pullback hVU e

theorem overTrivializationOfRestrictOpenTrivialization
    {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    overTrivializationOfRestrictIso M V
        (restrictOpenTrivialization hVU e) =
      ModularCurves.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U (overTrivializationOfRestrictIso M U e)
          (Over.mk (homOfLE hVU)) := by
  apply Iso.ext
  let G := (overEquiv V).functor
  apply G.map_injective
  simp only [overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom]
  let i : V ⟶ U := homOfLE hVU
  have hres := overEquiv_map_dualRestrict M i
    (overTrivializationOfRestrictIso M U e).hom
  change _ = G.map (ModularCurves.SheafOfModules.dualRestrict
    X.ringCatSheaf M i.op (overTrivializationOfRestrictIso M U e).hom)
  rw [hres]
  simp only [overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Functor.map_comp,
    Iso.trans_hom, restrictOpenTrivialization, Category.assoc]
  slice_rhs 1 2 => erw [overRestrictModuleIso_comp_overFunctorEquiv]
  rw [overRestrictUnitIso_eq_restrictUnitIsoP]
  rfl

end AlgebraicGeometry.Scheme.Modules
