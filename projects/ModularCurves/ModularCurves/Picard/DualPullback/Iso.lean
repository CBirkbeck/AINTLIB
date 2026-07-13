import ModularCurves.Picard.DualPullback.LocalTrivializationInv

/-!
# Pullback of dual invertible modules

The canonical map from the pullback of a dual to the dual of the pullback is an
isomorphism for every cover-locally invertible module.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem dualPullbackHom_over_isIso_of_trivialT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsIso ((dualPullbackHomD f M).over (f ⁻¹ᵁ U)) := by
  let V := f ⁻¹ᵁ U
  let d := ModularCurves.SheafOfModules.dualOverIsoOfIso
    X.ringCatSheaf M U e
  let pS := localPullbackTrivializationT f (dualObj M) U d
  let eY := localPullbackTrivializationT f M U e
  let pT := ModularCurves.SheafOfModules.dualOverIsoOfIso
    Y.ringCatSheaf ((pullback f).obj M) V eY
  let m := (dualPullbackHomD f M).over V
  let T : Over V := Over.mk (𝟙 V)
  let oneV : (Y.ringCatSheaf.over V).obj.obj (.op T) := 1
  let xg := ((pullbackPushforwardAdjunction f).unit.app
    (dualObj M)).val.app (.op U) e.hom
  have hd := dualOverIsoOfIso_hom_terminal_apply_trivializationT M U e
  have hpS : (overEquiv V).functor.map pS.hom =
      (localPullbackModuleIso f (dualObj M) U).inv ≫
        (pullback (f ∣_ U)).map
          ((overEquiv U).functor.map d.hom) ≫
        (localPullbackUnitIso f U).hom := by
    dsimp only [pS, localPullbackTrivializationT]
    simp only [Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage, Iso.trans_hom,
      Functor.mapIso_hom]
    rfl
  have hsInv := localPullbackTrivialization_inv_one_coreT
    f M U e d pS hd hpS
  have hm := dualPullbackHom_unit_appT f M U e.hom
  change m.val.app (.op T) xg = localDualPullback f M U e.hom at hm
  have hlocal := localDualPullback_trivialization_homT f M U e
  have ht := dualOverIsoOfIso_hom_terminal_apply_trivializationT
    ((pullback f).obj M) V eY
  have hmx : m.val.app (.op T) xg = eY.hom := by
    rw [hm, hlocal]
  exact isIso_of_local_trivializations_terminal_oneT (Y := Y) V
    (A := ((pullback f).obj (dualObj M)).over V)
    (B := (dualObj ((pullback f).obj M)).over V)
    pS pT m xg eY.hom hsInv hmx ht

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite



namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

theorem dualPullbackHom_restrict_isIso_of_trivialT (f : Y ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅
      _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    IsIso ((restrictFunctor (f ⁻¹ᵁ U).ι).map
      (dualPullbackHomD f M)) := by
  let V := f ⁻¹ᵁ U
  let q := dualPullbackHomD f M
  let m := q.over V
  let a := (overEquiv V).functor.map m
  let eA := (overFunctorEquiv V).app ((pullback f).obj (dualObj M))
  let eB := (overFunctorEquiv V).app (dualObj ((pullback f).obj M))
  let d := (restrictFunctor V.ι).map q
  letI hm : IsIso m := dualPullbackHom_over_isIso_of_trivialT f M U e
  letI ha : IsIso a := by
    dsimp only [a]
    infer_instance
  letI heA : IsIso eA.hom := by
    dsimp only [eA]
    infer_instance
  letI heB : IsIso eB.hom := by
    dsimp only [eB]
    infer_instance
  have hnat : a ≫ eB.hom = eA.hom ≫ d :=
    (overFunctorEquiv V).hom.naturality q
  haveI hcomp : IsIso (eA.hom ≫ d) := by
    rw [← hnat]
    exact IsIso.comp_isIso' ha heB
  exact (isIso_comp_left_iff eA.hom d).mp hcomp

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

/-- A module morphism which is an isomorphism after restriction to an open
neighborhood induces an isomorphism on the corresponding ambient stalk. -/
theorem isIso_stalkFunctor_map_of_isIso_restrict_opensT
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (x : U)
    [IsIso ((restrictFunctor U.ι).map f)] :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x.1).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) := by
  let eStalk := restrictStalkNatIso U.ι x
  apply (NatIso.isIso_map_iff eStalk f).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor.{u, u + 1}
      AddCommGrpCat.{u} _).map
    ((toPresheaf.{u} _).map ((restrictFunctor U.ι).map f)))
  infer_instance

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- A pullback trivialization on an open subscheme, expressed on its over-site. -/
noncomputable def overTrivializationOfPullbackIsoT (M : X.Modules) (U : X.Opens)
    (e : (pullback U.ι).obj M ≅ unitObj U.toScheme) :
    M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U) :=
  overTrivializationOfRestrictIso M U
    ((restrictFunctorIsoPullback U.ι).app M ≪≫ e)

/-- Pullback commutes with the dual of an invertible module on every stalk. -/
theorem dualPullbackHom_stalk_isIso_of_isInvertibleT
    (f : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M) (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        (dualPullbackHomD f M)).hom) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  have hy : f y ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  obtain ⟨i, hyi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  obtain ⟨e⟩ := htriv i
  let eOver := overTrivializationOfPullbackIsoT M (U i) e
  letI : IsIso ((restrictFunctor (f ⁻¹ᵁ U i).ι).map
      (dualPullbackHomD f M)) :=
    dualPullbackHom_restrict_isIso_of_trivialT f M (U i) eOver
  let yi : f ⁻¹ᵁ U i := ⟨y, hyi⟩
  exact isIso_stalkFunctor_map_of_isIso_restrict_opensT
    (dualPullbackHomD f M) (f ⁻¹ᵁ U i) yi

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory Opposite


namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- Pullback commutes with the sheaf dual of an invertible module. -/
theorem dualPullbackHomD_isIso_of_isInvertibleT
    (f : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M) :
    IsIso (dualPullbackHomD f M) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  letI hreflect : F.ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  haveI hstalk : ∀ y : Y,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (F.map (dualPullbackHomD f M)).hom) := by
    intro y
    exact dualPullbackHom_stalk_isIso_of_isInvertibleT f M hM y
  haveI hmap : IsIso (F.map (dualPullbackHomD f M)) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      (F.map (dualPullbackHomD f M))
  exact @Functor.ReflectsIsomorphisms.reflects _ _ _ _ F hreflect _ _
    (dualPullbackHomD f M) hmap

/-- The canonical pullback comparison for the dual of an invertible module. -/
noncomputable def dualPullbackIsoOfIsInvertibleT
    (f : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M) :
    (pullback f).obj (dualObj M) ≅ dualObj ((pullback f).obj M) := by
  letI := dualPullbackHomD_isIso_of_isInvertibleT f M hM
  exact asIso (dualPullbackHomD f M)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- The canonical comparison from the pullback of a module dual to the dual of its
pullback. -/
noncomputable def dualPullbackHom (f : Y ⟶ X) (M : X.Modules) :
    (pullback f).obj (dualObj M) ⟶ dualObj ((pullback f).obj M) :=
  dualPullbackHomD f M

/-- The canonical dual-pullback comparison is natural in the module. -/
theorem dualPullbackHom_naturality (f : Y ⟶ X)
    {M N : X.Modules} (q : M ⟶ N) :
    (pullback f).map (dualMapObj q) ≫ dualPullbackHom f M =
      dualPullbackHom f N ≫ dualMapObj ((pullback f).map q) :=
  dualPullbackHom_naturalityD f q

/-- Pullback commutes with the sheaf dual of a cover-locally invertible module. -/
theorem dualPullbackHom_isIso_of_isInvertible
    (f : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M) :
    IsIso (dualPullbackHom f M) := by
  change IsIso (dualPullbackHomD f M)
  exact dualPullbackHomD_isIso_of_isInvertibleT f M hM

/-- The canonical pullback isomorphism for the dual of an invertible module. -/
noncomputable def dualPullbackIsoOfIsInvertible
    (f : Y ⟶ X) (M : X.Modules) (hM : IsInvertible M) :
    (pullback f).obj (dualObj M) ≅ dualObj ((pullback f).obj M) := by
  letI := dualPullbackHom_isIso_of_isInvertible f M hM
  exact asIso (dualPullbackHom f M)

end AlgebraicGeometry.Scheme.Modules
