import ModularCurves.EllipticCurve.PoleSheaf
import ModularCurves.Picard.DualPullback.UnitNaturality

/-!
# Base change for the canonical pole-unit section

The canonical inclusion of the structure sheaf into the simple-pole sheaf is preserved by
arbitrary base change. This identifies the first member of every compatible pole basis with the
literal constant section `1`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

private theorem inverse_baseChange_squareT (f : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules}
    (q : M ⟶ unitObj X) (q' : N ⟶ unitObj Y)
    (e : (pullback f).obj M ≅ N)
    (h : e.hom ≫ q' = (pullback f).map q ≫ (pullbackUnitIso f).hom) :
    e.inv ≫ (pullback f).map q = q' ≫ (pullbackUnitIso f).inv := by
  apply (cancel_epi e.hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  rw [h]
  simp

private theorem dualMapObj_compT {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    dualMapObj (f ≫ g) = dualMapObj g ≫ dualMapObj f :=
  ModularCurves.SheafOfModules.dualMap_comp X.ringCatSheaf f g

private theorem dualMapObj_baseChange_squareT (f : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules}
    (q : M ⟶ unitObj X) (q' : N ⟶ unitObj Y)
    (e : (pullback f).obj M ≅ N)
    (h : e.hom ≫ q' = (pullback f).map q ≫ (pullbackUnitIso f).hom) :
    dualMapObj ((pullback f).map q) ≫ dualMapObj e.inv =
      dualMapObj (pullbackUnitIso f).inv ≫ dualMapObj q' := by
  rw [← dualMapObj_compT e.inv ((pullback f).map q)]
  rw [← dualMapObj_compT q' (pullbackUnitIso f).inv]
  rw [inverse_baseChange_squareT f q q' e h]

private theorem dualPoleUnitHom_baseChangeT (f : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules}
    (hM : IsInvertible M)
    (q : M ⟶ unitObj X) (q' : N ⟶ unitObj Y)
    (e : (pullback f).obj M ≅ N)
    (h : e.hom ≫ q' = (pullback f).map q ≫ (pullbackUnitIso f).hom) :
    (pullback f).map
          ((dualUnitObjIso (X := X)).inv ≫ dualMapObj q) ≫
        (dualPullbackIsoOfIsInvertible f M hM ≪≫
          (dualIsoObj e).symm).hom =
      (pullbackUnitIso f).hom ≫
        (dualUnitObjIso (X := Y)).inv ≫ dualMapObj q' := by
  rw [Functor.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom]
  change (pullback f).map (dualUnitObjIso (X := X)).inv ≫
      (pullback f).map (dualMapObj q) ≫ dualPullbackHom f M ≫
        dualMapObj e.inv =
    (pullbackUnitIso f).hom ≫
      (dualUnitObjIso (X := Y)).inv ≫ dualMapObj q'
  calc
    _ = (pullback f).map (dualUnitObjIso (X := X)).inv ≫
        ((pullback f).map (dualMapObj q) ≫ dualPullbackHom f M) ≫
          dualMapObj e.inv := by simp only [Category.assoc]
    _ = (pullback f).map (dualUnitObjIso (X := X)).inv ≫
        (dualPullbackHom f (unitObj X) ≫
          dualMapObj ((pullback f).map q)) ≫ dualMapObj e.inv := by
      rw [dualPullbackHom_naturality]
    _ = (pullback f).map (dualUnitObjIso (X := X)).inv ≫
        dualPullbackHom f (unitObj X) ≫
          (dualMapObj ((pullback f).map q) ≫ dualMapObj e.inv) := by
      simp only [Category.assoc]
    _ = (pullback f).map (dualUnitObjIso (X := X)).inv ≫
        dualPullbackHom f (unitObj X) ≫
          (dualMapObj (pullbackUnitIso f).inv ≫ dualMapObj q') := by
      rw [dualMapObj_baseChange_squareT f q q' e h]
    _ = ((pullback f).map (dualUnitObjIso (X := X)).inv ≫
        dualPullbackHom f (unitObj X) ≫
          dualMapObj (pullbackUnitIso f).inv) ≫ dualMapObj q' := by
      simp only [Category.assoc]
    _ = ((pullbackUnitIso f).hom ≫
        (dualUnitObjIso (X := Y)).inv) ≫ dualMapObj q' := by
      rw [dualPullbackHom_unit_naturality]
    _ = _ := by simp only [Category.assoc]


end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

theorem sectionPoleUnitHom_baseChange
    {C S T : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (t : T ⟶ S) :
    (Scheme.Modules.pullback (pullback.fst π t)).map
          (sectionPoleUnitHom π z hz) ≫
        (sectionPoleSheafBaseChangeIso hsm z hz t).hom =
      (Scheme.Modules.pullbackUnitIso (pullback.fst π t)).hom ≫
        sectionPoleUnitHom (pullback.snd π t)
          (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t) := by
  let g := pullback.fst π t
  let M := sectionIdealModule π z hz
  let N := sectionIdealModule (pullback.snd π t)
    (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t)
  let q := sectionIdealToUnit π z hz
  let q' := sectionIdealToUnit (pullback.snd π t)
    (sectionBaseChange z hz t) (sectionBaseChange_snd z hz t)
  let e := sectionIdealModuleBaseChangeIso hsm z hz t
  letI : IsSeparated (pullback.snd π t) := inferInstance
  have hSquare : e.hom ≫ q' =
      (Scheme.Modules.pullback g).map q ≫
        (Scheme.Modules.pullbackUnitIso g).hom := by
    dsimp only [e, q, q', M, N, g, sectionIdealToUnit,
      sectionIdealModuleBaseChangeIso, Scheme.Modules.pullbackUnitIso]
    exact idealModuleBaseChangeHom_comp_toUnit z hz t
  change (Scheme.Modules.pullback g).map
        ((Scheme.Modules.dualUnitObjIso (X := C)).inv ≫
          Scheme.Modules.dualMapObj q) ≫
      (Scheme.Modules.dualPullbackIsoOfIsInvertible g M
          (sectionIdealModule_isInvertible hsm z hz) ≪≫
        (Scheme.Modules.dualIsoObj e).symm).hom =
    (Scheme.Modules.pullbackUnitIso g).hom ≫
      (Scheme.Modules.dualUnitObjIso
        (X := pullback π t)).inv ≫ Scheme.Modules.dualMapObj q'
  exact Scheme.Modules.dualPoleUnitHom_baseChangeT g
    (sectionIdealModule_isInvertible hsm z hz) q q' e hSquare

end ModularCurves
