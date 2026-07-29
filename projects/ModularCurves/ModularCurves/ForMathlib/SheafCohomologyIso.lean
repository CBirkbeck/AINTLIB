import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Sites.Equivalence
import ModularCurves.ForMathlib.FlasqueCohomology
import ModularCurves.ForMathlib.TopCatSheafRestrict

/-!
# Sheaf cohomology under homeomorphisms

This file proves that the genuine `Sheaf.H` groups are transported by a
homeomorphism. The proof compares constant sheaves and maps Ext through the
induced equivalence of additive sheaf categories.
-/

open CategoryTheory Limits TopologicalSpace

universe u v

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

private noncomputable def congrIso {X X' Y Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃ Ext X' Y' n where
  toFun a := (mk₀ eX.inv).comp (a.comp (mk₀ eY.hom) (add_zero n)) (zero_add n)
  invFun a := (mk₀ eX.hom).comp (a.comp (mk₀ eY.inv) (add_zero n)) (zero_add n)
  left_inv a := by
    dsimp
    rw [comp_assoc_of_third_deg_zero, comp_assoc_of_second_deg_zero,
      mk₀_comp_mk₀, eY.hom_inv_id, comp_mk₀_id,
      mk₀_comp_mk₀_assoc, eX.hom_inv_id, mk₀_id_comp]
  right_inv a := by
    dsimp
    rw [comp_assoc_of_third_deg_zero, comp_assoc_of_second_deg_zero,
      mk₀_comp_mk₀, eY.inv_hom_id, comp_mk₀_id,
      mk₀_comp_mk₀_assoc, eX.inv_hom_id, mk₀_id_comp]

end CategoryTheory.Abelian.Ext

namespace TopCat.Sheaf

private lemma opensMap_hom_isCocontinuous {X Y : TopCat.{u}} (e : X ≅ Y) :
    (Opens.map e.hom).IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := by
  change (Opens.mapMapIso e).functor.IsCocontinuous
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  exact (Adjunction.isCocontinuous_iff_coverPreserving _ _
    (Opens.mapMapIso e).toAdjunction).2 (coverPreserving_opens_map e.inv)

private lemma opensMap_inv_isCocontinuous {X Y : TopCat.{u}} (e : X ≅ Y) :
    (Opens.map e.inv).IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
  change (Opens.mapMapIso e).inverse.IsCocontinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  exact (Adjunction.isCocontinuous_iff_coverPreserving _ _
    (Opens.mapMapIso e).symm.toAdjunction).2 (coverPreserving_opens_map e.hom)

private noncomputable def equivOfIso {X Y : TopCat.{u}} (e : X ≅ Y) :
    X.Sheaf AddCommGrpCat.{u} ≌ Y.Sheaf AddCommGrpCat.{u} := by
  let eO := Opens.mapMapIso e
  letI : eO.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := opensMap_hom_isCocontinuous e
  letI : eO.inverse.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := opensMap_inv_isCocontinuous e
  letI : eO.symm.functor.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
    change eO.inverse.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)
    infer_instance
  letI : eO.symm.inverse.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := by
    change eO.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
    infer_instance
  letI : eO.symm.functor.IsDenseSubsite (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    CategoryTheory.Equivalence.isDenseSubsite_functor_of_isCocontinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) eO.symm
  exact CategoryTheory.Functor.IsDenseSubsite.sheafEquiv
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      eO.symm.functor AddCommGrpCat

private noncomputable def equivOfIsoConstant {X Y : TopCat.{u}} (e : X ≅ Y)
    (A : AddCommGrpCat.{u}) :
    (equivOfIso e).functor.obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj A) ≅
      (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj A := by
  let eO := Opens.mapMapIso e
  letI : eO.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := opensMap_hom_isCocontinuous e
  letI : eO.inverse.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := opensMap_inv_isCocontinuous e
  letI : eO.symm.functor.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
    change eO.inverse.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)
    infer_instance
  letI : eO.symm.inverse.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := by
    change eO.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
    infer_instance
  letI : eO.symm.functor.IsDenseSubsite (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    CategoryTheory.Equivalence.isDenseSubsite_functor_of_isCocontinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) eO.symm
  have htop : IsTerminal (eO.symm.functor.obj (⊤ : Opens X)) := by
    rw [show eO.symm.functor.obj (⊤ : Opens X) = (⊤ : Opens Y) by
      change (Opens.map e.inv).obj ⊤ = ⊤
      exact Opens.map_top e.inv]
    exact isTerminalTop
  exact (equivCommuteConstant (Opens.grothendieckTopology X) AddCommGrpCat
    (Opens.grothendieckTopology Y) eO.symm.functor isTerminalTop htop).app A

private noncomputable def equivOfIsoIsoPushforward {X Y : TopCat.{u}} (e : X ≅ Y) :
    (equivOfIso e).functor ≅ pushforward AddCommGrpCat e.hom := by
  let eO := Opens.mapMapIso e
  letI : eO.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := opensMap_hom_isCocontinuous e
  letI : eO.inverse.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := opensMap_inv_isCocontinuous e
  letI : eO.symm.functor.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) := by
    change eO.inverse.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)
    infer_instance
  letI : eO.symm.inverse.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := by
    change eO.functor.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
    infer_instance
  letI : eO.symm.functor.IsDenseSubsite (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    CategoryTheory.Equivalence.isDenseSubsite_functor_of_isCocontinuous
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) eO.symm
  letI : eO.symm.inverse.IsDenseSubsite (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) := by
    change eO.functor.IsDenseSubsite (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)
    exact CategoryTheory.Equivalence.isDenseSubsite_functor_of_isCocontinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) eO
  exact (equivOfIso e).toAdjunction.leftAdjointUniq
    (eO.symm.sheafCongr (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) AddCommGrpCat).toAdjunction

/-- Cohomology of additive sheaves is invariant under a homeomorphism. -/
theorem subsingleton_H_of_iso {X Y : TopCat.{u}} (e : X ≅ Y)
    {F : X.Sheaf AddCommGrpCat.{u}} {G : Y.Sheaf AddCommGrpCat.{u}}
    (hFG : (pushforward AddCommGrpCat e.hom).obj F ≅ G) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H F n)] :
    Subsingleton (CategoryTheory.Sheaf.H G n) := by
  letI : HasExt.{u} (X.Sheaf AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  letI : HasExt.{u} (Y.Sheaf AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  let E := equivOfIso e
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : E.functor.Additive :=
    Functor.additive_of_iso (equivOfIsoIsoPushforward e).symm
  let cX := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  let cY := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  letI : AddCommGroup (CategoryTheory.Abelian.Ext cX F n) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  letI : AddCommGroup (CategoryTheory.Abelian.Ext
      (E.functor.obj cX) (E.functor.obj F) n) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  let mapExt : CategoryTheory.Abelian.Ext cX F n ≃+
      CategoryTheory.Abelian.Ext (E.functor.obj cX) (E.functor.obj F) n :=
    AddEquiv.ofBijective (E.functor.mapExtAddHom cX F n)
      (E.functor.mapExt_bijective_of_preservesInjectiveObjects cX F n)
  let hExt := mapExt.toEquiv.trans (CategoryTheory.Abelian.Ext.congrIso
    (X := E.functor.obj cX) (X' := cY) (Y := E.functor.obj F) (Y' := G)
    (equivOfIsoConstant e (AddCommGrpCat.of (ULift ℤ)))
    ((equivOfIsoIsoPushforward e).app F ≪≫ hFG) n)
  exact ⟨fun x y ↦ hExt.symm.injective (Subsingleton.elim _ _)⟩

end TopCat.Sheaf
