/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.InvertibleSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Duals of invertible sheaves

This file constructs the sheaf dual `Hom_O(M, O)` from module-linear morphisms on
over-sites.  It is used for the pole sheaves `O(n[0])` in the abstract-to-Weierstrass
comparison.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace ModularCurves

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- A section over `U` restricts to a section of the unit module on the over-site of
`U`. -/
noncomputable def overUnitSection (U : C) (r : R.obj.obj (op U)) :
    (SheafOfModules.unit (R.over U)).sections :=
  PresheafOfModules.sectionsMk
    (fun (V : (Over U)ᵒᵖ) => R.obj.map V.unop.hom.op r)
    (fun {V W : (Over U)ᵒᵖ} f => by
      change R.obj.map f.unop.left.op (R.obj.map V.unop.hom.op r) =
        R.obj.map W.unop.hom.op r
      rw [← R.obj.map_comp_apply, ← op_comp, Over.w])

@[simp]
theorem overUnitSection_apply (U : C) (r : R.obj.obj (op U))
    (V : (Over U)ᵒᵖ) :
    (overUnitSection R U r).val V = R.obj.map V.unop.hom.op r :=
  rfl

/-- Sections of the restricted structure sheaf on `Over U` are exactly sections on
`U`, by evaluation at the terminal object `U ⟶ U`. -/
noncomputable def overUnitSectionEquiv (U : C) :
    R.obj.obj (op U) ≃ (SheafOfModules.unit (R.over U)).sections where
  toFun := overUnitSection R U
  invFun s := s.val (op (Over.mk (𝟙 U)))
  left_inv r := by
    change R.obj.map (𝟙 U).op r = r
    rw [op_id, R.obj.map_id]
    rfl
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    change R.obj.map V.unop.hom.op (s.val (op (Over.mk (𝟙 U)))) = s.val V
    have h := s.property (Over.mkIdTerminal.from V.unop).op
    change R.obj.map (Over.mkIdTerminal.from V.unop).left.op
      (s.val (op (Over.mk (𝟙 U)))) = s.val V at h
    rw [Over.mkIdTerminal_from_left] at h
    exact h

/-- Multiplication by a section, as an endomorphism of the unit module on the
corresponding over-site. -/
noncomputable def overUnitScalarEnd (U : C) (r : R.obj.obj (op U)) :
    End (SheafOfModules.unit (R.over U)) :=
  (SheafOfModules.unit (R.over U)).unitHomEquiv.symm (overUnitSection R U r)

@[simp]
theorem overUnitScalarEnd_app_apply (U : C) (r : R.obj.obj (op U))
    (V : (Over U)ᵒᵖ) (x : (R.over U).obj.obj V) :
    (overUnitScalarEnd R U r).val.app V x =
      x * (show (R.over U).obj.obj V from R.obj.map V.unop.hom.op r) := by
  rfl

variable [∀ U, IsMulCommutative (R.obj.obj U)]

set_option backward.isDefEq.respectTransparency false in
/-- The central action of `O(U)` on the unit module over the over-site of `U`. -/
noncomputable def overUnitScalarEndRingHom (U : C) :
    R.obj.obj (op U) →+* End (SheafOfModules.unit (R.over U)) where
  toFun := overUnitScalarEnd R U
  map_one' := by
    apply (SheafOfModules.forget _).map_injective
    ext V
    erw [overUnitScalarEnd_app_apply]
    rw [End.one_def]
    simp
    erw [ModuleCat.hom_id]
    rfl
  map_mul' r s := by
    rw [mul_comm' r s]
    apply (SheafOfModules.forget _).map_injective
    ext V
    repeat' erw [overUnitScalarEnd_app_apply]
    simp
  map_zero' := by
    apply (SheafOfModules.forget _).map_injective
    ext V
    erw [overUnitScalarEnd_app_apply]
    simp
    erw [PresheafOfModules.zero_app, ModuleCat.hom_zero]
    rfl
  map_add' r s := by
    apply (SheafOfModules.forget _).map_injective
    ext V
    repeat' erw [overUnitScalarEnd_app_apply]
    simp
    erw [SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add]
    change _ = (overUnitScalarEnd R U r).val.app V
        (show (R.over U).obj.obj V from 1) +
      (overUnitScalarEnd R U s).val.app V
        (show (R.over U).obj.obj V from 1)
    rw [overUnitScalarEnd_app_apply, overUnitScalarEnd_app_apply, one_mul, one_mul]

/-- The module structure on local linear functionals, induced by postcomposition with
scalar multiplication on the unit module. -/
@[reducible]
noncomputable def dualSectionsModule (M : _root_.SheafOfModules R) (U : C) :
    Module (R.obj.obj (op U))
      (M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) :=
  Module.compHom _ (overUnitScalarEndRingHom R U)

/-- Linear functionals on the restriction of `M` to the over-site of `U`. -/
noncomputable def dualSections (M : _root_.SheafOfModules R) (U : C) :
    ModuleCat (R.obj.obj (op U)) :=
  letI := dualSectionsModule R M U
  ModuleCat.of _ (M.over U ⟶ _root_.SheafOfModules.unit (R.over U))

/-- Restrict a local linear functional along a morphism of the base site. -/
noncomputable def dualRestrict (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    M.over V.unop ⟶ _root_.SheafOfModules.unit (R.over V.unop) :=
  (_root_.SheafOfModules.overFunctorMap R f.unop).inv.app M ≫
    (_root_.SheafOfModules.overMap R f.unop).map α ≫
    (_root_.SheafOfModules.overMapUnitIso f.unop).hom

/-- The additive internal Hom which contains the module-linear dual as a subpresheaf. -/
noncomputable def ambientDual (M : _root_.SheafOfModules R) :=
  CategoryTheory.sheafHom
    ((_root_.SheafOfModules.toSheaf R).obj M)
    ((_root_.SheafOfModules.toSheaf R).obj (_root_.SheafOfModules.unit R))

/-- Forget module-linearity from a local functional. -/
noncomputable def dualToAmbient (M : _root_.SheafOfModules R) (U : C) :
    (M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) →
      (ambientDual R M).obj.obj (op U) :=
  fun α ↦ (_root_.SheafOfModules.toSheaf (R.over U)).map α

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
theorem dualToAmbient_injective (M : _root_.SheafOfModules R) (U : C) :
    Function.Injective (dualToAmbient R M U) :=
  fun _ _ h ↦ (_root_.SheafOfModules.toSheaf (R.over U)).map_injective h

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem ambientDual_map_dualToAmbient (M : _root_.SheafOfModules R)
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    (ambientDual R M).obj.map f (dualToAmbient R M U.unop α) =
      dualToAmbient R M V.unop (dualRestrict R M f α) :=
  rfl

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem dualRestrict_id (M : _root_.SheafOfModules R) (U : Cᵒᵖ)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    dualRestrict R M (𝟙 U) α = α := by
  apply dualToAmbient_injective R M U.unop
  rw [← ambientDual_map_dualToAmbient]
  simp

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
theorem dualRestrict_comp (M : _root_.SheafOfModules R) {U V W : Cᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    dualRestrict R M (f ≫ g) α =
      dualRestrict R M g (dualRestrict R M f α) := by
  apply dualToAmbient_injective R M W.unop
  rw [← ambientDual_map_dualToAmbient, ← ambientDual_map_dualToAmbient,
    ← ambientDual_map_dualToAmbient]
  simp

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem dualRestrict_zero (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V) :
    dualRestrict R M f 0 = 0 := by
  apply (_root_.SheafOfModules.forget _).map_injective
  ext W x
  rfl

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem dualRestrict_add (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (α β : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    dualRestrict R M f (α + β) = dualRestrict R M f α + dualRestrict R M f β := by
  apply (_root_.SheafOfModules.forget _).map_injective
  ext W x
  rfl

@[simp]
theorem dualRestrict_smul (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : R.obj.obj U)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    letI := dualSectionsModule R M U.unop
    letI := dualSectionsModule R M V.unop
    dualRestrict R M f (r • α) = R.obj.map f r • dualRestrict R M f α := by
  letI := dualSectionsModule R M U.unop
  letI := dualSectionsModule R M V.unop
  rw [show r • α = α ≫ overUnitScalarEnd R U.unop r from rfl]
  rw [show R.obj.map f r • dualRestrict R M f α =
    dualRestrict R M f α ≫
      overUnitScalarEnd R V.unop (R.obj.map f r) from rfl]
  apply (_root_.SheafOfModules.forget _).map_injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [dualRestrict, _root_.SheafOfModules.overMapUnitIso,
    _root_.SheafOfModules.overMap, _root_.SheafOfModules.pushforward]
  repeat' erw [overUnitScalarEnd_app_apply]
  congr 1
  change R.obj.map (W.unop.hom ≫ f.unop).op r =
    R.obj.map W.unop.hom.op (R.obj.map f r)
  rw [op_comp, R.obj.map_comp_apply]
  simp

/-- The additive presheaf of local module-linear functionals on `M`. -/
noncomputable def dualPresheafAb (M : _root_.SheafOfModules R) : Cᵒᵖ ⥤ Ab where
  obj U := AddCommGrpCat.of
    (M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop))
  map {U V} f := AddCommGrpCat.ofHom
    { toFun := dualRestrict R M f
      map_zero' := dualRestrict_zero R M f
      map_add' := dualRestrict_add R M f }
  map_id U := by
    apply AddCommGrpCat.ext
    intro α
    exact dualRestrict_id R M U α
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro α
    exact dualRestrict_comp R M f g α

/-- The presheaf of `R`-modules whose sections over `U` are the module morphisms
`M|_U → R|_U`. -/
noncomputable def dualPresheaf (M : _root_.SheafOfModules R) :
    PresheafOfModules R.obj :=
  letI (U : Cᵒᵖ) : Module (R.obj.obj U) ((dualPresheafAb R M).obj U) :=
    dualSectionsModule R M U.unop
  PresheafOfModules.ofPresheaf (dualPresheafAb R M)
    (fun {_ _} f r α ↦ dualRestrict_smul R M f r α)

/-- The module-linear local functionals, viewed as a subpresheaf of the additive
internal Hom. -/
noncomputable def dualSubfunctor (M : _root_.SheafOfModules R) :
    Subfunctor (ambientDual R M).obj where
  obj U := Set.range (dualToAmbient R M U.unop)
  map f _ := by
    rintro ⟨α, rfl⟩
    exact ⟨dualRestrict R M f α, ambientDual_map_dualToAmbient R M f α⟩

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
set_option backward.isDefEq.respectTransparency.types false in
/-- If a section `s` of the additive internal Hom over `U` restricts to module-linear
functionals along a `J`-covering sieve, then `s` is itself module-linear. This is the
linearity-descent step in the sheaf condition for the module-linear dual. -/
private theorem dualSubfunctor_hom_app_smul (M : _root_.SheafOfModules R) {U : Cᵒᵖ}
    (s : (ambientDual R M).obj.obj U)
    (hs : (dualSubfunctor R M).sieveOfSection s ∈ J U.unop)
    (V : (Over U.unop)ᵒᵖ) (r : (R.over U.unop).obj.obj V)
    (m : (M.over U.unop).val.obj V) :
    s.hom.app V (r • m) =
      r • (show (_root_.SheafOfModules.unit (R.over U.unop)).val.obj V from
        s.hom.app V m) := by
  let T : Sieve V.unop :=
    (Sieve.overEquiv V.unop).symm
      (Sieve.pullback (V.unop.hom) ((dualSubfunctor R M).sieveOfSection s))
  have hT : T ∈ (J.over U.unop) V.unop :=
    J.overEquiv_symm_mem_over V.unop _ (J.pullback_stable (V.unop.hom) hs)
  apply (_root_.SheafOfModules.unit (R.over U.unop)).isSheaf.isSeparated
    V.unop T hT
  intro W i hi
  erw [← CategoryTheory.congr_fun (s.hom.naturality i.op) (r • m)]
  change s.hom.app (op W)
      ((M.over U.unop).val.map i.op (r • m)) =
    (_root_.SheafOfModules.unit (R.over U.unop)).val.map i.op
      (r • (show (_root_.SheafOfModules.unit (R.over U.unop)).val.obj V from
        s.hom.app V m))
  rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul]
  erw [← CategoryTheory.congr_fun (s.hom.naturality i.op) m]
  have hi' :
      (Sieve.pullback (V.unop.hom)
        ((dualSubfunctor R M).sieveOfSection s)) i.left :=
    (Sieve.overEquiv_symm_iff _ i).mp hi
  change (ambientDual R M).obj.map (i.left ≫ V.unop.hom).op s ∈
    (dualSubfunctor R M).obj (op W.left) at hi'
  rcases hi' with ⟨β, hβ⟩
  change s.hom.app (op W)
      ((R.over U.unop).obj.map i.op r • (M.over U.unop).val.map i.op m) =
    (R.over U.unop).obj.map i.op r •
      (show (_root_.SheafOfModules.unit (R.over U.unop)).val.obj (op W) from
        s.hom.app (op W) ((M.over U.unop).val.map i.op m))
  rw [Over.w i] at hβ
  have hβ_app := congr_arg
    (fun q => q.hom.app (op (Over.mk (𝟙 W.left)))) hβ
  let r' : (R.over W.left).obj.obj (op (Over.mk (𝟙 W.left))) :=
    (R.over U.unop).obj.map i.op r
  let m' : (M.over W.left).val.obj (op (Over.mk (𝟙 W.left))) :=
    (M.over U.unop).val.map i.op m
  have hβ_smul := CategoryTheory.congr_fun hβ_app (r' • m')
  have hβ_m := CategoryTheory.congr_fun hβ_app m'
  have hleft_smul :
      (dualToAmbient R M W.left β).hom.app (op (Over.mk (𝟙 W.left)))
          (r' • m') =
        β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') := rfl
  have hleft_m :
      (dualToAmbient R M W.left β).hom.app (op (Over.mk (𝟙 W.left))) m' =
        β.val.app (op (Over.mk (𝟙 W.left))) m' := rfl
  have hright_smul :
      (((ambientDual R M).obj.map W.hom.op s).hom.app
          (op (Over.mk (𝟙 W.left)))) (r' • m') =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') := rfl
  have hright_m :
      (((ambientDual R M).obj.map W.hom.op s).hom.app
          (op (Over.mk (𝟙 W.left)))) m' =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' := rfl
  have hβ_canon_smul :
      β.val.app (op (Over.mk (𝟙 W.left))) (r' • m') =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') :=
    hleft_smul.symm.trans (hβ_smul.trans hright_smul)
  have hβ_canon_m :
      β.val.app (op (Over.mk (𝟙 W.left))) m' =
        s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' :=
    hleft_m.symm.trans (hβ_m.trans hright_m)
  let e : (Over.map W.hom).obj (Over.mk (𝟙 W.left)) ≅ W :=
    Over.isoMk (Iso.refl _) (by rfl)
  have hs_canon_smul :
      s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (r' • m') = s.hom.app (op W) (r' • m') := by
    have h := CategoryTheory.congr_fun (s.hom.naturality e.hom.op) (r' • m')
    dsimp [e] at h
    change s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).obj.map (𝟙 W.left).op
          (r' • m')) =
      ((_root_.SheafOfModules.toSheaf R).obj
          (_root_.SheafOfModules.unit R)).obj.map (𝟙 W.left).op
        (s.hom.app (op W) (r' • m')) at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).obj.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        (_root_.SheafOfModules.unit R)).obj.map_id] at h
    simpa using h
  have hs_canon_m :
      s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) m' =
        s.hom.app (op W) m' := by
    have h := CategoryTheory.congr_fun (s.hom.naturality e.hom.op) m'
    dsimp [e] at h
    change s.hom.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
        (((_root_.SheafOfModules.toSheaf R).obj M).obj.map (𝟙 W.left).op m') =
      ((_root_.SheafOfModules.toSheaf R).obj
          (_root_.SheafOfModules.unit R)).obj.map (𝟙 W.left).op
        (s.hom.app (op W) m') at h
    rw [op_id,
      ((_root_.SheafOfModules.toSheaf R).obj M).obj.map_id,
      ((_root_.SheafOfModules.toSheaf R).obj
        (_root_.SheafOfModules.unit R)).obj.map_id] at h
    simpa using h
  change s.hom.app (op W) (r' • m') =
    r' • (show (_root_.SheafOfModules.unit (R.over W.left)).val.obj
      (op (Over.mk (𝟙 W.left))) from s.hom.app (op W) m')
  rw [← hs_canon_smul, ← hs_canon_m, ← hβ_canon_smul, ← hβ_canon_m]
  exact (β.val.app (op (Over.mk (𝟙 W.left)))).hom.map_smul r' m'

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
set_option backward.isDefEq.respectTransparency.types false in
/-- Module-linearity of a local functional descends along covering sieves. -/
theorem dualSubfunctor_isSheaf (M : _root_.SheafOfModules R) :
    Presieve.IsSheaf J (dualSubfunctor R M).toFunctor := by
  apply ((dualSubfunctor R M).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type J (ambientDual R M).obj).mp
      (ambientDual R M).property)).2
  intro U s hs
  let α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop) :=
    { val := PresheafOfModules.homMk s.hom (dualSubfunctor_hom_app_smul R M s hs) }
  exact ⟨α, rfl⟩

/-- Local module-linear functionals identify with the corresponding points of the
module-linear subfunctor of the additive internal Hom. -/
noncomputable def dualToSubfunctorEquiv (M : _root_.SheafOfModules R) (U : Cᵒᵖ) :
    ((dualPresheafAb R M).obj U : Type u) ≃
      (dualSubfunctor R M).toFunctor.obj U where
  toFun α := ⟨dualToAmbient R M U.unop α, ⟨α, rfl⟩⟩
  invFun x := x.2.choose
  left_inv α := by
    apply dualToAmbient_injective R M U.unop
    exact (Set.mem_range.mp (show dualToAmbient R M U.unop α ∈
      Set.range (dualToAmbient R M U.unop) from ⟨α, rfl⟩)).choose_spec
  right_inv x := by
    apply Subtype.ext
    exact x.2.choose_spec

/-- The underlying type-valued presheaf of local linear functionals is isomorphic to
the module-linear subfunctor of the additive internal Hom. -/
noncomputable def dualPresheafToSubfunctorIso (M : _root_.SheafOfModules R) :
    dualPresheafAb R M ⋙ forget Ab ≅ (dualSubfunctor R M).toFunctor :=
  NatIso.ofComponents
    (fun U ↦ (dualToSubfunctorEquiv R M U).toIso)
    (fun f ↦ by
      ext α
      apply Subtype.ext
      exact ambientDual_map_dualToAmbient R M f α)

/-- The sheaf dual `Hom_R(M, R)`. -/
noncomputable def dual (M : _root_.SheafOfModules R) :
    _root_.SheafOfModules R where
  val := dualPresheaf R M
  isSheaf := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget J
      (dualPresheaf R M).presheaf (forget _)).mpr
    apply (isSheaf_iff_isSheaf_of_type J _).mpr
    exact Presieve.isSheaf_iso J (dualPresheafToSubfunctorIso R M).symm
      (dualSubfunctor_isSheaf R M)

@[simp]
theorem dual_val (M : _root_.SheafOfModules R) :
    (dual R M).val = dualPresheaf R M :=
  rfl

section

private instance overIsMulCommutative (U : C) :
    ∀ V, IsMulCommutative ((R.over U).obj.obj V) := fun V ↦ by
  change IsMulCommutative (R.obj.obj (op V.unop.left))
  infer_instance

private noncomputable def iteratedOverEquivalence (U : C) (V : Over U) :
    _root_.SheafOfModules ((R.over U).over V) ≌
      _root_.SheafOfModules (R.over V.left) :=
  (_root_.SheafOfModules.pushforwardPushforwardEquivalence
    (Over.iteratedSliceEquiv V)
    (S := (R.over U).over V) (R := R.over V.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)).symm

set_option maxHeartbeats 2000000 in
private noncomputable def iteratedDualSectionsEquiv
    (M : _root_.SheafOfModules R) (U : C) (V : Over U) :
    (((M.over U).over V ⟶ _root_.SheafOfModules.unit ((R.over U).over V))) ≃
      (M.over V.left ⟶ _root_.SheafOfModules.unit (R.over V.left)) :=
  (iteratedOverEquivalence R U V).fullyFaithfulFunctor.homEquiv

set_option maxHeartbeats 2000000 in
private noncomputable def iteratedDualSectionsLinearEquiv
    (M : _root_.SheafOfModules R) (U : C) (V : Over U) :
    letI : Module (R.obj.obj (op V.left))
        ((M.over U).over V ⟶ _root_.SheafOfModules.unit ((R.over U).over V)) :=
      dualSectionsModule (R.over U) (M.over U) V
    letI := dualSectionsModule R M V.left
    ((M.over U).over V ⟶ _root_.SheafOfModules.unit ((R.over U).over V))
      ≃ₗ[R.obj.obj (op V.left)]
    (M.over V.left ⟶ _root_.SheafOfModules.unit (R.over V.left)) := by
  letI : Module (R.obj.obj (op V.left))
      ((M.over U).over V ⟶ _root_.SheafOfModules.unit ((R.over U).over V)) :=
    dualSectionsModule (R.over U) (M.over U) V
  letI := dualSectionsModule R M V.left
  exact
    { toEquiv := iteratedDualSectionsEquiv R M U V
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Restricting a dual presheaf to an over-site agrees with taking the dual after
restriction. -/
noncomputable def dualOverPresheafIso (M : _root_.SheafOfModules R) (U : C) :
    ((dual R M).over U).val ≅ (dual (R.over U) (M.over U)).val := by
  refine PresheafOfModules.isoMk
    (fun V ↦ (iteratedDualSectionsLinearEquiv R M U V.unop).symm.toModuleIso)
    (fun {_ _} f ↦ ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  rfl

/-- Restricting a sheaf dual to an over-site agrees with taking the dual after
restriction. -/
noncomputable def dualOverIso (M : _root_.SheafOfModules R) (U : C) :
    (dual R M).over U ≅ dual (R.over U) (M.over U) := by
  exact (_root_.SheafOfModules.fullyFaithfulForget (R.over U)).preimageIso
    (dualOverPresheafIso R M U)

end

/-- An endomorphism of the unit module over `Over U` is determined by its value at
`1` over the terminal object. -/
noncomputable def dualUnitSectionsEquiv (U : C) :
    (_root_.SheafOfModules.unit (R.over U) ⟶
      _root_.SheafOfModules.unit (R.over U)) ≃ R.obj.obj (op U) :=
  (_root_.SheafOfModules.unit (R.over U)).unitHomEquiv.trans
    (overUnitSectionEquiv R U).symm

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem dualUnitSectionsEquiv_apply (U : C)
    (α : _root_.SheafOfModules.unit (R.over U) ⟶
      _root_.SheafOfModules.unit (R.over U)) :
    dualUnitSectionsEquiv R U α =
      α.val.app (op (Over.mk (𝟙 U)))
        (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1) :=
  rfl

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem dualUnitSectionsEquiv_symm_apply (U : C) (r : R.obj.obj (op U)) :
    (dualUnitSectionsEquiv R U).symm r = overUnitScalarEnd R U r :=
  rfl

/-- The identification of unit endomorphisms with scalars is linear for the
postcomposition action used on the dual. -/
@[reducible]
noncomputable def dualUnitEndModule (U : C) :
    Module (R.obj.obj (op U))
      (End (_root_.SheafOfModules.unit (R.over U))) :=
  Module.compHom _ (overUnitScalarEndRingHom R U)

set_option backward.isDefEq.respectTransparency.types false in
/-- The identification of unit endomorphisms with scalars is linear for the
postcomposition action used on the dual. -/
noncomputable def dualUnitLinearEquiv (U : C) :
    letI := dualUnitEndModule R U
    End (_root_.SheafOfModules.unit (R.over U)) ≃ₗ[R.obj.obj (op U)]
        R.obj.obj (op U) := by
  letI := dualUnitEndModule R U
  refine
    { toEquiv := dualUnitSectionsEquiv R U
      map_add' := ?_
      map_smul' := ?_ }
  · intro α β
    change (α + β).val.app (op (Over.mk (𝟙 U)))
        (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1) =
      α.val.app (op (Over.mk (𝟙 U)))
          (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1) +
        β.val.app (op (Over.mk (𝟙 U)))
          (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1)
    rfl
  · intro r α
    rw [show r • α = α ≫ overUnitScalarEnd R U r from rfl]
    change (overUnitScalarEnd R U r).val.app (op (Over.mk (𝟙 U)))
        (α.val.app (op (Over.mk (𝟙 U)))
          (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1)) =
      r * (show R.obj.obj (op U) from
        α.val.app (op (Over.mk (𝟙 U)))
          (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1))
    rw [overUnitScalarEnd_app_apply]
    change (show R.obj.obj (op U) from α.val.app (op (Over.mk (𝟙 U)))
          (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1)) *
        R.obj.map (𝟙 U).op r = _
    rw [op_id, R.obj.map_id]
    exact mul_comm' _ _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem dualUnitLinearEquiv_dualRestrict {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : (_root_.SheafOfModules.unit R).over U.unop ⟶
      _root_.SheafOfModules.unit (R.over U.unop)) :
    dualUnitLinearEquiv R V.unop (dualRestrict R (_root_.SheafOfModules.unit R) f α) =
      R.obj.map f (dualUnitLinearEquiv R U.unop α) := by
  change (dualRestrict R (_root_.SheafOfModules.unit R) f α).val.app
      (op (Over.mk (𝟙 V.unop)))
        (show (R.over V.unop).obj.obj (op (Over.mk (𝟙 V.unop))) from 1) =
    R.obj.map f (α.val.app (op (Over.mk (𝟙 U.unop)))
      (show (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop))) from 1))
  dsimp [dualRestrict, _root_.SheafOfModules.overFunctorMap,
    _root_.SheafOfModules.overMapUnitIso, _root_.SheafOfModules.overMap,
    _root_.SheafOfModules.pushforward]
  change α.val.app
      (op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop))))
        (show (R.over U.unop).obj.obj
          (op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop)))) from 1) =
    R.obj.map f (α.val.app (op (Over.mk (𝟙 U.unop)))
      (show (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop))) from 1))
  let g : (Over.map f.unop).obj (Over.mk (𝟙 V.unop)) ⟶
      Over.mk (𝟙 U.unop) := Over.homMk f.unop (by
        change f.unop ≫ 𝟙 U.unop = 𝟙 V.unop ≫ f.unop
        rw [Category.comp_id, Category.id_comp])
  have h := CategoryTheory.congr_fun (α.val.naturality g.op)
    (show (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop))) from 1)
  change α.val.app (op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop))))
      (((_root_.SheafOfModules.unit R).over U.unop).val.map g.op
        (show (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop))) from 1)) =
    (_root_.SheafOfModules.unit (R.over U.unop)).val.map g.op
      (α.val.app (op (Over.mk (𝟙 U.unop)))
        (show (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop))) from 1)) at h
  have hsource_one :
      ((_root_.SheafOfModules.unit R).over U.unop).val.map g.op
          (show ((_root_.SheafOfModules.unit R).over U.unop).val.obj
            (op (Over.mk (𝟙 U.unop))) from
              (1 : (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop))))) =
        (show ((_root_.SheafOfModules.unit R).over U.unop).val.obj
          (op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop)))) from
            (1 : (R.over U.unop).obj.obj
              (op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop)))))) := by
    change R.obj.map g.left.op 1 = 1
    exact (R.obj.map g.left.op).hom.map_one
  have htarget (x : (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop)))) :
      (_root_.SheafOfModules.unit (R.over U.unop)).val.map g.op x =
        R.obj.map f x := by
    change R.obj.map g.left.op x = R.obj.map f x
    rfl
  rw [hsource_one, htarget] at h
  change α.val.app (op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop))))
      (show (R.over U.unop).obj.obj
        (op ((Over.map f.unop).obj (Over.mk (𝟙 V.unop)))) from 1) =
    R.obj.map f (α.val.app (op (Over.mk (𝟙 U.unop)))
      (show (R.over U.unop).obj.obj (op (Over.mk (𝟙 U.unop))) from 1)) at h
  exact h

/-- The dual presheaf of the unit module is the unit presheaf. -/
noncomputable def dualUnitPresheafIso :
    dualPresheaf R (_root_.SheafOfModules.unit R) ≅
      PresheafOfModules.unit R.obj :=
  PresheafOfModules.isoMk
    (fun U ↦ (dualUnitLinearEquiv R U.unop).toModuleIso)
    (fun {_ _} f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      exact dualUnitLinearEquiv_dualRestrict R f α)

/-- The sheaf dual of the structure sheaf is canonically the structure sheaf. -/
noncomputable def dualUnitIso :
    dual R (_root_.SheafOfModules.unit R) ≅ _root_.SheafOfModules.unit R :=
  (_root_.SheafOfModules.fullyFaithfulForget R).preimageIso
    (dualUnitPresheafIso R)

/-- Precomposition of a local functional by a morphism of sheaves of modules. -/
noncomputable def dualPrecomp {M N : _root_.SheafOfModules R} (f : M ⟶ N)
    (U : C) (α : N.over U ⟶ _root_.SheafOfModules.unit (R.over U)) :
    M.over U ⟶ _root_.SheafOfModules.unit (R.over U) :=
  f.over U ≫ α

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem dualRestrict_dualPrecomp {M N : _root_.SheafOfModules R} (f : M ⟶ N)
    {U V : Cᵒᵖ} (g : U ⟶ V)
    (α : N.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) :
    dualRestrict R M g (dualPrecomp R f U.unop α) =
      dualPrecomp R f V.unop (dualRestrict R N g α) := by
  rfl

/-- Precomposition is linear for the postcomposition scalar action on local
functionals. -/
noncomputable def dualPrecompLinearMap {M N : _root_.SheafOfModules R}
    (f : M ⟶ N) (U : C) :
    letI := dualSectionsModule R N U
    letI := dualSectionsModule R M U
    (N.over U ⟶ _root_.SheafOfModules.unit (R.over U)) →ₗ[R.obj.obj (op U)]
      (M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) := by
  letI := dualSectionsModule R N U
  letI := dualSectionsModule R M U
  refine
    { toFun := dualPrecomp R f U
      map_add' := ?_
      map_smul' := ?_ }
  · intro α β
    simp [dualPrecomp, Preadditive.comp_add]
  · intro r α
    change f.over U ≫ (α ≫ overUnitScalarEnd R U r) =
      (f.over U ≫ α) ≫ overUnitScalarEnd R U r
    simp [Category.assoc]

/-- The morphism on dual presheaves induced contravariantly by a module morphism. -/
noncomputable def dualMapVal {M N : _root_.SheafOfModules R} (f : M ⟶ N) :
    dualPresheaf R N ⟶ dualPresheaf R M where
  app U := by
    letI := dualSectionsModule R N U.unop
    letI := dualSectionsModule R M U.unop
    change ModuleCat.of (R.obj.obj U)
        (N.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop)) ⟶
      ModuleCat.of (R.obj.obj U)
        (M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop))
    exact ModuleCat.ofHom (dualPrecompLinearMap R f U.unop)
  naturality g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact dualRestrict_dualPrecomp R f g α

/-- Dualization sends a module morphism to the reverse morphism on sheaf duals. -/
noncomputable def dualMap {M N : _root_.SheafOfModules R} (f : M ⟶ N) :
    dual R N ⟶ dual R M :=
  ⟨dualMapVal R f⟩

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem dualMap_id (M : _root_.SheafOfModules R) :
    dualMap R (𝟙 M) = 𝟙 (dual R M) := by
  ext U α
  dsimp [dualMap, dualMapVal, dualPrecompLinearMap, dualPrecomp]
  change dualPrecomp R (𝟙 M) U.unop α = α
  simp [dualPrecomp]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem dualMap_comp {M N P : _root_.SheafOfModules R} (f : M ⟶ N) (g : N ⟶ P) :
    dualMap R (f ≫ g) = dualMap R g ≫ dualMap R f := by
  ext U α
  dsimp [dualMap, dualMapVal, dualPrecompLinearMap, dualPrecomp]
  change dualPrecomp R (f ≫ g) U.unop α =
    dualPrecomp R f U.unop (dualPrecomp R g U.unop α)
  simp [dualPrecomp, Category.assoc]

/-- An isomorphism of modules induces the reverse isomorphism of their duals. -/
noncomputable def dualIso {M N : _root_.SheafOfModules R} (e : M ≅ N) :
    dual R N ≅ dual R M where
  hom := dualMap R e.hom
  inv := dualMap R e.inv
  hom_inv_id := by
    rw [← dualMap_comp, e.inv_hom_id, dualMap_id]
  inv_hom_id := by
    rw [← dualMap_comp, e.hom_inv_id, dualMap_id]

/-- A trivialization of `M` over `U` identifies local functionals on `M` with
scalars on `U`. -/
noncomputable def dualTrivializationLinearEquiv (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) :
    letI := dualSectionsModule R M U
    (M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) ≃ₗ[R.obj.obj (op U)]
      R.obj.obj (op U) := by
  letI := dualSectionsModule R M U
  letI := dualUnitEndModule R U
  refine
    { toFun := fun α ↦ dualUnitLinearEquiv R U (e.inv ≫ α)
      invFun := fun r ↦ e.hom ≫ (dualUnitLinearEquiv R U).symm r
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro α β
    let α' : End (_root_.SheafOfModules.unit (R.over U)) := e.inv ≫ α
    let β' : End (_root_.SheafOfModules.unit (R.over U)) := e.inv ≫ β
    rw [Preadditive.comp_add]
    change dualUnitLinearEquiv R U (α' + β') =
      dualUnitLinearEquiv R U α' + dualUnitLinearEquiv R U β'
    exact (dualUnitLinearEquiv R U).map_add α' β'
  · intro r α
    let α' : End (_root_.SheafOfModules.unit (R.over U)) := e.inv ≫ α
    change dualUnitLinearEquiv R U
        (e.inv ≫ (α ≫ overUnitScalarEnd R U r)) =
      r • dualUnitLinearEquiv R U α'
    rw [← Category.assoc]
    change dualUnitLinearEquiv R U (r • α') =
      r • dualUnitLinearEquiv R U α'
    exact (dualUnitLinearEquiv R U).map_smul r α'
  · intro α
    let α' : End (_root_.SheafOfModules.unit (R.over U)) := e.inv ≫ α
    change e.hom ≫ (dualUnitLinearEquiv R U).symm
      (dualUnitLinearEquiv R U α') = α
    rw [LinearEquiv.symm_apply_apply]
    change e.hom ≫ (e.inv ≫ α) = α
    simp
  · intro r
    let α' : End (_root_.SheafOfModules.unit (R.over U)) :=
      (dualUnitLinearEquiv R U).symm r
    change dualUnitLinearEquiv R U
      (e.inv ≫ (e.hom ≫ α')) = r
    rw [← Category.assoc]
    rw [e.inv_hom_id, Category.id_comp]
    exact (dualUnitLinearEquiv R U).apply_symm_apply r

/-- Restrict an over-site trivialization from `U` to an object `V ⟶ U`. -/
noncomputable def restrictOverTrivialization (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) (V : Over U) :
    M.over V.left ≅ _root_.SheafOfModules.unit (R.over V.left) :=
  ((_root_.SheafOfModules.overFunctorMap R V.hom).app M).symm ≪≫
    (_root_.SheafOfModules.overMap R V.hom).mapIso e ≪≫
      _root_.SheafOfModules.overMapUnitIso V.hom

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem dualRestrict_app_apply (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop))
    (Z : (Over V.unop)ᵒᵖ) (x : (M.over V.unop).val.obj Z) :
    (dualRestrict R M f α).val.app Z x =
      α.val.app (op ((Over.map f.unop).obj Z.unop)) x :=
  rfl

omit [∀ U, IsMulCommutative (R.obj.obj U)] in
@[simp]
theorem restrictOverTrivialization_inv_app_apply
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) (V : Over U)
    (Z : (Over V.left)ᵒᵖ)
    (x : (_root_.SheafOfModules.unit (R.over V.left)).val.obj Z) :
    (restrictOverTrivialization R M U e V).inv.val.app Z x =
      e.inv.val.app (op ((Over.map V.hom).obj Z.unop)) x :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem dualTrivializationLinearEquiv_dualRestrict
    (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    {V W : Over U} (f : V ⟶ W)
    (α : M.over W.left ⟶ _root_.SheafOfModules.unit (R.over W.left)) :
    dualTrivializationLinearEquiv R M V.left
        (restrictOverTrivialization R M U e V)
        (dualRestrict R M f.left.op α) =
      R.obj.map f.left.op
        (dualTrivializationLinearEquiv R M W.left
          (restrictOverTrivialization R M U e W) α) := by
  change (dualRestrict R M f.left.op α).val.app
      (op (Over.mk (𝟙 V.left)))
        ((restrictOverTrivialization R M U e V).inv.val.app
          (op (Over.mk (𝟙 V.left)))
          (show (R.over V.left).obj.obj (op (Over.mk (𝟙 V.left))) from 1)) =
    R.obj.map f.left.op
      (α.val.app (op (Over.mk (𝟙 W.left)))
        ((restrictOverTrivialization R M U e W).inv.val.app
          (op (Over.mk (𝟙 W.left)))
          (show (R.over W.left).obj.obj (op (Over.mk (𝟙 W.left))) from 1)))
  rw [dualRestrict_app_apply, restrictOverTrivialization_inv_app_apply,
    restrictOverTrivialization_inv_app_apply]
  change α.val.app
      (op ((Over.map f.left).obj (Over.mk (𝟙 V.left))))
        (e.inv.val.app
          (op ((Over.map V.hom).obj (Over.mk (𝟙 V.left))))
          (show (R.over U).obj.obj
            (op ((Over.map V.hom).obj (Over.mk (𝟙 V.left)))) from 1)) =
    R.obj.map f.left.op
      (α.val.app (op (Over.mk (𝟙 W.left)))
        (e.inv.val.app
          (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (show (R.over U).obj.obj
            (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1)))
  let g : (Over.map f.left).obj (Over.mk (𝟙 V.left)) ⟶
      Over.mk (𝟙 W.left) :=
    Over.homMk f.left (by
      change f.left ≫ 𝟙 W.left = 𝟙 V.left ≫ f.left
      rw [Category.comp_id, Category.id_comp])
  let h : (Over.map V.hom).obj (Over.mk (𝟙 V.left)) ⟶
      (Over.map W.hom).obj (Over.mk (𝟙 W.left)) :=
    Over.homMk f.left (by
      change f.left ≫ (𝟙 W.left ≫ W.hom) = 𝟙 V.left ≫ V.hom
      rw [Category.id_comp, Category.id_comp]
      exact f.w)
  have he := PresheafOfModules.naturality_apply e.inv.val h.op
    (show (R.over U).obj.obj
      (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1)
  have he' :
      e.inv.val.app (op ((Over.map V.hom).obj (Over.mk (𝟙 V.left))))
          (show (R.over U).obj.obj
            (op ((Over.map V.hom).obj (Over.mk (𝟙 V.left)))) from 1) =
        (M.over W.left).val.map g.op
          (e.inv.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
            (show (R.over U).obj.obj
              (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1)) := by
    change e.inv.val.app
        (op ((Over.map V.hom).obj (Over.mk (𝟙 V.left))))
          ((R.over U).obj.map h.op
            (show (R.over U).obj.obj
              (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1)) =
      (M.over W.left).val.map g.op
        (e.inv.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (show (R.over U).obj.obj
            (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1)) at he
    rw [map_one] at he
    exact he
  rw [he']
  have hα := PresheafOfModules.naturality_apply α.val g.op
    (e.inv.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
      (show (R.over U).obj.obj
        (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1))
  change α.val.app
      (op ((Over.map f.left).obj (Over.mk (𝟙 V.left))))
        ((M.over W.left).val.map g.op
          (e.inv.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
            (show (R.over U).obj.obj
              (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1))) =
    R.obj.map f.left.op
      (α.val.app (op (Over.mk (𝟙 W.left)))
        (e.inv.val.app (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left))))
          (show (R.over U).obj.obj
            (op ((Over.map W.hom).obj (Over.mk (𝟙 W.left)))) from 1))) at hα
  exact hα

/-- A trivialization of `M` over `U` trivializes the restriction of its dual to
the same over-site. -/
noncomputable def dualOverPresheafIsoOfIso (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) :
    ((dual R M).over U).val ≅ PresheafOfModules.unit (R.over U).obj :=
  PresheafOfModules.isoMk
    (fun V ↦ (dualTrivializationLinearEquiv R M V.unop.left
      (restrictOverTrivialization R M U e V.unop)).toModuleIso)
    (fun {_ _} f ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      exact dualTrivializationLinearEquiv_dualRestrict R M U e f.unop α)

/-- The sheaf dual of a module trivialized over `U` is trivial over `U`. -/
noncomputable def dualOverIsoOfIso (M : _root_.SheafOfModules R) (U : C)
    (e : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) :
    (dual R M).over U ≅ _root_.SheafOfModules.unit (R.over U) :=
  (_root_.SheafOfModules.fullyFaithfulForget (R.over U)).preimageIso
    (dualOverPresheafIsoOfIso R M U e)

end SheafOfModules

end ModularCurves

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

/-- The sheaf dual `Hom_{𝒪_X}(M, 𝒪_X)` of a module on a scheme. -/
noncomputable def dualObj (M : X.Modules) : X.Modules :=
  ModularCurves.SheafOfModules.dual X.ringCatSheaf M

/-- A module morphism induces the reverse morphism on scheme-level duals. -/
noncomputable def dualMapObj {M N : X.Modules} (f : M ⟶ N) :
    dualObj N ⟶ dualObj M :=
  ModularCurves.SheafOfModules.dualMap X.ringCatSheaf f

/-- An isomorphism of modules induces the reverse isomorphism of their scheme-level duals. -/
noncomputable def dualIsoObj {M N : X.Modules} (e : M ≅ N) :
    dualObj N ≅ dualObj M :=
  ModularCurves.SheafOfModules.dualIso X.ringCatSheaf e

/-- The dual of the structure sheaf is the structure sheaf. -/
noncomputable def dualUnitObjIso : dualObj (unitObj X) ≅ unitObj X :=
  ModularCurves.SheafOfModules.dualUnitIso X.ringCatSheaf

/-- A restriction trivialization of `M` induces a restriction trivialization of
its sheaf dual. -/
noncomputable def dualRestrictIsoOfRestrictIso (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ unitObj U.toScheme) :
    (restrictFunctor U.ι).obj (dualObj M) ≅ unitObj U.toScheme :=
  ((overFunctorEquiv U).app
      (dualObj M)).symm ≪≫
    (overEquiv U).functor.mapIso
      (ModularCurves.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U
        (overTrivializationOfRestrictIso M U e)) ≪≫
    U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- The sheaf dual of an invertible module is invertible. -/
theorem IsInvertible.dual {M : X.Modules} (hM : IsInvertible M) :
    IsInvertible (dualObj M) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  refine ⟨ι, U, hU, fun i ↦ ?_⟩
  obtain ⟨e⟩ := htriv i
  exact ⟨pullbackIsoOfRestrictIso (dualObj M) (U i)
    (dualRestrictIsoOfRestrictIso M (U i) (restrictIsoOfPullbackIso M (U i) e))⟩

end AlgebraicGeometry.Scheme.Modules
