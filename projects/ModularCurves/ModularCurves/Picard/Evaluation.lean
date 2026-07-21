/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.Dual

/-!
# Evaluation against the sheaf dual

This file isolates the evaluation pairing from the Picard comparison.  It is
used independently by the projective-twist construction.
-/

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace ModularCurves.SheafOfModules

open Opposite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- A section of `M` over `U`, regarded as a section on the over-site of `U`. -/
noncomputable def overSection (M : _root_.SheafOfModules R) (U : C)
    (m : M.val.obj (op U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun (V : (Over U)ᵒᵖ) => M.val.map V.unop.hom.op m)
    (fun {V W : (Over U)ᵒᵖ} f => by
      change M.val.map f.unop.left.op (M.val.map V.unop.hom.op m) =
        M.val.map W.unop.hom.op m
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w])

/-- Sections on the over-site restriction are sections over the original object. -/
noncomputable def overSectionEquiv (M : _root_.SheafOfModules R) (U : C) :
    M.val.obj (op U) ≃ (M.over U).sections where
  toFun := overSection R M U
  invFun s := s.val (op (Over.mk (CategoryStruct.id U)))
  left_inv m := by
    change M.val.map (CategoryStruct.id U).op m = m
    rw [op_id, M.val.map_id]
    rfl
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    change M.val.map V.unop.hom.op
      (s.val (op (Over.mk (CategoryStruct.id U)))) = s.val V
    have h := s.property (Over.mkIdTerminal.from V.unop).op
    change M.val.map (Over.mkIdTerminal.from V.unop).left.op
      (s.val (op (Over.mk (CategoryStruct.id U)))) = s.val V at h
    rw [Over.mkIdTerminal_from_left] at h
    exact h

@[simp]
theorem overSection_apply (M : _root_.SheafOfModules R) (U : C)
    (m : M.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overSection R M U m).val V = M.val.map V.unop.hom.op m :=
  rfl

/-- Evaluate a local functional against a section of a module. -/
noncomputable def evalSection (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) : R.obj.obj (op U) :=
  (overUnitSectionEquiv R U).symm
    (_root_.SheafOfModules.sectionsMap φ (overSection R M U m))

@[simp]
theorem evalSection_eq (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) :
    evalSection R M U φ m =
      φ.val.app (op (Over.mk (CategoryStruct.id U)))
        (M.val.map (CategoryStruct.id U).op m) :=
  rfl

theorem evalSection_add_right (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m m' : M.val.obj (op U)) :
    evalSection R M U φ (m + m') =
      evalSection R M U φ m + evalSection R M U φ m' := by
  simp only [evalSection_eq, map_add]
  exact map_add _ _ _

theorem evalSection_smul_right (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (r : R.obj.obj (op U)) (m : M.val.obj (op U)) :
    evalSection R M U φ (r • m) = r • evalSection R M U φ m := by
  simp only [evalSection_eq]
  rw [PresheafOfModules.map_smul]
  erw [(φ.val.app (op (Over.mk (CategoryStruct.id U)))).hom.map_smul]
  congr 1
  rw [op_id, R.obj.map_id]
  rfl

theorem evalSection_add_left (M : _root_.SheafOfModules R) (U : C)
    (φ ψ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) :
    evalSection R M U (φ + ψ) m =
      evalSection R M U φ m + evalSection R M U ψ m := by
  simp only [evalSection_eq]
  rfl

theorem evalSection_smul_left (M : _root_.SheafOfModules R) (U : C)
    [∀ V, IsMulCommutative (R.obj.obj V)]
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (r : R.obj.obj (op U)) (m : M.val.obj (op U)) :
    evalSection R M U (letI := dualSectionsModule R M U; r • φ) m =
      r • evalSection R M U φ m := by
  change evalSection R M U (φ ≫ overUnitScalarEnd R U r) m = _
  simp only [evalSection_eq]
  change
    (show R.obj.obj (op U) from
      φ.val.app (op (Over.mk (CategoryStruct.id U)))
        (M.val.map (CategoryStruct.id U).op m)) *
        (show R.obj.obj (op U) from
          R.obj.map (CategoryStruct.id U).op r) =
      r * (show R.obj.obj (op U) from
        φ.val.app (op (Over.mk (CategoryStruct.id U)))
          (M.val.map (CategoryStruct.id U).op m))
  have hr : (show R.obj.obj (op U) from
      R.obj.map (CategoryStruct.id U).op r) = r := by
    rw [op_id, R.obj.map_id]
    rfl
  rw [hr]
  exact mul_comm' _ r

/-- Evaluation commutes with restriction. -/
theorem evalSection_naturality (M : _root_.SheafOfModules R)
    {U V : Cᵒᵖ} (i : U ⟶ V)
    (φ : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop))
    (m : M.val.obj U) :
    evalSection R M V.unop (dualRestrict R M i φ) (M.val.map i m) =
      R.obj.map i (evalSection R M U.unop φ m) := by
  change
    (dualRestrict R M i φ).val.app
        (op (Over.mk (CategoryStruct.id V.unop)))
        (M.val.map (CategoryStruct.id V.unop).op (M.val.map i m)) =
      R.obj.map i
        (φ.val.app (op (Over.mk (CategoryStruct.id U.unop)))
          (M.val.map (CategoryStruct.id U.unop).op m))
  dsimp [dualRestrict, _root_.SheafOfModules.overMapUnitIso,
    _root_.SheafOfModules.overMap, _root_.SheafOfModules.pushforward,
    _root_.SheafOfModules.overFunctorMap]
  simp
  exact PresheafOfModules.naturality_apply φ.val
    ((Over.homMk i.unop (by
      show i.unop ≫ CategoryStruct.id (Opposite.unop U) =
        CategoryStruct.id (Opposite.unop V) ≫ i.unop
      simp) :
      (Over.map i.unop).obj
          (Over.mk (CategoryStruct.id (Opposite.unop V))) ⟶
        Over.mk (CategoryStruct.id (Opposite.unop U))).op) m

end ModularCurves.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U => by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b => mul_comm a b

open ModularCurves.SheafOfModules in
/-- Presheaf evaluation of a module against its sheaf dual. -/
noncomputable def evPre (M : X.Modules) :
    (M.val ⊗ (dualObj M).val :
      _root_.PresheafOfModules
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⟶
      𝟙_ (_root_.PresheafOfModules
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) where
  app U := ModuleCat.ofHom (TensorProduct.lift (by
    letI := dualSectionsModule X.ringCatSheaf M U.unop
    letI : SMulCommClass
        ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
        ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
        ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) :=
      ⟨fun a b c => by
        show a * (b * c) = b * (a * c)
        rw [← mul_assoc, mul_comm' a b, mul_assoc]⟩
    exact LinearMap.mk₂
      ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
      (fun m φ => evalSection X.ringCatSheaf M U.unop φ m)
      (fun m m' φ => evalSection_add_right
        X.ringCatSheaf M U.unop φ m m')
      (fun r m φ => evalSection_smul_right
        X.ringCatSheaf M U.unop φ r m)
      (fun m φ ψ => evalSection_add_left
        X.ringCatSheaf M U.unop φ ψ m)
      (fun r m φ => evalSection_smul_left
        X.ringCatSheaf M U.unop φ r m)))
  naturality {U V} i := by
    refine ModuleCat.MonoidalCategory.tensor_ext (fun m φ => ?_)
    exact evalSection_naturality X.ringCatSheaf M i φ m

/-- Evaluation on the sheafified tensor product. -/
noncomputable def ev (M : X.Modules) : tensorObj M (dualObj M) ⟶ unitObj X :=
  (PresheafOfModules.sheafificationAdjunction
    (CategoryStruct.id X.ringCatSheaf.obj)).homEquiv
      (M.val ⊗ (dualObj M).val) (unitObj X) |>.symm (evPre M)

/-- The sheaf-dual evaluation is obtained by sheafifying the presheaf pairing and
then applying the sheafification counit. -/
theorem ev_eq_sheafification_map (M : X.Modules) :
    ev M =
      (PresheafOfModules.sheafification
        (CategoryStruct.id X.ringCatSheaf.obj)).map (evPre M) ≫
        (sheafifyValIso (unitObj X)).hom := by
  let α := CategoryStruct.id X.ringCatSheaf.obj
  let P : X.PresheafOfModules := M.val ⊗ (dualObj M).val
  let F : X.Modules := unitObj X
  let adj := PresheafOfModules.sheafificationAdjunction α
  have hCounit :
      (adj.homEquiv P F).symm (evPre M) =
        (PresheafOfModules.sheafification α).map (evPre M) ≫
          adj.counit.app F :=
    adj.homEquiv_counit (X := P) (Y := F) (g := evPre M)
  exact hCounit

end AlgebraicGeometry.Scheme.Modules
