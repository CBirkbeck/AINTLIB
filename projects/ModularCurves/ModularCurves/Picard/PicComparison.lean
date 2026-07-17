/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import ModularCurves.Picard.Dual
import ModularCurves.Picard.PullbackTensorObj
import ModularCurves.Picard.InvertibleSheaf

/-!
# The Picard comparison: cover-local invertibility ↔ ⊗-invertibility

**[PIC-P2-CMP]** (GME 2.2.2 (2.17): *"the formation of an invertible sheaf is local"*):
the cover-local `IsInvertible` predicate of `Picard/InvertibleSheaf.lean` agrees with
⊗-invertibility in the localized monoidal structure — i.e. with defining an element of
`Pic X = (Skeleton X.Modules)ˣ`.

Bridging layer (closed here): the hand-rolled sheafified tensor `tensorObj` and unit
`unitObj` of `Picard/InvertibleSheaf.lean` agree with the localized monoidal `⊗` / `𝟙_`
of `Modules.monoidalCategory` (`tensorObj_iso_tensor`, `unitObj_iso_unit`).

Leaves (`Nonempty`-wrapped `Prop`s, v10.8 discipline):
* `nonempty_eval_iso` **[CMP-PAIR]**: for invertible `M` the evaluation pairing
  `M ⊗ dualObj M ≅ 𝒪ₓ` — the dual is consumed from the merged `Picard/Dual.lean`
  (`IsInvertible.dual`, `dualObj`), never rebuilt; the content is the *global* pairing
  isomorphism from the cover-local trivializations.
* `isInvertible_of_isUnit` **[CMP-←]**: a ⊗-unit is cover-locally trivial (Zariski-local
  freeness of invertible modules — independent of the dual machinery).
-/

universe u

open CategoryTheory MonoidalCategory

namespace ModularCurves.SheafOfModules

open Opposite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- **[PAIR-1a]** A section of `M` over `U` as a section of the restriction of `M` to the
over-site of `U` (mirror of `overUnitSection` at a general module). -/
noncomputable def overSection (M : _root_.SheafOfModules R) (U : C)
    (m : M.val.obj (op U)) : (M.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun (V : (Over U)ᵒᵖ) => M.val.map V.unop.hom.op m)
    (fun {V W : (Over U)ᵒᵖ} f => by
      change M.val.map f.unop.left.op (M.val.map V.unop.hom.op m) =
        M.val.map W.unop.hom.op m
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w])

/-- Sections of the over-site restriction are exactly sections over `U`, by evaluation at
the terminal object (mirror of `overUnitSectionEquiv` at a general module). -/
noncomputable def overSectionEquiv (M : _root_.SheafOfModules R) (U : C) :
    M.val.obj (op U) ≃ (M.over U).sections where
  toFun := overSection R M U
  invFun s := s.val (op (Over.mk (𝟙 U)))
  left_inv m := by
    change M.val.map (𝟙 U).op m = m
    rw [op_id, M.val.map_id]
    rfl
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro V
    change M.val.map V.unop.hom.op (s.val (op (Over.mk (𝟙 U)))) = s.val V
    have h := s.property (Over.mkIdTerminal.from V.unop).op
    change M.val.map (Over.mkIdTerminal.from V.unop).left.op
      (s.val (op (Over.mk (𝟙 U)))) = s.val V at h
    rw [Over.mkIdTerminal_from_left] at h
    exact h

@[simp]
theorem overSection_apply (M : _root_.SheafOfModules R) (U : C)
    (m : M.val.obj (op U)) (V : (Over U)ᵒᵖ) :
    (overSection R M U m).val V = M.val.map V.unop.hom.op m :=
  rfl

/-- **[PAIR-1b]** Evaluation of a local linear functional (a section of the sheaf dual)
against a section of `M`, landing in the structure sheaf: push the section into the
over-site, apply the functional, and read off the unit-section at the terminal object. -/
noncomputable def evalSection (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) : R.obj.obj (op U) :=
  (overUnitSectionEquiv R U).symm
    (_root_.SheafOfModules.sectionsMap φ (overSection R M U m))

@[simp]
theorem evalSection_eq (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) :
    evalSection R M U φ m = φ.val.app (op (Over.mk (𝟙 U))) (M.val.map (𝟙 U).op m) :=
  rfl

theorem evalSection_add_right (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m m' : M.val.obj (op U)) :
    evalSection R M U φ (m + m') = evalSection R M U φ m + evalSection R M U φ m' := by
  simp only [evalSection_eq, map_add]
  exact map_add _ _ _

theorem evalSection_smul_right (M : _root_.SheafOfModules R) (U : C)
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (r : R.obj.obj (op U)) (m : M.val.obj (op U)) :
    evalSection R M U φ (r • m) = r • evalSection R M U φ m := by
  simp only [evalSection_eq]
  rw [PresheafOfModules.map_smul]
  erw [(φ.val.app (op (Over.mk (𝟙 U)))).hom.map_smul]
  congr 1
  rw [op_id, R.obj.map_id]
  rfl

theorem evalSection_add_left (M : _root_.SheafOfModules R) (U : C)
    (φ ψ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (m : M.val.obj (op U)) :
    evalSection R M U (φ + ψ) m = evalSection R M U φ m + evalSection R M U ψ m := by
  simp only [evalSection_eq]
  rfl

theorem evalSection_unit_mul (U : C) [∀ V, IsMulCommutative (R.obj.obj V)]
    (φ : (_root_.SheafOfModules.unit R).over U ⟶
      _root_.SheafOfModules.unit (R.over U))
    (r : (_root_.SheafOfModules.unit R).val.obj (op U)) :
    evalSection R (_root_.SheafOfModules.unit R) U φ r =
      evalSection R (_root_.SheafOfModules.unit R) U φ
        (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U))) *
        (show R.obj.obj (op U) from r) := by
  have h := evalSection_smul_right R (_root_.SheafOfModules.unit R) U φ
    (show R.obj.obj (op U) from r)
    (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U)))
  rw [show ((show R.obj.obj (op U) from r) •
      (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U))) :
        (_root_.SheafOfModules.unit R).val.obj (op U)) = r from by
    show (show R.obj.obj (op U) from r) * (1 : R.obj.obj (op U)) = r
    rw [mul_one]] at h
  rw [h, smul_eq_mul]
  exact mul_comm' _ _

theorem evalSection_unit_one (U : C)
    (φ : (_root_.SheafOfModules.unit R).over U ⟶
      _root_.SheafOfModules.unit (R.over U)) :
    evalSection R (_root_.SheafOfModules.unit R) U φ
        (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U))) =
      φ.val.app (op (Over.mk (𝟙 U)))
        (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1) := by
  simp only [evalSection_eq]
  congr 1
  show R.obj.map (𝟙 U).op (1 : R.obj.obj (op U)) = (1 : R.obj.obj (op U))
  rw [op_id, R.obj.map_id]
  rfl

theorem evalSection_smul_left (M : _root_.SheafOfModules R) (U : C)
    [∀ V, IsMulCommutative (R.obj.obj V)]
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U))
    (r : R.obj.obj (op U)) (m : M.val.obj (op U)) :
    evalSection R M U (letI := dualSectionsModule R M U; r • φ) m =
      r • evalSection R M U φ m := by
  show evalSection R M U (φ ≫ overUnitScalarEnd R U r) m = _
  simp only [evalSection_eq]
  show (overUnitScalarEnd R U r).val.app (op (Over.mk (𝟙 U)))
    (φ.val.app (op (Over.mk (𝟙 U))) (M.val.map (𝟙 U).op m)) = _
  rw [overUnitScalarEnd_app_apply]
  simp only [Over.mk_hom]
  have hr : (ConcreteCategory.hom (R.obj.map (𝟙 U).op)) r = r := by
    rw [op_id, R.obj.map_id]
    rfl
  rw [smul_eq_mul]
  erw [hr]
  exact (mul_comm' r _).symm

/-- **[PAIR-1c]** Naturality of the evaluation: evaluating the restricted functional on the
restricted section is the restriction of the evaluation. -/
theorem evalSection_naturality (M : _root_.SheafOfModules R) {U V : Cᵒᵖ} (i : U ⟶ V)
    (φ : M.over U.unop ⟶ _root_.SheafOfModules.unit (R.over U.unop))
    (m : M.val.obj U) :
    evalSection R M V.unop (dualRestrict R M i φ) (M.val.map i m) =
      R.obj.map i (evalSection R M U.unop φ m) := by
  simp only [evalSection_eq]
  dsimp [dualRestrict, _root_.SheafOfModules.overMapUnitIso, _root_.SheafOfModules.overMap,
    _root_.SheafOfModules.pushforward, _root_.SheafOfModules.overFunctorMap]
  simp
  exact PresheafOfModules.naturality_apply φ.val
    ((Over.homMk i.unop (by
      show i.unop ≫ 𝟙 (Opposite.unop U) = 𝟙 (Opposite.unop V) ≫ i.unop
      simp) :
      (Over.map i.unop).obj (Over.mk (𝟙 (Opposite.unop V))) ⟶
        Over.mk (𝟙 (Opposite.unop U))).op) m

/-- **Factorization of the evaluation through a trivialization**: for an isomorphism
`ψ : M|ᵤ ≅ 𝒪|ᵤ` on the over-site, every functional is a scalar multiple of `ψ.hom`, and
the evaluation factors accordingly. -/
theorem evalSection_factor (M : _root_.SheafOfModules R) (U : C)
    [∀ V, IsMulCommutative (R.obj.obj V)]
    (ψ : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) (m : M.val.obj (op U)) :
    evalSection R M U φ m =
      dualUnitSectionsEquiv R U (ψ.inv ≫ φ) * evalSection R M U ψ.hom m := by
  have hφ : φ = ψ.hom ≫ (ψ.inv ≫ φ) := by rw [Iso.hom_inv_id_assoc]
  have hε : (ψ.inv ≫ φ) = overUnitScalarEnd R U (dualUnitSectionsEquiv R U (ψ.inv ≫ φ)) :=
    ((dualUnitSectionsEquiv R U).symm_apply_apply (ψ.inv ≫ φ)).symm
  calc evalSection R M U φ m
      = evalSection R M U (ψ.hom ≫ overUnitScalarEnd R U
          (dualUnitSectionsEquiv R U (ψ.inv ≫ φ))) m := by rw [← hε, ← hφ]
    _ = evalSection R M U (letI := dualSectionsModule R M U
          dualUnitSectionsEquiv R U (ψ.inv ≫ φ) • ψ.hom) m := rfl
    _ = dualUnitSectionsEquiv R U (ψ.inv ≫ φ) • evalSection R M U ψ.hom m :=
        evalSection_smul_left R M U ψ.hom _ m
    _ = dualUnitSectionsEquiv R U (ψ.inv ≫ φ) * evalSection R M U ψ.hom m := rfl


/-- Evaluation against (the hom of) a trivialization is bijective: it is the composite of
the section equivalences with the bijective sections-map of an isomorphism. -/
theorem bijective_evalSection_iso (M : _root_.SheafOfModules R) (U : C)
    (ψ : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) :
    Function.Bijective (fun m => evalSection R M U ψ.hom m) := by
  have hcomp : (fun m => evalSection R M U ψ.hom m) =
      (overUnitSectionEquiv R U).symm ∘
        (fun s => _root_.SheafOfModules.sectionsMap ψ.hom s) ∘
        (overSectionEquiv R M U) := rfl
  rw [hcomp]
  refine Function.Bijective.comp (Equiv.bijective _)
    (Function.Bijective.comp ?_ (Equiv.bijective _))
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun s => _root_.SheafOfModules.sectionsMap ψ.inv s, fun s => ?_, fun s => ?_⟩
  · show _root_.SheafOfModules.sectionsMap ψ.inv
      (_root_.SheafOfModules.sectionsMap ψ.hom s) = s
    rw [← _root_.SheafOfModules.sectionsMap_comp, Iso.hom_inv_id,
      _root_.SheafOfModules.sectionsMap_id]
  · show _root_.SheafOfModules.sectionsMap ψ.hom
      (_root_.SheafOfModules.sectionsMap ψ.inv s) = s
    rw [← _root_.SheafOfModules.sectionsMap_comp, Iso.inv_hom_id,
      _root_.SheafOfModules.sectionsMap_id]

end ModularCurves.SheafOfModules

namespace CategoryTheory.MonoidalCategory

universe v₂ u₂

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- The conjugation action of an endomorphism of the monoidal unit on an object. -/
def unitEndAct (s : 𝟙_ D ⟶ 𝟙_ D) (X : D) : X ⟶ X :=
  (λ_ X).inv ≫ s ▷ X ≫ (λ_ X).hom

theorem unitEndAct_naturality (s : 𝟙_ D ⟶ 𝟙_ D) {X Y : D} (f : X ⟶ Y) :
    unitEndAct s X ≫ f = f ≫ unitEndAct s Y := by
  simp only [unitEndAct, Category.assoc]
  rw [← leftUnitor_naturality, ← whisker_exchange_assoc, leftUnitor_inv_naturality_assoc]

theorem unitEndAct_unit (s : 𝟙_ D ⟶ 𝟙_ D) : unitEndAct s (𝟙_ D) = s := by
  show (λ_ (𝟙_ D)).inv ≫ s ▷ 𝟙_ D ≫ (λ_ (𝟙_ D)).hom = s
  rw [unitors_equal, rightUnitor_naturality, unitors_inv_equal, Iso.inv_hom_id_assoc]

theorem unitEndAct_tensor (s : 𝟙_ D ⟶ 𝟙_ D) (X Y : D) :
    unitEndAct s (X ⊗ Y) = unitEndAct s X ▷ Y := by
  simp only [unitEndAct, comp_whiskerRight, whiskerRight_tensor, leftUnitor_tensor_hom,
    leftUnitor_tensor_inv, Category.assoc, Iso.hom_inv_id_assoc]

/-- Conjugating the unit-endomorphism action along an isomorphism. -/
theorem unitEndAct_conj (s : 𝟙_ D ⟶ 𝟙_ D) {X Y : D} (k : X ≅ Y) :
    unitEndAct s Y = k.inv ≫ unitEndAct s X ≫ k.hom := by
  rw [unitEndAct_naturality s k.hom, Iso.inv_hom_id_assoc]

/-- An idempotent-producing split pair through the unit is two-sided, provided the
middle object is isomorphic to a ⊗-invertible one. -/
theorem comp_eq_id_of_comp_eq_id {P : D} (v : 𝟙_ D ⟶ P) (w : P ⟶ 𝟙_ D)
    (hwv : w ≫ v = 𝟙 P) {B' A' : D} (kP : P ≅ B') (e'' : B' ⊗ A' ≅ 𝟙_ D) :
    v ≫ w = 𝟙 (𝟙_ D) := by
  have h1 : unitEndAct (v ≫ w) P ≫ w = w := by
    rw [unitEndAct_naturality, unitEndAct_unit, ← Category.assoc, hwv, Category.id_comp]
  have hq : unitEndAct (v ≫ w) P = 𝟙 P := by
    calc unitEndAct (v ≫ w) P
        = unitEndAct (v ≫ w) P ≫ w ≫ v := by rw [hwv, Category.comp_id]
      _ = (unitEndAct (v ≫ w) P ≫ w) ≫ v := (Category.assoc _ _ _).symm
      _ = w ≫ v := by rw [h1]
      _ = 𝟙 P := hwv
  have hqB : unitEndAct (v ≫ w) B' = 𝟙 B' := by
    rw [unitEndAct_conj (v ≫ w) kP, hq, Category.id_comp, Iso.inv_hom_id]
  have hqBA : unitEndAct (v ≫ w) (B' ⊗ A') = 𝟙 (B' ⊗ A') := by
    rw [unitEndAct_tensor, hqB, id_whiskerRight]
  rw [← unitEndAct_unit (v ≫ w), unitEndAct_conj (v ≫ w) e'', hqBA,
    Category.id_comp, Iso.inv_hom_id]

/-- **Split pairs against an invertible object are two-sided:** if `A` is ⊗-invertible
and `a : 𝟙 ⟶ A`, `b : A ⟶ 𝟙` satisfy `a ≫ b = 𝟙`, then also `b ≫ a = 𝟙`.
(The heart of
"an invertible module with a unit pairing value is trivial": conjugate the idempotent
`b ≫ a` into `End (𝟙_)`, where the split property and invertibility force it to be the
identity.) -/
theorem whiskerRight_comp_eq_id_of_split {A B : D} (e : A ⊗ B ≅ 𝟙_ D)
    (e' : B ⊗ A ≅ 𝟙_ D) (a : 𝟙_ D ⟶ A) (b : A ⟶ 𝟙_ D)
    (hab : a ≫ b = 𝟙 (𝟙_ D)) : b ≫ a = 𝟙 A := by
  -- `tensorRight B` is faithful: composing with `tensorRight A` is isomorphic to `𝟭`
  haveI : (tensorRight B ⋙ tensorRight A).Faithful := by
    refine Functor.Faithful.of_iso (F := 𝟭 D) ?_
    have hcongr : tensorRight (𝟙_ D) ≅ tensorRight (B ⊗ A) :=
      NatIso.ofComponents (fun X => whiskerLeftIso X e'.symm) (by
        intro X Y f
        simp
        rw [← whiskerRight_tensor]
        have h2 : (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv = f ▷ 𝟙_ D := by
          rw [rightUnitor_inv_naturality, Iso.hom_inv_id_assoc]
        exact (congrArg (fun t => t ≫ Y ◁ e'.inv) h2).trans
          (whisker_exchange f e'.inv).symm)
    exact (rightUnitorNatIso D).symm ≪≫ hcongr ≪≫ tensorRightTensor B A
  haveI : (tensorRight B).Faithful :=
    Functor.Faithful.of_comp (tensorRight B) (tensorRight A)
  apply (tensorRight B).map_injective
  show (b ≫ a) ▷ B = 𝟙 A ▷ B
  have hvw : (e.inv ≫ b ▷ B) ≫ ((a ▷ B) ≫ e.hom) = 𝟙 (𝟙_ D) := by
    refine comp_eq_id_of_comp_eq_id (e.inv ≫ b ▷ B) ((a ▷ B) ≫ e.hom) ?_ (λ_ B) e'
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← comp_whiskerRight, hab, id_whiskerRight]
  have hba : (b ▷ B) ≫ (a ▷ B) = 𝟙 (A ⊗ B) := by
    have h2 := congrArg (fun t => e.hom ≫ t ≫ e.inv) hvw
    simpa [Category.assoc] using h2
  rw [comp_whiskerRight, hba, id_whiskerRight]

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The identity morphism on `X`'s structure sheaf viewed in `RingCat`, the sheafification
parameter that `Modules.monoidalCategory` is built from.  Named once here: it otherwise appears
verbatim six times inside `nonempty_tensorObj_iso_tensor`. -/
private abbrev ringSheafId (X : Scheme.{u}) :=
  𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
    Sheaf _ RingCat.{u}).obj

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

open ModularCurves.SheafOfModules in
/-- **[PAIR-2]** The evaluation morphism of presheaves: `M ⊗ᵖ M^∨ ⟶ 𝒪ₓ`,
pointwise the lift of the bilinear evaluation pairing. -/
noncomputable def evPre (M : X.Modules) :
    (M.val ⊗ (dualObj M).val :
      _root_.PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⟶
      𝟙_ (_root_.PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) where
  app U := ModuleCat.ofHom (TensorProduct.lift (by
    letI := dualSectionsModule X.ringCatSheaf M U.unop
    letI : SMulCommClass ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
        ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
        ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) :=
      ⟨fun a b c => by
        show a * (b * c) = b * (a * c)
        rw [← mul_assoc, mul_comm' a b, mul_assoc]⟩
    exact LinearMap.mk₂ ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
      (fun m φ => evalSection X.ringCatSheaf M U.unop φ m)
      (fun m m' φ => evalSection_add_right X.ringCatSheaf M U.unop φ m m')
      (fun r m φ => evalSection_smul_right X.ringCatSheaf M U.unop φ r m)
      (fun m φ ψ => evalSection_add_left X.ringCatSheaf M U.unop φ ψ m)
      (fun r m φ => evalSection_smul_left X.ringCatSheaf M U.unop φ r m)))
  naturality {U V} i := by
    refine ModuleCat.MonoidalCategory.tensor_ext (fun m φ => ?_)
    exact ModularCurves.SheafOfModules.evalSection_naturality X.ringCatSheaf M i φ m

/-- **[PAIR-2, sheaf level]** The evaluation morphism `M ⊗ M^∨ ⟶ 𝒪ₓ` on the sheafified
tensor: the sheafification of `evPre`, collapsed onto the unit by the counit. -/
noncomputable def ev (M : X.Modules) : tensorObj M (dualObj M) ⟶ unitObj X :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (evPre M) ≫
    (sheafifyValIso (unitObj X)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- **[CMP-T]** The hand-rolled sheafified tensor of `Picard/InvertibleSheaf.lean` agrees
with the localized monoidal tensor: `tensorObj M N ≅ M ⊗ N` — both are the sheafification
of the presheaf tensor of the underlying presheaves (`μIso` of the monoidal localization
functor + the counit identifications). -/
theorem nonempty_tensorObj_iso_tensor (M N : X.Modules) :
    letI := Modules.monoidalCategory X
    Nonempty (tensorObj M N ≅ M ⊗ N) := by
  letI := Modules.monoidalCategory X
  have eM : (Localization.Monoidal.toMonoidalCategory
      (L := _root_.PresheafOfModules.sheafification.{u}
        (ringSheafId X))
      (W := _root_.PresheafOfModules.sheafificationW.{u}
        (ringSheafId X))
      (Iso.refl _)).obj M.val ≅
      (M : LocalizedMonoidal
        (_root_.PresheafOfModules.sheafification.{u}
          (ringSheafId X))
        (_root_.PresheafOfModules.sheafificationW.{u}
          (ringSheafId X)) (Iso.refl _)) := sheafifyValIso M
  have eN : (Localization.Monoidal.toMonoidalCategory
      (L := _root_.PresheafOfModules.sheafification.{u}
        (ringSheafId X))
      (W := _root_.PresheafOfModules.sheafificationW.{u}
        (ringSheafId X))
      (Iso.refl _)).obj N.val ≅
      (N : LocalizedMonoidal
        (_root_.PresheafOfModules.sheafification.{u}
          (ringSheafId X))
        (_root_.PresheafOfModules.sheafificationW.{u}
          (ringSheafId X)) (Iso.refl _)) := sheafifyValIso N
  exact ⟨((tensorIso eM.symm eN.symm) ≪≫
    Functor.Monoidal.μIso (Localization.Monoidal.toMonoidalCategory
      (L := _root_.PresheafOfModules.sheafification.{u}
        (ringSheafId X))
      (W := _root_.PresheafOfModules.sheafificationW.{u}
        (ringSheafId X))
      (Iso.refl _)) M.val N.val).symm⟩

/-- **[CMP-U]** The hand-rolled unit of `Picard/InvertibleSheaf.lean` agrees with the
localized monoidal unit: `unitObj X ≅ 𝟙_ X.Modules`. -/
theorem nonempty_unitObj_iso_unit :
    letI := Modules.monoidalCategory X
    Nonempty ((unitObj X : X.Modules) ≅ 𝟙_ (X.Modules)) := by
  letI := Modules.monoidalCategory X
  exact ⟨(sheafifyValIso (unitObj X)).symm⟩

/-- **[PAIR-4b]** The evaluation on the unit module is an isomorphism: the presheaf-level
pairing is pointwise invertible (every endomorphism of the unit is a scalar), so the
sheafified evaluation is a composition of isomorphisms. -/
theorem isIso_ev_unitObj (Y : Scheme.{u}) : IsIso (ev (unitObj Y)) := by
  -- the dual-unit identification, cast to the clean clothing
  let hd : ((dualObj (unitObj Y)).val :
      _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ≅
      𝟙_ (_root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :=
    ModularCurves.SheafOfModules.dualUnitPresheafIso Y.ringCatSheaf
  -- the factorization of the presheaf evaluation
  have hfac : evPre (unitObj Y) =
      (tensorIso (Iso.refl ((unitObj Y).val :
        _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) hd).hom ≫
      (ρ_ ((unitObj Y).val :
        _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).hom := by
    ext1 V
    refine ModuleCat.MonoidalCategory.tensor_ext (fun r φ => ?_)
    have h2 := PresheafOfModules.tensorHom_app_tmul
      (T := Y.sheaf.obj) (𝟙 ((unitObj Y).val :
        _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))
      hd.hom V r φ
    have h1 : (ModuleCat.Hom.hom (((Iso.refl ((unitObj Y).val :
        _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⊗ᵢ hd).hom ≫
        (ρ_ ((unitObj Y).val :
          _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).hom).app V))
        (r ⊗ₜ[((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V)] φ) =
        (ModuleCat.Hom.hom ((ρ_ ((unitObj Y).val :
          _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).hom.app V))
          ((ConcreteCategory.hom ((𝟙 ((unitObj Y).val :
            _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⊗ₘ
              hd.hom).app V))
            (r ⊗ₜ[((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj V)] φ)) := rfl
    refine Eq.trans ?_ ((h1.trans (congrArg (fun z =>
      (ModuleCat.Hom.hom ((ρ_ ((unitObj Y).val :
        _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).hom.app V)) z)
      h2)).symm)
    show ModularCurves.SheafOfModules.evalSection Y.ringCatSheaf (unitObj Y)
        (Opposite.unop V) φ r =
      (ConcreteCategory.hom (hd.hom.app V)) φ • r
    have hφ : (ConcreteCategory.hom (hd.hom.app V)) φ =
        ModularCurves.SheafOfModules.dualUnitSectionsEquiv Y.ringCatSheaf
          (Opposite.unop V) φ := rfl
    exact Eq.trans (ModularCurves.SheafOfModules.evalSection_unit_mul Y.ringCatSheaf
      (Opposite.unop V) φ r)
      (congrArg (fun c => c * (show Y.ringCatSheaf.obj.obj V from r))
        ((ModularCurves.SheafOfModules.evalSection_unit_one Y.ringCatSheaf
          (Opposite.unop V) φ).trans
          (((ModularCurves.SheafOfModules.dualUnitSectionsEquiv_apply Y.ringCatSheaf
            (Opposite.unop V) φ).symm).trans hφ.symm)))
  let eTensor := tensorIso (Iso.refl ((unitObj Y).val :
    _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))) hd
  let eRight := ρ_ ((unitObj Y).val :
    _root_.PresheafOfModules (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  haveI : IsIso eTensor.hom := eTensor.isIso_hom
  haveI : IsIso eRight.hom := eRight.isIso_hom
  letI hEvPre : IsIso (evPre (unitObj Y)) := by
    rw [hfac]
    let eFac := eTensor ≪≫ eRight
    change IsIso eFac.hom
    exact eFac.isIso_hom
  dsimp only [ev]
  let ePre := @asIso _ _ _ _ (evPre (unitObj Y)) hEvPre
  exact IsIso.comp_isIso'
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso ePre).isIso_hom
    (sheafifyValIso (unitObj Y)).isIso_hom

/-- **[PAIR-4′]** On an open where `M` trivializes, the component of the presheaf
evaluation is bijective: conjugate the pairing by the trivialization and its induced
dual-trivialization; the conjugated pairing is the unit multiplication (the component
content of `isIso_ev_unitObj`). Section-level — no functor conjugation. -/
theorem bijective_evPre_app_of_triv {M : X.Modules} {W : X.Opens}
    (e : (Modules.pullback W.ι).obj M ≅ unitObj W.toScheme) :
    Function.Bijective ((evPre M).app (Opposite.op W)) := by
  letI := ModularCurves.SheafOfModules.dualSectionsModule X.ringCatSheaf M W
  -- the over-trivialization and the packaged bijective evaluation against it
  let ψ : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) :=
    overTrivializationOfRestrictIso M W ((restrictFunctorIsoPullback W.ι).app M ≪≫ e)
  let hL : M.val.obj (Opposite.op W) ≃ₗ[X.ringCatSheaf.obj.obj (Opposite.op W)]
      X.ringCatSheaf.obj.obj (Opposite.op W) :=
    LinearEquiv.ofBijective
      { toFun := fun m => ModularCurves.SheafOfModules.evalSection X.ringCatSheaf M W ψ.hom m
        map_add' := fun a b =>
          ModularCurves.SheafOfModules.evalSection_add_right X.ringCatSheaf M W ψ.hom a b
        map_smul' := fun c a =>
          ModularCurves.SheafOfModules.evalSection_smul_right X.ringCatSheaf M W ψ.hom c a }
      (ModularCurves.SheafOfModules.bijective_evalSection_iso X.ringCatSheaf M W ψ)
  letI : CommSemiring ↑(X.ringCatSheaf.obj.obj (Opposite.op W)) :=
    inferInstanceAs (CommSemiring ↑(X.sheaf.obj.obj (Opposite.op W)))
  letI : Module ↑(X.ringCatSheaf.obj.obj (Opposite.op W))
      ↑(M.val.obj (Opposite.op W)) :=
    inferInstanceAs (Module ↑(X.sheaf.obj.obj (Opposite.op W))
      ↑(M.val.obj (Opposite.op W)))
  letI : Module ↑(X.ringCatSheaf.obj.obj (Opposite.op W))
      ↑((dualObj M).val.obj (Opposite.op W)) :=
    inferInstanceAs (Module ↑(X.sheaf.obj.obj (Opposite.op W))
      ↑((dualObj M).val.obj (Opposite.op W)))
  -- the inverse component `c ↦ hL⁻¹ c ⊗ ψ.hom`, as a hom of module categories
  let k : (𝟙_ (_root_.PresheafOfModules
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).obj (Opposite.op W) ⟶
      (M.val ⊗ (dualObj M).val : _root_.PresheafOfModules
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op W) :=
    ModuleCat.ofHom
      (((TensorProduct.mk (X.ringCatSheaf.obj.obj (Opposite.op W))
        (M.val.obj (Opposite.op W)) ((dualObj M).val.obj (Opposite.op W))).flip ψ.hom) ∘ₗ
        hL.symm.toLinearMap)
  have hki : k ≫ (evPre M).app (Opposite.op W) = 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
    exact hL.apply_symm_apply c
  have hik : (evPre M).app (Opposite.op W) ≫ k = 𝟙 _ := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m φ => ?_
    have hc := ModularCurves.SheafOfModules.evalSection_factor X.ringCatSheaf M W ψ φ m
    -- the inverse image of the evaluation is the scalar times the section
    have hsm : hL.symm (ModularCurves.SheafOfModules.evalSection X.ringCatSheaf M W φ m) =
        ModularCurves.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf W (ψ.inv ≫ φ) • m :=
      hL.injective ((hL.apply_symm_apply _).trans (hc.trans
        ((_root_.map_smul hL _ m).trans (smul_eq_mul _ _)).symm))
    -- the scalar times the trivialization is the functional
    have hcψ : ModularCurves.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf W
        (ψ.inv ≫ φ) • ψ.hom = φ := by
      show ψ.hom ≫ ModularCurves.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W
        (ModularCurves.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf W (ψ.inv ≫ φ)) = φ
      exact (congrArg (fun t => ψ.hom ≫ t)
        ((ModularCurves.SheafOfModules.dualUnitSectionsEquiv
          X.ringCatSheaf W).symm_apply_apply (ψ.inv ≫ φ))).trans (Iso.hom_inv_id_assoc ψ φ)
    exact (congrArg (fun x => x ⊗ₜ[X.ringCatSheaf.obj.obj (Opposite.op W)] ψ.hom) hsm).trans
      ((TensorProduct.smul_tmul _ m ψ.hom).trans (congrArg (fun y => m ⊗ₜ y) hcψ))
  haveI : IsIso ((evPre M).app (Opposite.op W)) := ⟨k, hik, hki⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- **[CMP-PAIR]** For an invertible module the evaluation pairing against the sheaf dual
(consumed from `Picard/Dual.lean`) is an isomorphism onto the unit: the presheaf pairing
is bijective on every open inside the trivializing cover
(`bijective_evPre_app_of_triv` after `restrictTrivialization`), hence locally bijective,
hence inverted by the sheafification. -/
theorem nonempty_eval_iso {M : X.Modules} (hM : IsInvertible M) :
    Nonempty (tensorObj M (dualObj M) ≅ unitObj X) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  have hw : PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj) (evPre M) := by
    refine sheafificationW_of_bijective_on_cover (evPre M) U hU (fun i W hW => ?_)
    obtain ⟨e⟩ := htriv i
    exact bijective_evPre_app_of_triv (restrictTrivialization hW e)
  rw [PresheafOfModules.sheafificationW_iff] at hw
  haveI : IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (evPre M)) := hw
  haveI : IsIso (ev M) := by
    let eSheaf := asIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (evPre M))
    let eFinal := eSheaf ≪≫ sheafifyValIso (unitObj X)
    change IsIso eFinal.hom
    exact eFinal.isIso_hom
  exact ⟨asIso (ev M)⟩

/-- **[PIC-P2-CMP], → direction.** A cover-locally trivial module is ⊗-invertible: the
inverse class is the sheaf dual (`Picard/Dual.lean`), the unit isomorphism is the
evaluation pairing. -/
theorem IsInvertible.isUnit_toSkeleton {M : X.Modules} (hM : IsInvertible M) :
    letI := Modules.monoidalCategory X
    IsUnit (toSkeleton M) := by
  letI := Modules.monoidalCategory X
  letI := Modules.symmetricCategory X
  obtain ⟨epair⟩ := nonempty_eval_iso hM
  obtain ⟨eT⟩ := nonempty_tensorObj_iso_tensor M (dualObj M)
  obtain ⟨eU⟩ := nonempty_unitObj_iso_unit (X := X)
  refine isUnit_of_dvd_one ⟨toSkeleton (dualObj M), ?_⟩
  rw [← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
  exact Quotient.sound ⟨eU.symm ≪≫ epair.symm ≪≫ eT⟩

/-- **[CMP-L1]** Unfolding a ⊗-unit: a ⊗-inverse module together with an isomorphism
`M ⊗ N ≅ 𝒪ₓ` for the hand-rolled sheafified tensor (skeleton quotient unfold, then the
[CMP-T]/[CMP-U] bridges backwards). -/
theorem exists_tensorObj_iso_unitObj_of_isUnit_toSkeleton {M : X.Modules}
    (hM : letI := Modules.monoidalCategory X
      IsUnit (toSkeleton M)) :
    ∃ N : X.Modules, Nonempty (tensorObj M N ≅ unitObj X) := by
  letI := Modules.monoidalCategory X
  obtain ⟨v, hv, -⟩ := isUnit_iff_exists.mp hM
  refine ⟨(fromSkeleton X.Modules).obj v, ?_⟩
  rw [← toSkeleton_fromSkeleton_obj (C := X.Modules) v, ← Skeleton.toSkeleton_tensorObj,
    Skeleton.one_eq] at hv
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.mp hv
  obtain ⟨eT⟩ := nonempty_tensorObj_iso_tensor M ((fromSkeleton X.Modules).obj v)
  obtain ⟨eU⟩ := nonempty_unitObj_iso_unit (X := X)
  exact ⟨eT ≪≫ e ≪≫ eU.symm⟩

private noncomputable def tensorToSheafify (M N : X.Modules) :
    (M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) ⟶ (tensorObj M N).val := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app (M.val ⊗ N.val)

private theorem tensorToSheafify_app_apply (M N : X.Modules) (V : X.Opens)
    (t : (M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V)) :
    (tensorToSheafify M N).app (Opposite.op V) t =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥X)
        (M.val ⊗ N.val : _root_.PresheafOfModules
          (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).presheaf).app (Opposite.op V) t :=
  rfl

private theorem tensorObj_val_map_apply (M N : X.Modules) {V W : X.Opens}
    (i : Opposite.op V ⟶ Opposite.op W) (t : (tensorObj M N).val.obj (Opposite.op V)) :
    (tensorObj M N).val.map i t =
      (CategoryTheory.sheafify (Opens.grothendieckTopology ↥X)
        (M.val ⊗ N.val : _root_.PresheafOfModules
          (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).presheaf).map i t :=
  rfl

/-- The pairing of an isomorphism `ε : M ⊗ N ≅ 𝒪ₓ` on presheaf-tensor elements over an
open `V`: apply the sheafification unit, then `ε.hom`, landing in `𝒪(V)`. -/
noncomputable def pairingElem {M N : X.Modules} (ε : tensorObj M N ≅ unitObj X)
    (V : X.Opens)
    (t : ((M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V) :=
  ε.hom.val.app (Opposite.op V) ((tensorToSheafify M N).app (Opposite.op V) t)

/-- The pairing is additive. -/
theorem pairingElem_add {M N : X.Modules} (ε : tensorObj M N ≅ unitObj X) (V : X.Opens)
    (t t' : ((M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε V (t + t') = pairingElem ε V t + pairingElem ε V t' := by
  simp only [pairingElem, map_add]
  rfl

/-- The pairing is homogeneous (both layers are morphisms of modules). -/
theorem pairingElem_smul {M N : X.Modules} (ε : tensorObj M N ≅ unitObj X) (V : X.Opens)
    (c : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V))
    (t : ((M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε V (c • t) = c • pairingElem ε V t := by
  have h₁ := ((tensorToSheafify M N).app (Opposite.op V)).hom.map_smul c t
  have h₂ := (ε.hom.val.app (Opposite.op V)).hom.map_smul c
    ((tensorToSheafify M N).app (Opposite.op V) t)
  exact (congrArg (ε.hom.val.app (Opposite.op V)) h₁).trans h₂

/-- The pairing is additive (both layers are morphisms of modules). -/
theorem pairingElem_sum {M N : X.Modules} (ε : tensorObj M N ≅ unitObj X) (V : X.Opens)
    {ι : Type*} (s : Finset ι)
    (f : ι → ((M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε V (∑ i ∈ s, f i) = ∑ i ∈ s, pairingElem ε V (f i) := by
  simp only [pairingElem, map_sum]
  rfl

/-- The pairing commutes with restriction (naturality of both layers). -/
theorem pairingElem_map {M N : X.Modules} (ε : tensorObj M N ≅ unitObj X)
    {V W : X.Opens} (i : Opposite.op V ⟶ Opposite.op W)
    (t : ((M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op V))) :
    pairingElem ε W ((M.val ⊗ N.val : _root_.PresheafOfModules
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map i t) =
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map i (pairingElem ε V t) := by
  simp only [pairingElem]
  exact (congrArg (ε.hom.val.app (Opposite.op W))
    (PresheafOfModules.naturality_apply (tensorToSheafify M N) i t)).trans
    (PresheafOfModules.naturality_apply ε.hom.val i _)

/-- **[CMP-L2]** Around every point, an isomorphism `ε : M ⊗ N ≅ 𝒪ₓ` yields a section
pair whose pairing is exactly `1`: locally lift the `ε`-preimage of the unit section
through the sheafification, decompose the lift as a finite sum of pure tensors, use
locality of the stalk to find a summand with invertible pairing, then rescale. -/
theorem exists_pairingElem_tmul_eq_one {M N : X.Modules} (ε : tensorObj M N ≅ unitObj X)
    (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V) (m : M.val.obj (Opposite.op V))
      (n : N.val.obj (Opposite.op V)), pairingElem ε V (m ⊗ₜ n) = 1 := by
  classical
  -- the ε-preimage of the unit section
  set ζ := ε.inv.val.app (Opposite.op ⊤)
    (show (unitObj X).val.obj (Opposite.op ⊤) from
      (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))) with hζ
  -- locally lift ζ through the sheafification unit
  have hmem : Presheaf.imageSieve (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥X)
      (M.val ⊗ N.val : _root_.PresheafOfModules
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).presheaf) ζ ∈
      Opens.grothendieckTopology ↥X ⊤ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology ↥X)
        (M.val ⊗ N.val : _root_.PresheafOfModules
          (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).presheaf) (U := Opposite.op ⊤) ζ
  rw [Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V₀, iV₀, hlift, hxV₀⟩ := hmem x trivial
  obtain ⟨τ, hτ⟩ := hlift
  -- ε sends ζ back to the unit section
  have hcomp : ε.inv.val ≫ ε.hom.val = 𝟙 _ :=
    congrArg SheafOfModules.Hom.val ε.inv_hom_id
  have hεone : ε.hom.val.app (Opposite.op ⊤) ζ =
      (show (unitObj X).val.obj (Opposite.op ⊤) from
        (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))) := by
    rw [hζ]
    show (ConcreteCategory.hom ((ε.inv.val ≫ ε.hom.val).app (Opposite.op ⊤)))
      (show (unitObj X).val.obj (Opposite.op ⊤) from
        (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))) = _
    rw [hcomp]
    rfl
  -- the pairing of the lifted section is exactly 1
  have h1 : pairingElem ε V₀ τ = 1 := by
    show ε.hom.val.app (Opposite.op V₀)
      ((tensorToSheafify M N).app (Opposite.op V₀) τ) = _
    have h2 : (tensorToSheafify M N).app (Opposite.op V₀) τ =
        (tensorObj M N).val.map iV₀.op ζ := by
      exact (tensorToSheafify_app_apply M N V₀ τ).trans
        (hτ.trans (tensorObj_val_map_apply M N iV₀.op ζ).symm)
    refine (congrArg (ε.hom.val.app (Opposite.op V₀)) h2).trans
      ((PresheafOfModules.naturality_apply ε.hom.val iV₀.op ζ).trans
        ((congrArg (X.ringCatSheaf.obj.map iV₀.op) hεone).trans ?_))
    show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map iV₀.op
      (show (unitObj X).val.obj (Opposite.op ⊤) from
        (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))) = 1
    exact map_one (ConcreteCategory.hom
      ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map iV₀.op))
  -- decompose the lift as a finite sum of pure tensors
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset τ
  have h1' : (1 : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V₀)) =
      ∑ p ∈ S, pairingElem ε V₀ (p.1 ⊗ₜ p.2) :=
    (h1.symm.trans (congrArg (pairingElem ε V₀) hS)).trans (pairingElem_sum ε V₀ S _)
  -- some summand has a pairing with invertible germ at x
  have hpigeon : ∃ p ∈ S,
      IsUnit (X.presheaf.germ V₀ x hxV₀ (pairingElem ε V₀ (p.1 ⊗ₜ p.2))) := by
    by_contra hall
    push Not at hall
    have hnon : X.presheaf.germ V₀ x hxV₀
        (∑ p ∈ S, pairingElem ε V₀ (p.1 ⊗ₜ p.2)) ∈ nonunits (X.presheaf.stalk x) := by
      rw [map_sum]
      refine Finset.sum_induction _ (· ∈ nonunits _)
        (fun a b ha hb => IsLocalRing.nonunits_add ha hb)
        (zero_mem_nonunits.mpr zero_ne_one) (fun p hp => mem_nonunits_iff.mpr (hall p hp))
    let a : X.presheaf.obj (Opposite.op V₀) :=
      ∑ p ∈ S, pairingElem ε V₀ (p.1 ⊗ₜ p.2)
    have ha : (1 : X.presheaf.obj (Opposite.op V₀)) = a := h1'
    have hnonA : X.presheaf.germ V₀ x hxV₀ a ∈ nonunits (X.presheaf.stalk x) := by
      simpa only [a] using hnon
    have hga : X.presheaf.germ V₀ x hxV₀ a = 1 := by
      rw [← map_one (ConcreteCategory.hom (X.presheaf.germ V₀ x hxV₀)), ha]
    exact (mem_nonunits_iff.mp hnonA) (hga ▸ isUnit_one)
  obtain ⟨p, hpS, hpu⟩ := hpigeon
  -- the unit germ restricts to a unit on a smaller open
  obtain ⟨V, iV, hxV, hu⟩ :=
    X.toLocallyRingedSpace.toRingedSpace.isUnit_res_of_isUnit_germ V₀
      (pairingElem ε V₀ (p.1 ⊗ₜ p.2)) x hxV₀ hpu
  obtain ⟨b, hb⟩ := hu.exists_left_inv
  let c : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V) := b
  let m₁ : M.val.obj (Opposite.op V) := M.val.map iV.op p.1
  let n₁ : N.val.obj (Opposite.op V) := N.val.map iV.op p.2
  letI : Module ↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V))
      ↑(M.val.obj (Opposite.op V)) :=
    inferInstanceAs (Module ↑(X.ringCatSheaf.obj.obj (Opposite.op V))
      ↑(M.val.obj (Opposite.op V)))
  letI : Module ↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V))
      ↑(N.val.obj (Opposite.op V)) :=
    inferInstanceAs (Module ↑(X.ringCatSheaf.obj.obj (Opposite.op V))
      ↑(N.val.obj (Opposite.op V)))
  refine ⟨V, hxV, m₁, c • n₁, ?_⟩
  -- rescaling computation
  have hbal : m₁ ⊗ₜ[
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)]
        (c • n₁) =
      c • (m₁ ⊗ₜ[
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁) :=
    TensorProduct.tmul_smul _ _ _
  have hres : pairingElem ε V
        (m₁ ⊗ₜ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁) =
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map iV.op
        (pairingElem ε V₀ (p.1 ⊗ₜ p.2)) :=
    (congrArg (pairingElem ε V)
      (PresheafOfModules.Monoidal.tensorObj_map_tmul iV.op p.1 p.2).symm).trans
      (pairingElem_map ε iV.op (p.1 ⊗ₜ p.2))
  have hsm := pairingElem_smul ε V c
    (m₁ ⊗ₜ[
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁)
  calc pairingElem ε V
        (m₁ ⊗ₜ[
          (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] (c • n₁))
      = pairingElem ε V (c •
          (m₁ ⊗ₜ[
            (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁)) :=
        congrArg (pairingElem ε V) hbal
    _ = c • pairingElem ε V
          (m₁ ⊗ₜ[
            (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)] n₁) := hsm
    _ = c • (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map iV.op
          (pairingElem ε V₀ (p.1 ⊗ₜ p.2)) :=
        congrArg (c • ·) hres
    _ = 1 := (smul_eq_mul c _).trans hb

open ModularCurves.SheafOfModules in
/-- **[CMP-L3a]** Pairing against a fixed section `n` of `N`, as a morphism on the
over-site: componentwise `s ↦ ⟨s ⊗ n|_V⟩` for the pairing of `ε`. -/
noncomputable def pairingHom {M N : X.Modules} (ε : tensorObj M N ≅ unitObj X)
    {W : X.Opens} (n : N.val.obj (Opposite.op W)) :
    M.over W ⟶ SheafOfModules.unit (X.ringCatSheaf.over W) := by
  let component (Vf : (Over W)ᵒᵖ) :
      (M.over W).val.obj Vf ⟶
        (SheafOfModules.unit (X.ringCatSheaf.over W)).val.obj Vf := by
    letI : Module ↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(M.val.obj (Opposite.op (Opposite.unop Vf).left)) :=
      inferInstanceAs (Module ↑(X.ringCatSheaf.obj.obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(M.val.obj (Opposite.op (Opposite.unop Vf).left)))
    letI : Module ↑((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(N.val.obj (Opposite.op (Opposite.unop Vf).left)) :=
      inferInstanceAs (Module ↑(X.ringCatSheaf.obj.obj
        (Opposite.op (Opposite.unop Vf).left))
        ↑(N.val.obj (Opposite.op (Opposite.unop Vf).left)))
    exact ConcreteCategory.ofHom
      ((ε.hom.val.app (Opposite.op (Opposite.unop Vf).left)).hom.comp
        (((tensorToSheafify M N).app (Opposite.op (Opposite.unop Vf).left)).hom.comp
          ((TensorProduct.mk
            ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
              (Opposite.op (Opposite.unop Vf).left))
            (M.val.obj (Opposite.op (Opposite.unop Vf).left))
            (N.val.obj (Opposite.op (Opposite.unop Vf).left))).flip
              (N.val.map (Opposite.unop Vf).hom.op n))))
  refine ⟨{ app := component, naturality := fun {Vf Vf'} i => ?_ }⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  have hw : i.unop.left ≫ (Opposite.unop Vf).hom = (Opposite.unop Vf').hom :=
    Over.w i.unop
  have h₁ : N.val.map ((Opposite.unop Vf').hom).op n =
      N.val.map (i.unop.left).op (N.val.map ((Opposite.unop Vf).hom).op n) := by
    show N.val.presheaf.map ((Opposite.unop Vf').hom).op n =
      N.val.presheaf.map (i.unop.left).op
        (N.val.presheaf.map ((Opposite.unop Vf).hom).op n)
    rw [← hw, op_comp, Functor.map_comp]
    rfl
  simp only [ModuleCat.comp_apply, ModuleCat.restrictScalars.map_apply]
  have hM : (M.over W).val.map i s = M.val.map (i.unop.left).op s := rfl
  have hO : (SheafOfModules.unit (X.ringCatSheaf.over W)).val.map i (component Vf s) =
      (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (i.unop.left).op
        (component Vf s) := rfl
  rw [hM, hO]
  change pairingElem ε (Opposite.unop Vf').left
      ((M.val.map (i.unop.left).op s) ⊗ₜ N.val.map ((Opposite.unop Vf').hom).op n) =
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (i.unop.left).op
      (pairingElem ε (Opposite.unop Vf).left
        (s ⊗ₜ N.val.map ((Opposite.unop Vf).hom).op n))
  refine (congrArg (fun t => pairingElem ε (Opposite.unop Vf').left
      ((M.val.map (i.unop.left).op s) ⊗ₜ t)) h₁).trans ?_
  refine (congrArg (pairingElem ε (Opposite.unop Vf').left)
      (PresheafOfModules.Monoidal.tensorObj_map_tmul (i.unop.left).op s
        (N.val.map ((Opposite.unop Vf).hom).op n)).symm).trans ?_
  exact pairingElem_map ε (i.unop.left).op _

open ModularCurves.SheafOfModules in
/-- **[CMP-L3b]** When the pairing value of `(m, n)` is `1`, multiplication by `m`
splits the pairing against `n`: the composite on the over-site is the identity of the
unit. -/
theorem unitHomEquiv_symm_overSection_comp_pairingHom {M N : X.Modules}
    (ε : tensorObj M N ≅ unitObj X) {W : X.Opens} (m : M.val.obj (Opposite.op W))
    (n : N.val.obj (Opposite.op W)) (h1 : pairingElem ε W (m ⊗ₜ n) = 1) :
    (M.over W).unitHomEquiv.symm (overSection X.ringCatSheaf M W m) ≫ pairingHom ε n =
      𝟙 (SheafOfModules.unit (X.ringCatSheaf.over W)) := by
  refine (SheafOfModules.unitHomEquiv_symm_comp (overSection X.ringCatSheaf M W m)
    (pairingHom ε n)).trans ?_
  refine Eq.trans
    (congrArg (SheafOfModules.unit (X.ringCatSheaf.over W)).unitHomEquiv.symm ?_)
    (Equiv.symm_apply_apply _ (𝟙 _))
  refine PresheafOfModules.sections_ext _ _ (fun V => ?_)
  rw [show (SheafOfModules.sectionsMap (pairingHom ε n)
      (overSection X.ringCatSheaf M W m)).val V =
      (pairingHom ε n).val.app V ((overSection X.ringCatSheaf M W m).val V) from rfl,
    SheafOfModules.unitHomEquiv_apply_coe]
  change (pairingHom ε n).val.app V (M.val.map (Opposite.unop V).hom.op m) = _
  change pairingElem ε (Opposite.unop V).left
      ((M.val.map (Opposite.unop V).hom.op m) ⊗ₜ
        N.val.map (Opposite.unop V).hom.op n) = _
  exact (congrArg (pairingElem ε (Opposite.unop V).left)
      (PresheafOfModules.Monoidal.tensorObj_map_tmul
        ((Opposite.unop V).hom).op m n).symm).trans
    ((pairingElem_map ε ((Opposite.unop V).hom).op (m ⊗ₜ n)).trans
      ((congrArg ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map
          ((Opposite.unop V).hom).op) h1).trans
        (map_one (ConcreteCategory.hom ((X.sheaf.obj ⋙ forget₂ CommRingCat
          RingCat).map ((Opposite.unop V).hom).op)))))

open ModularCurves.SheafOfModules in
/-- **[CMP-L3]** A section pair with pairing value `1` trivializes `M` on `W`:
pair-with-`n` and multiply-by-`m` are transported through the over-site equivalence and
are mutually inverse — one composite by the sections computation, the other by the
generic monoidal split-pair cancellation against the ⊗-invertibility supplied by `ε`. -/
theorem nonempty_pullback_iso_unitObj_of_pairingElem {M N : X.Modules}
    (ε : tensorObj M N ≅ unitObj X) {W : X.Opens} (m : M.val.obj (Opposite.op W))
    (n : N.val.obj (Opposite.op W))
    (h1 : pairingElem ε W (m ⊗ₜ n) = 1) :
    Nonempty ((Modules.pullback W.ι).obj M ≅ unitObj ↑W) := by
  letI := Modules.monoidalCategory (↑W : Scheme.{u})
  letI := Modules.symmetricCategory (↑W : Scheme.{u})
  -- the transported split pair
  let α : SheafOfModules.unit (X.ringCatSheaf.over W) ⟶ M.over W :=
    (M.over W).unitHomEquiv.symm (overSection X.ringCatSheaf M W m)
  let β : M.over W ⟶ SheafOfModules.unit (X.ringCatSheaf.over W) := pairingHom ε n
  let eM : (overEquiv W).functor.obj (M.over W) ≅ (Modules.pullback W.ι).obj M :=
    (overFunctorEquiv W).app M ≪≫ (restrictFunctorIsoPullback W.ι).app M
  let eO : (overEquiv W).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over W)) ≅
      unitObj ↑W := W.sheafOfModulesEquivOverUnit X.ringCatSheaf
  let αs : unitObj ↑W ⟶ (Modules.pullback W.ι).obj M :=
    eO.inv ≫ (overEquiv W).functor.map α ≫ eM.hom
  let βs : (Modules.pullback W.ι).obj M ⟶ unitObj ↑W :=
    eM.inv ≫ (overEquiv W).functor.map β ≫ eO.hom
  have hαβs : αs ≫ βs = 𝟙 (unitObj ↑W) := by
    show (eO.inv ≫ (overEquiv W).functor.map α ≫ eM.hom) ≫
      (eM.inv ≫ (overEquiv W).functor.map β ≫ eO.hom) = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc,
      unitHomEquiv_symm_overSection_comp_pairingHom ε m n h1,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  -- ⊗-invertibility of the pullback, and the cancellation
  obtain ⟨ePT⟩ := nonempty_pullback_tensorObj W.ι M N
  obtain ⟨eT⟩ := nonempty_tensorObj_iso_tensor
    ((Modules.pullback W.ι).obj M) ((Modules.pullback W.ι).obj N)
  obtain ⟨eU⟩ := nonempty_unitObj_iso_unit (X := (↑W : Scheme.{u}))
  let e : ((Modules.pullback W.ι).obj M ⊗ (Modules.pullback W.ι).obj N :
      (↑W : Scheme.{u}).Modules) ≅ 𝟙_ ((↑W : Scheme.{u}).Modules) :=
    eT.symm ≪≫ ePT.symm ≪≫ (Modules.pullback W.ι).mapIso ε ≪≫
      pullbackUnitIso W.ι ≪≫ eU
  let e' : ((Modules.pullback W.ι).obj N ⊗ (Modules.pullback W.ι).obj M :
      (↑W : Scheme.{u}).Modules) ≅ 𝟙_ ((↑W : Scheme.{u}).Modules) :=
    (β_ ((Modules.pullback W.ι).obj N) ((Modules.pullback W.ι).obj M)) ≪≫ e
  have hab : (eU.inv ≫ αs) ≫ (βs ≫ eU.hom) =
      𝟙 (𝟙_ ((↑W : Scheme.{u}).Modules)) := by
    simp only [Category.assoc]
    rw [← Category.assoc αs βs, hαβs, Category.id_comp, Iso.inv_hom_id]
  have hba := CategoryTheory.MonoidalCategory.whiskerRight_comp_eq_id_of_split e e'
    (eU.inv ≫ αs) (βs ≫ eU.hom) hab
  have hβαs : βs ≫ αs = 𝟙 ((Modules.pullback W.ι).obj M) := by
    have h3 : (βs ≫ eU.hom) ≫ (eU.inv ≫ αs) = βs ≫ αs := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact h3.symm.trans hba
  exact ⟨⟨βs, αs, hβαs, hαβs⟩⟩

/-- **[CMP-←]** A ⊗-invertible module is cover-locally trivial (Zariski-local freeness:
around every point a pure-tensor decomposition of the unit section exhibits, over the
local ring at the point, a unit pairing value, and rescaling gives a section pair with
pairing exactly 1 on a neighbourhood, which trivializes `M` there). -/
theorem isInvertible_of_isUnit_toSkeleton {M : X.Modules}
    (hM : letI := Modules.monoidalCategory X
      IsUnit (toSkeleton M)) :
    IsInvertible M := by
  obtain ⟨N, ⟨ε⟩⟩ := exists_tensorObj_iso_unitObj_of_isUnit_toSkeleton hM
  choose V hxV m n h1 using fun x => exists_pairingElem_tmul_eq_one ε x
  refine ⟨↥X, V, ?_, fun x => ?_⟩
  · rw [eq_top_iff]
    exact fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  · exact nonempty_pullback_iso_unitObj_of_pairingElem ε (m x) (n x) (h1 x)

/-- **[PIC-P2-CMP] (GME 2.2.2 (2.17)): the formation of an invertible sheaf is local** —
cover-local invertibility agrees with ⊗-invertibility in `Pic X`'s ambient monoid. -/
theorem isInvertible_iff_isUnit_toSkeleton (M : X.Modules) :
    letI := Modules.monoidalCategory X
    (IsInvertible M ↔ IsUnit (toSkeleton M)) :=
  ⟨fun hM => hM.isUnit_toSkeleton, fun hM => isInvertible_of_isUnit_toSkeleton hM⟩

end AlgebraicGeometry.Scheme.Modules
