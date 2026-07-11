/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.Dual
import ModularCurves.Picard.PullbackTensorObj

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
    ((Over.homMk i.unop (by show i.unop ≫ 𝟙 (Opposite.unop U) = 𝟙 (Opposite.unop V) ≫ i.unop; simp) :
      (Over.map i.unop).obj (Over.mk (𝟙 (Opposite.unop V))) ⟶
        Over.mk (𝟙 (Opposite.unop U))).op) m

end ModularCurves.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

open ModularCurves.SheafOfModules in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[PAIR-2, sheaf level]** The evaluation morphism `M ⊗ M^∨ ⟶ 𝒪ₓ` on the sheafified
tensor: the sheafification of `evPre`, collapsed onto the unit by the counit. -/
noncomputable def ev (M : X.Modules) : tensorObj M (dualObj M) ⟶ unitObj X :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (evPre M) ≫
    (sheafifyValIso (unitObj X)).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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
        (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj))
      (W := _root_.PresheafOfModules.sheafificationW.{u}
        (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj))
      (Iso.refl _)).obj M.val ≅
      (M : LocalizedMonoidal
        (_root_.PresheafOfModules.sheafification.{u}
          (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
            Sheaf _ RingCat.{u}).obj))
        (_root_.PresheafOfModules.sheafificationW.{u}
          (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
            Sheaf _ RingCat.{u}).obj)) (Iso.refl _)) := sheafifyValIso M
  have eN : (Localization.Monoidal.toMonoidalCategory
      (L := _root_.PresheafOfModules.sheafification.{u}
        (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj))
      (W := _root_.PresheafOfModules.sheafificationW.{u}
        (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj))
      (Iso.refl _)).obj N.val ≅
      (N : LocalizedMonoidal
        (_root_.PresheafOfModules.sheafification.{u}
          (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
            Sheaf _ RingCat.{u}).obj))
        (_root_.PresheafOfModules.sheafificationW.{u}
          (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
            Sheaf _ RingCat.{u}).obj)) (Iso.refl _)) := sheafifyValIso N
  exact ⟨((tensorIso eM.symm eN.symm) ≪≫
    Functor.Monoidal.μIso (Localization.Monoidal.toMonoidalCategory
      (L := _root_.PresheafOfModules.sheafification.{u}
        (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj))
      (W := _root_.PresheafOfModules.sheafificationW.{u}
        (𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
          Sheaf _ RingCat.{u}).obj))
      (Iso.refl _)) M.val N.val).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[CMP-U]** The hand-rolled unit of `Picard/InvertibleSheaf.lean` agrees with the
localized monoidal unit: `unitObj X ≅ 𝟙_ X.Modules`. -/
theorem nonempty_unitObj_iso_unit :
    letI := Modules.monoidalCategory X
    Nonempty ((unitObj X : X.Modules) ≅ 𝟙_ (X.Modules)) := by
  letI := Modules.monoidalCategory X
  exact ⟨(sheafifyValIso (unitObj X)).symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[PAIR-3 / CMP-LOC]** Being an isomorphism of `𝒪ₓ`-modules is Zariski-local: a
morphism whose restriction to every member of an open cover is an isomorphism is an
isomorphism. (Route: cover-local isomorphy makes the underlying presheaf map locally
bijective, hence a `sheafificationW`-member, hence inverted by sheafification — and
sheaves are local objects for the sheafification.) -/
theorem isIso_of_isIso_restrict {A B : X.Modules} (g : A ⟶ B) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, IsIso ((restrictFunctor (U i).ι).map g)) : IsIso g := by
  -- Step 1: the section maps inside cover members are bijective
  have happ : ∀ (i : ι) (W : X.Opens), W ≤ U i → IsIso (g.app W) := by
    intro i W hW
    have h1 := Hom.isIso_iff_isIso_app.mp (h i) ((U i).ι ⁻¹ᵁ W)
    have h2 : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W) = W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hW]
    rw [← h2]
    exact h1
  have hbij : ∀ (i : ι) (W : X.Opens), W ≤ U i →
      Function.Bijective (g.app W) := by
    intro i W hW
    haveI := happ i W hW
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  -- Step 2: the cover-sieve is covering
  have hsieve : ∀ (V : (TopologicalSpace.Opens ↥X)ᵒᵖ) (S : Sieve V.unop),
      (∀ (i : ι) (W : X.Opens) (hWi : W ≤ U i) (hWV : W ≤ V.unop), S (homOfLE hWV)) →
      S ∈ Opens.grothendieckTopology ↥X V.unop := by
    intro V S hS
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have hxT : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxT
    exact ⟨V.unop ⊓ U i, homOfLE inf_le_left,
      hS i (V.unop ⊓ U i) inf_le_right inf_le_left, ⟨hx, hi⟩⟩
  -- Step 3: locally bijective
  haveI hinj : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf _).map g.val) := by
    constructor
    intro V x y hxy
    refine hsieve V _ (fun i W hWi hWV => ?_)
    refine (hbij i W hWi).injective ?_
    have hnx := PresheafOfModules.naturality_apply g.val (homOfLE hWV).op x
    have hny := PresheafOfModules.naturality_apply g.val (homOfLE hWV).op y
    calc g.app W (A.val.map (homOfLE hWV).op x)
        = B.val.map (homOfLE hWV).op (g.val.app V x) := hnx
      _ = B.val.map (homOfLE hWV).op (g.val.app V y) := by rw [show g.val.app V x =
            g.val.app V y from hxy]
      _ = g.app W (A.val.map (homOfLE hWV).op y) := hny.symm
  haveI hsurj : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf _).map g.val) := by
    constructor
    intro V s
    refine hsieve (Opposite.op V) _ (fun i W hWi hWV => ?_)
    obtain ⟨t, ht⟩ := (hbij i W hWi).surjective (B.val.map (homOfLE hWV).op s)
    exact ⟨t, ht⟩
  -- Step 4: the sheafification inverts g.val, and g is conjugate to it by the counit
  have hw : PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj) g.val :=
    (PresheafOfModules.sheafificationW_iff_isLocallyBijective _ g.val).mpr ⟨hinj, hsurj⟩
  rw [PresheafOfModules.sheafificationW_iff] at hw
  have hnat := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).counit.naturality g
  have hg : g = (sheafifyValIso A).inv ≫
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g.val ≫
      (sheafifyValIso B).hom := by
    rw [Iso.eq_inv_comp]
    exact hnat.symm
  rw [hg]
  haveI : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map g.val) := hw
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[CMP-PAIR]** For an invertible module the evaluation pairing against the sheaf dual
(consumed from `Picard/Dual.lean`) is an isomorphism onto the unit: on a trivializing open
both factors are trivial and the pairing is the multiplication; the isomorphism property
of the global evaluation morphism is Zariski-local (`isIso_of_isIso_restrict`). -/
theorem nonempty_eval_iso {M : X.Modules} (hM : IsInvertible M) :
    Nonempty (tensorObj M (dualObj M) ≅ unitObj X) := by
  sorry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[CMP-←]** A ⊗-invertible module is cover-locally trivial (Zariski-local freeness:
the stalks of a ⊗-unit are invertible modules over local rings, hence free of rank one,
and a generator spreads out to a trivialization on an open neighbourhood). -/
theorem isInvertible_of_isUnit_toSkeleton {M : X.Modules}
    (hM : letI := Modules.monoidalCategory X
      IsUnit (toSkeleton M)) :
    IsInvertible M := by
  sorry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[PIC-P2-CMP] (GME 2.2.2 (2.17)): the formation of an invertible sheaf is local** —
cover-local invertibility agrees with ⊗-invertibility in `Pic X`'s ambient monoid. -/
theorem isInvertible_iff_isUnit_toSkeleton (M : X.Modules) :
    letI := Modules.monoidalCategory X
    (IsInvertible M ↔ IsUnit (toSkeleton M)) :=
  ⟨fun hM => hM.isUnit_toSkeleton, fun hM => isInvertible_of_isUnit_toSkeleton hM⟩

end AlgebraicGeometry.Scheme.Modules
