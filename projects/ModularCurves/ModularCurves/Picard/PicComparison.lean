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

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

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
