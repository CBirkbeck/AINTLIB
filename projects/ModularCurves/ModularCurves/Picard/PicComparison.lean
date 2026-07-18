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

/-- The identity morphism on `X`'s structure sheaf viewed in `RingCat`, the sheafification
parameter that `Modules.monoidalCategory` is built from.  Named once here: it otherwise appears
verbatim six times inside `nonempty_tensorObj_iso_tensor`. -/
private abbrev ringSheafId (X : Scheme.{u}) :=
  𝟙 (⟨X.sheaf.obj ⋙ forget₂ CommRingCat RingCat, X.ringCatSheaf.property⟩ :
    Sheaf _ RingCat.{u}).obj

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[CMP-PAIR]** For an invertible module the evaluation pairing against the sheaf dual
(consumed from `Picard/Dual.lean`) is an isomorphism onto the unit: on a trivializing open
both factors are trivial and the pairing is the multiplication; the isomorphism property
of the global evaluation morphism is Zariski-local. -/
theorem nonempty_eval_iso {M : X.Modules} (hM : IsInvertible M) :
    Nonempty (tensorObj M (dualObj M) ≅ unitObj X) := by
  sorry

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

/-- **[PIC-P2-CMP] (GME 2.2.2 (2.17)): the formation of an invertible sheaf is local** —
cover-local invertibility agrees with ⊗-invertibility in `Pic X`'s ambient monoid. -/
theorem isInvertible_iff_isUnit_toSkeleton (M : X.Modules) :
    letI := Modules.monoidalCategory X
    (IsInvertible M ↔ IsUnit (toSkeleton M)) :=
  ⟨fun hM => hM.isUnit_toSkeleton, fun hM => isInvertible_of_isUnit_toSkeleton hM⟩

end AlgebraicGeometry.Scheme.Modules
