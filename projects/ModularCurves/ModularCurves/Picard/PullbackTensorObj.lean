/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.PullbackTensorGeneral

/-!
# Pullback commutes with the sheafified tensor (general morphisms)

The general-`f` closure of `[PIC-P1b-MONO]`'s last registered leaf, relocated from
`Picard/InvertibleSheaf.lean` (which cannot import the monoidal-pullback machinery — the
import chain runs the other way): for any morphism of schemes `f : Y ⟶ X` and
`𝒪ₓ`-modules `M, N`,

`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`

for the sheafified tensor `tensorObj` of `Picard/InvertibleSheaf.lean`. Assembled from
mathlib's `sheafificationCompPullback` (the pullback of a sheafification), the tensorator
of the monoidal presheaf pullback (`PresheafOfModules.pullbackMonoidal` — the
`[D-PresPB′-general]` payoff), and the double-sheafification collapse
`nonempty_sheafify_tensor_idem` (the D-Idem leaf).
-/

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Bridging instance: the monoidal structure on presheaves of modules over the
`sheafToPresheaf`-spelled underlying presheaf of the ring sheaf (the clothing produced by
`Sheaf.Hom.hom`-projections), transported from the `CommRingCat`-derived clothing. -/
noncomputable instance (X : Scheme.{u}) : MonoidalCategory
    (_root_.PresheafOfModules.{u}
      ((sheafToPresheaf (Opens.grothendieckTopology ↥X) RingCat).obj
        X.ringCatSheaf)) :=
  inferInstanceAs (MonoidalCategory
    (_root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)))

set_option backward.isDefEq.respectTransparency.types false in
/-- The pullback of a sheaf of modules is the sheafification of the presheaf pullback of
its underlying presheaf (`sheafificationCompPullback`, precomposed with the counit
identification `sh(M.val) ≅ M`). -/
noncomputable def pullbackIsoSheafifyPresheafPullback (f : Y ⟶ X) (M : X.Modules) :
    (Modules.pullback f).obj M ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val) :=
  (Modules.pullback f).mapIso (sheafifyValIso M).symm ≪≫
    (SheafOfModules.sheafificationCompPullback.{u} f.toRingCatSheafHom).app M.val

set_option backward.isDefEq.respectTransparency.types false in
/-- **(GAP-1 downstream core, general `f`, closed.)** Pullback commutes with the
sheafified tensor: `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`. Relocated from
`Picard/InvertibleSheaf.lean` and proved: express both sides through the sheafification
of the presheaf pullback (`pullbackIsoSheafifyPresheafPullback`), apply the tensorator of
the monoidal presheaf pullback, and collapse the double sheafification
(`nonempty_sheafify_tensor_idem`). -/
theorem nonempty_pullback_tensorObj (f : Y ⟶ X) (M N : X.Modules) :
    Nonempty ((Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Modules.pullback f).obj M) ((Modules.pullback f).obj N)) := by
  -- E1: the pullback of the sheafified tensor is the sheafification of the presheaf
  -- pullback of the presheaf tensor
  have E1 : (Modules.pullback f).obj (tensorObj M N) ≅
      (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj (M.val ⊗ N.val)) :=
    (SheafOfModules.sheafificationCompPullback.{u} f.toRingCatSheafHom).app (M.val ⊗ N.val)
  -- E2: the tensorator of the monoidal presheaf pullback, already packaged as
  -- `nonempty_sheafify_presheafPullback_tensor` (same statement, `CommRingCat`-derived
  -- clothing — definitionally the spelling used here)
  obtain ⟨E2⟩ := nonempty_sheafify_presheafPullback_tensor f M.val N.val
  -- E3: collapse the double sheafification (the D-Idem leaf)
  obtain ⟨E3⟩ := _root_.PresheafOfModules.nonempty_sheafify_tensor_idem
    Y.sheaf.obj Y.ringCatSheaf.property
    ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val)
    ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj N.val)
  -- E4: identify the sheafified factors with the pullbacks
  have E4 : tensorObj
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val))
      ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj N.val)) ≅
      tensorObj ((Modules.pullback f).obj M) ((Modules.pullback f).obj N) :=
    tensorObjCongr (pullbackIsoSheafifyPresheafPullback f M).symm
      (pullbackIsoSheafifyPresheafPullback f N).symm
  exact ⟨E1 ≪≫ E2 ≪≫ E3 ≪≫ E4⟩

end AlgebraicGeometry.Scheme.Modules
