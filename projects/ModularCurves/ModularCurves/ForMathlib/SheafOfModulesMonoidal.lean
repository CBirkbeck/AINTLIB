/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Towards the monoidal structure on sheaves of modules ([GAP1-W-MONO])

The AINTLIB ModularCurves GAP-1 development, route (b′) (board v10.64/v10.65): equip
`SheafOfModules` with a monoidal structure by localizing the monoidal category of
presheaves of modules at the class of morphisms inverted by sheafification, via
mathlib's `LocalizedMonoidal` machinery. The single load-bearing mathematical leaf is
tensor-stability of that class; everything else is registration plumbing.

* `PresheafOfModules.sheafificationW`: the inverted class.
* `sheafificationW_isLocalization`: the `IsLocalization` registration at `α = 𝟙`
  (reflective case), via `Adjunction.isLocalization`.
* `sheafificationW_iff_isLocallyBijective`: membership = locally injective + locally
  surjective on underlying presheaves of abelian groups (through mathlib's
  `WEqualsLocallyBijective` and the reflection of isomorphisms by `toSheaf`).
* `[GAP1-W-MONO]` (staged): tensor-stability. The locally-surjective half
  (`IsLocallySurjective.tensorHom`) is proven at the level of sections; the
  locally-injective half (`IsLocallyInjective.tensorHom`) is the stalkwise/filtered
  argument (no flatness — stalks of a locally bijective map are isomorphisms) and is
  a registered work-in-progress leaf.

Once the leaf closes, `LocalizedMonoidal (sheafification (𝟙 _)) (sheafificationW _) ε`
with `ε` the sheafified-unit counit iso hands `SheafOfModules` its monoidal structure
with monoidal sheafification — the GAP-1 kernel, tensor-closure of invertible sheaves,
and the Pic-group coherences (board v10.64).
-/

universe v v' u u'

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The class of morphisms of presheaves of modules inverted by the sheafification
functor: the localizing class for `SheafOfModules`. -/
def sheafificationW : MorphismProperty (PresheafOfModules.{v} R₀) :=
  (MorphismProperty.isomorphisms _).inverseImage (sheafification.{v} α)

lemma sheafificationW_iff {M N : PresheafOfModules.{v} R₀} (f : M ⟶ N) :
    sheafificationW.{v} α f ↔ IsIso ((sheafification.{v} α).map f) :=
  Iff.rfl

/-- Membership in the localizing class is local bijectivity of the underlying morphism
of presheaves of abelian groups: the sheafification of modules inverts exactly the
locally bijective maps. -/
lemma sheafificationW_iff_isLocallyBijective {M N : PresheafOfModules.{v} R₀}
    (f : M ⟶ N) :
    sheafificationW.{v} α f ↔
      Presheaf.IsLocallyInjective J ((toPresheaf R₀).map f) ∧
        Presheaf.IsLocallySurjective J ((toPresheaf R₀).map f) := by
  rw [sheafificationW_iff]
  constructor
  · intro h
    have h1 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) :=
      inferInstance
    have h2 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) := h1
    have h3 : J.W ((toPresheaf R₀).map f) := (J.W_iff _).mpr h2
    exact ⟨h3.isLocallyInjective, h3.isLocallySurjective⟩
  · rintro ⟨h1, h2⟩
    have h3 : J.W ((toPresheaf R₀).map f) := J.W_of_isLocallyBijective _
    have h4 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) :=
      (J.W_iff _).mp h3
    have h5 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) := h4
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

section Reflective

variable (R' : Sheaf J RingCat.{u})

/-- At `α = 𝟙` the sheafification adjunction is reflective (`forget` is fully faithful
and `restrictScalars (𝟙 _)` is an equivalence), so the sheafification functor is a
localization at `sheafificationW`. -/
instance sheafificationW_isLocalization :
    (sheafification.{v} (𝟙 R'.obj)).IsLocalization (sheafificationW.{v} (𝟙 R'.obj)) := by
  have h : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Full :=
    Functor.Full.comp _ _
  have h' : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Faithful :=
    Functor.Faithful.comp _ _
  exact (sheafificationAdjunction (𝟙 R'.obj)).isLocalization

end Reflective

end PresheafOfModules
