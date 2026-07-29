/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafSuccessorSections

/-!
# The constant section of the first pole module

The literal constant section is nonzero in the monoidal unit and remains
nonzero after applying the first pole-filtration inclusion.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace

universe u

namespace ModularCurves

/-- The canonical section of the monoidal unit is nonzero on a nonempty
scheme. -/
theorem monoidalUnitSection_ne_zero
    (X : Scheme.{u}) [Nonempty X] : monoidalUnitSection X ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  let V : X.affineOpens := ⟨U, hU⟩
  letI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI : Nonempty V.1.toScheme := ‹Nonempty U›
  letI : Nonempty (⊤ : V.1.toScheme.Opens) :=
    ⟨⟨⟨x, hxU⟩, Set.mem_univ _⟩⟩
  intro hzero
  have hcoord := localTrivializationTopSection_monoidalUnitSection V
  rw [hzero, localTrivializationTopSection_zero] at hcoord
  exact zero_ne_one hcoord

/-- The literal constant section in the first pole-section module. -/
noncomputable def sectionPoleSheafPowerOneSection
    {C S : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 1) :=
  Scheme.Modules.baseSectionsMap π
    (sectionPoleSheafSuccHom π z hz 0) (monoidalUnitSection C)

/-- The literal constant section remains nonzero in the first pole-section
module. -/
theorem sectionPoleSheafPowerOneSection_ne_zero
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) [Nonempty C] :
    sectionPoleSheafPowerOneSection π z hz ≠ 0 := by
  haveI : Mono (sectionPoleSheafSuccHom π z hz 0) :=
    sectionPoleSheafSuccHom_mono hsm z hz 0
  have hq : Function.Injective (Scheme.Modules.baseSectionsMap π
      (sectionPoleSheafSuccHom π z hz 0)) :=
    (ModuleCat.mono_iff_injective (Scheme.Modules.baseSectionsMap π
      (sectionPoleSheafSuccHom π z hz 0))).mp
      (Scheme.Modules.baseSectionsMap_mono π
        (sectionPoleSheafSuccHom π z hz 0) inferInstance)
  intro hzero
  apply monoidalUnitSection_ne_zero C
  apply hq
  exact hzero.trans
    ((Scheme.Modules.baseSectionsMap π
      (sectionPoleSheafSuccHom π z hz 0)).hom.map_zero).symm

end ModularCurves
