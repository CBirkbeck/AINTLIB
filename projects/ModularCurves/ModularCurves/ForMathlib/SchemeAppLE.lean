/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Basic computation rules for `Scheme.Hom.appLE`

General-purpose lemmas about the restricted section maps `f.appLE U V e` and the restricted
morphisms `f.resLE U V e`: how they behave on the identity morphism, between top opens, along
an open immersion, and under an equality of morphisms.

Nothing here is specific to any construction — these are `mathlib`-shaped facts about
`Scheme.Hom.appLE`, kept in `ForMathlib` so that they are findable from the `AlgebraicGeometry`
namespace rather than from whichever development first needed them.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The `appLE` of an identity morphism is the identity. -/
theorem appLE_id {X : Scheme.{u}} {U : X.Opens} (e : U ≤ (𝟙 X) ⁻¹ᵁ U) :
    Scheme.Hom.appLE (𝟙 X) U U e = 𝟙 _ := by
  rw [Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.id_app]
  exact (Category.id_comp _).trans (X.presheaf.map_id _)

/-- `appLE` between the top opens is `appTop`. -/
theorem appLE_top_top {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Hom.appLE f ⊤ ⊤ le_top = f.appTop := by
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  exact Category.comp_id _

/-- The `⊤`-restriction of an open immersion's sections is the section iso. -/
theorem ι_appLE_top {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

/-- `resLE` transported along an equality of morphisms. -/
theorem appLE_congr_hom_resLE {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (W : X.Opens) {e : W ≤ f ⁻¹ᵁ U} :
    f.resLE U W e = g.resLE U W (h ▸ e) := by
  subst h; rfl

/-- `appLE` transported along an equality of morphisms. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens)
    (W : X.Opens) (e : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W (h ▸ e) := by
  subst h; rfl

end AlgebraicGeometry
