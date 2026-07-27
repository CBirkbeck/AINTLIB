/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.AffineScheme
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
  simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, Scheme.Hom.appTop]
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

/-- The canonical affine-chart morphism induces the inverse `ΓSpec` identification on
sections. -/
theorem IsAffineOpen.fromSpec_appLE_comp_ΓSpecIso
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appLE U ⊤
        (le_of_eq hU.fromSpec_preimage_self.symm) ≫
      (Scheme.ΓSpecIso Γ(X, U)).hom =
        𝟙 Γ(X, U) := by
  have hdef : hU.fromSpec = hU.isoSpec.inv ≫ U.ι := rfl
  rw [appLE_congr_hom hdef U ⊤,
    ← Scheme.Hom.appLE_comp_appLE hU.isoSpec.inv U.ι U ⊤ ⊤
      U.ι_preimage_self.ge le_top,
    ι_appLE_top,
    appLE_top_top]
  have h1 : hU.isoSpec.inv.appTop ≫ hU.isoSpec.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  have h2 : hU.isoSpec.hom.appTop =
      (Scheme.ΓSpecIso Γ(X, U)).hom ≫ U.topIso.inv := by
    rw [hU.isoSpec_hom, Scheme.Opens.toSpecΓ_appTop]
  rw [h2] at h1
  have h3 : hU.isoSpec.inv.appTop ≫
      (Scheme.ΓSpecIso Γ(X, U)).hom = U.topIso.hom := by
    have h4 := congrArg (· ≫ U.topIso.hom) h1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp] at h4
    exact h4
  rw [Category.assoc, h3, Iso.inv_hom_id]

end AlgebraicGeometry
