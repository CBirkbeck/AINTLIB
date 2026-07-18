/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Topology.Category.TopCat.Opens

/-!
# The opens-preimage functor is final

For a continuous map `f : X → Y`, the preimage functor
`Opens.map f : Opens Y ⥤ Opens X` is final: for every `U : Opens X` the comma category
of opens `V : Opens Y` with `U ≤ f ⁻¹ᵁ V` is nonempty (`V = ⊤`) and connected (any two
such `V₁, V₂` zig-zag through `V₁ ⊓ V₂`, since preimage preserves binary meets).

This feeds mathlib's `SheafOfModules.pullbackObjUnitToUnit` isomorphism (which requires
`[F.Final]` on the underlying site functor): pullback of the unit sheaf of modules along
any morphism of schemes is the unit — AINTLIB ModularCurves T-PIC1a-FIN. Upstream
candidate.
-/

open CategoryTheory TopologicalSpace

namespace TopologicalSpace.Opens

variable {X Y : TopCat} (f : X ⟶ Y)

instance map_final : (Opens.map f).Final where
  out U := by
    have hne : Nonempty (StructuredArrow U (Opens.map f)) :=
      ⟨StructuredArrow.mk (Y := ⊤) (homOfLE le_top)⟩
    refine zigzag_isConnected fun A B => ?_
    have hA : U ≤ (Opens.map f).obj (A.right ⊓ B.right) :=
      le_inf (leOfHom A.hom) (leOfHom B.hom)
    have z1 : Zag A (StructuredArrow.mk (homOfLE hA)) :=
      Or.inr ⟨StructuredArrow.homMk (homOfLE inf_le_left) (Subsingleton.elim _ _)⟩
    have z2 : Zag (StructuredArrow.mk (homOfLE hA)) B :=
      Or.inl ⟨StructuredArrow.homMk (homOfLE inf_le_right) (Subsingleton.elim _ _)⟩
    exact (Relation.ReflTransGen.single z1).trans (Relation.ReflTransGen.single z2)

end TopologicalSpace.Opens
