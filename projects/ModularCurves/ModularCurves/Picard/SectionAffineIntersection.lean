/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.ForMathlib.FiniteIntersectionFunctor

/-!
# Finite intersections and preimages (W3.4.c)

The un-normalized descent needs to compare the affine-intersection diagram of a cover of
the base with that of its preimage cover on the total space, the comparison being
evaluation along a section `z`. The first step is purely lattice-theoretic: a finite
intersection of preimages is the preimage of the finite intersection.
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace ModularCurves

variable {X Y : Scheme.{u}} {J : Type u}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4.c brick] Preimage commutes with the finite intersection of a cover.** -/
theorem finiteIntersectionOpen_preimage (f : X ⟶ Y) (U : J → Y.Opens) (s : Finset J) :
    X.finiteIntersectionOpen (fun i => f ⁻¹ᵁ U i) s = f ⁻¹ᵁ Y.finiteIntersectionOpen U s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Scheme.finiteIntersectionOpen_empty, Scheme.finiteIntersectionOpen_empty]
      rfl
  | insert i s hi ih =>
      have h1 : X.finiteIntersectionOpen (fun i => f ⁻¹ᵁ U i) (insert i s) =
          (f ⁻¹ᵁ U i) ⊓ X.finiteIntersectionOpen (fun i => f ⁻¹ᵁ U i) s := by
        simp only [Scheme.finiteIntersectionOpen, Finset.coe_insert, iInf_insert]
      have h2 : Y.finiteIntersectionOpen U (insert i s) =
          U i ⊓ Y.finiteIntersectionOpen U s := by
        simp only [Scheme.finiteIntersectionOpen, Finset.coe_insert, iInf_insert]
      rw [h1, h2, ih]
      rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W3.4.c brick] A section lands in the finite intersection.** If `z` is a section of
`f`, then over the finite intersection of a family of base opens, `z` maps into the
finite intersection of their preimages. -/
theorem finiteIntersectionOpen_le_preimage_section {T : Scheme.{u}} (f : X ⟶ T)
    (z : T ⟶ X) (hz : z ≫ f = 𝟙 T) (U : J → T.Opens) (s : Finset J) :
    T.finiteIntersectionOpen U s ≤
      z ⁻¹ᵁ X.finiteIntersectionOpen (fun i => f ⁻¹ᵁ U i) s := by
  rw [finiteIntersectionOpen_preimage]
  intro x hx
  show x ∈ z ⁻¹ᵁ (f ⁻¹ᵁ T.finiteIntersectionOpen U s)
  have h : z ⁻¹ᵁ (f ⁻¹ᵁ T.finiteIntersectionOpen U s) =
      (z ≫ f) ⁻¹ᵁ T.finiteIntersectionOpen U s := rfl
  rw [h, hz]
  exact hx

end ModularCurves
