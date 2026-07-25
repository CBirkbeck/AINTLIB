/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.QuotientProblem

/-!
# Products of moduli problems

**[T-YR-6-APP (P1)]** The pointwise product of two moduli problems, and the fact that
it is represented by the total space of a relative representation of the second
problem over a representing object of the first: "a point of `Z` = a point of `X`
(i.e. a `P`-datum) together with a `Q`-datum on the curve it classifies".

This is the tool that identifies the two orders of "add a ρ-level structure" and
"add a Legendre datum" for the `Y(ρ̄)` smoothness leaf.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace ModularCurves

namespace ModuliProblem

variable {R : CommRingCat.{u}}

/-- The pointwise product of two moduli problems. -/
def prod (P Q : ModuliProblem R) : ModuliProblem R where
  obj X := P.obj X × Q.obj X
  map {X Y} f := ↾fun a => (P.map f a.1, Q.map f a.2)
  map_id X := by
    ext a
    · simp only [FunctorToTypes.map_id_apply]
      rfl
    · simp only [FunctorToTypes.map_id_apply]
      rfl
  map_comp f g := by
    ext a
    · simp only [FunctorToTypes.map_comp_apply]
      rfl
    · simp only [FunctorToTypes.map_comp_apply]
      rfl

@[simp] lemma prod_map_apply (P Q : ModuliProblem R) {X Y : (EllObj R)ᵒᵖ} (f : X ⟶ Y)
    (a : P.obj X × Q.obj X) :
    (P.prod Q).map f a = (P.map f a.1, Q.map f a.2) := rfl

end ModuliProblem

end ModularCurves

end
