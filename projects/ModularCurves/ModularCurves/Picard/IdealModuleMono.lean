/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Picard.IdealModule

/-!
# Monotone maps of ideal modules

The subtype inclusion `idealModule J₁ ⟶ idealModule J₂` for nested ideal sheaves —
in a minimal-import file: the same declarations time out at kernel level when
elaborated inside the heavy `WeilPairing/LineVertical.lean` import environment.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Ideal sections are monotone in the ideal sheaf: the subscheme inclusion composes
with the smaller inclusion, so vanishing transfers. -/
theorem idealSections_mono {J₁ J₂ : C.IdealSheafData} (h : J₁ ≤ J₂)
    (U : (TopologicalSpace.Opens ↥C)ᵒᵖ) {g : Γ(C, U.unop)}
    (hg : g ∈ idealSections J₁ U) : g ∈ idealSections J₂ U := by
  refine RingHom.mem_ker.mpr ?_
  have hι := Scheme.IdealSheafData.inclusion_subschemeι h
  rw [← hι]
  show ((Scheme.IdealSheafData.inclusion h).app _).hom
    ((J₁.subschemeι.app U.unop).hom g) = 0
  rw [RingHom.mem_ker.mp hg, map_zero]

end AlgebraicGeometry.Scheme.Modules
