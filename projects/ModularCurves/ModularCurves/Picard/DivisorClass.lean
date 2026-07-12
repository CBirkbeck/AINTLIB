/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.Picard.IdealModule

/-!
# The Picard class of a relative effective Cartier divisor (the D2 seam)

The seam between the divisor engine of `LevelStructure/CartierDivisor.lean` and the
Picard stream: on a separated smooth relative curve, the ideal module of a relative
effective Cartier divisor is invertible (KM 1.1.1's official form, via
`RelEffCartierDiv.isOfficial` + `isInvertible_idealModule`), so it has a class in
`Pic C`; following GME (`L(D) = I(D)⁻¹`, p. 107) we take the inverse class.

## Main definitions

* `ModularCurves.RelEffCartierDiv.isInvertible_idealModule`: the ideal module of a
  relative effective Cartier divisor is invertible.
* `ModularCurves.RelEffCartierDiv.picClass`: the class `[I(D)]⁻¹ ∈ Pic C`.
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

namespace RelEffCartierDiv

variable {C S : Scheme.{u}} {π : C ⟶ S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The ideal sheaf of a relative effective Cartier divisor is an invertible module**
(KM 1.1.1: "the ideal sheaf `I(D) ⊂ O_X` is an invertible `O_X`-module"; the AG-LB
interface applied to the engine's `isOfficial`). -/
theorem isInvertible_idealModule [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π) (D : RelEffCartierDiv π) :
    IsInvertible (idealModule D.ideal) :=
  Modules.isInvertible_idealModule D.ideal (D.isOfficial π hsm).locallyPrincipal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Picard class of a relative effective Cartier divisor: `[I(D)]⁻¹` (GME p. 107:
"`I(P)` is invertible, and `P` gives rise to a relative effective Cartier divisor";
p. 109: "`L = I(P)⁻¹`"). -/
noncomputable def picClass [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π)
    (D : RelEffCartierDiv π) : Pic C :=
  letI := Modules.monoidalCategory C
  ((D.isInvertible_idealModule hsm).isUnit_toSkeleton).unit⁻¹

end RelEffCartierDiv

end ModularCurves
