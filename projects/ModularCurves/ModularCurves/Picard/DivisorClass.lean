/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.Picard.IdealModule
import ModularCurves.Picard.RelativePic

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
theorem isInvertible_idealModule [IsSeparated π] (D : RelEffCartierDiv π)
    (h : IsOfficialCartier π D.ideal) :
    IsInvertible (idealModule D.ideal) :=
  Modules.isInvertible_idealModule D.ideal h.locallyPrincipal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Picard class of a relative effective Cartier divisor: `[I(D)]⁻¹` (GME p. 107:
"`I(P)` is invertible, and `P` gives rise to a relative effective Cartier divisor";
p. 109: "`L = I(P)⁻¹`"). -/
noncomputable def picClass [IsSeparated π] (D : RelEffCartierDiv π)
    (h : IsOfficialCartier π D.ideal) : Pic C :=
  letI := Modules.monoidalCategory C
  ((D.isInvertible_idealModule h).isUnit_toSkeleton).unit⁻¹

end RelEffCartierDiv

section Assembly

open AlgebraicGeometry.Scheme.Modules CategoryTheory.Limits

variable {S E : Scheme.{u}} (p : E ⟶ S) (z : S ⟶ E) (hz : z ≫ p = 𝟙 S)
variable {T : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The GME (2.16) assembly map** `E(T) → Pic_{E/S}(T)`: a section `P` of the
base-changed curve goes to the normalized class of `I(P)⁻¹ ⊗ I(0)` (GME p. 108:
"`P ↦ I(P)⁻¹ ↦ I(P)⁻¹ ⊗ I(0)`"), projected into the kernel model by the zero-section
splitting. -/
noncomputable def sectionToPicRel [IsSeparated p]
    (hsm : SmoothOfRelativeDimension 1 p) (t : T ⟶ S)
    (P : T ⟶ Limits.pullback p t) (hP : P ≫ Limits.pullback.snd p t = 𝟙 T) :
    picRel p z hz t :=
  haveI hsep : IsSeparated (Limits.pullback.snd p t) :=
    MorphismProperty.pullback_snd (P := @IsSeparated) p t ‹_›
  have hsm' : SmoothOfRelativeDimension 1 (Limits.pullback.snd p t) :=
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) p t hsm
  picRelProj p z hz t
    ((RelEffCartierDiv.sectionDivisor (Limits.pullback.snd p t) P hP).picClass
        (RelEffCartierDiv.sectionDivisor_isOfficial hsm' P hP) *
      ((RelEffCartierDiv.sectionDivisor (Limits.pullback.snd p t)
        (baseChangeZero p z hz t) (baseChangeZero_snd p z hz t)).picClass
          (RelEffCartierDiv.sectionDivisor_isOfficial hsm'
            (baseChangeZero p z hz t) (baseChangeZero_snd p z hz t)))⁻¹)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The zero section is sent to the identity class (GME p. 108: "`Pic⁰` is a group
functor with the identity `O_E`"). -/
theorem sectionToPicRel_zero [IsSeparated p] (hsm : SmoothOfRelativeDimension 1 p)
    (t : T ⟶ S) :
    sectionToPicRel p z hz hsm t (baseChangeZero p z hz t) (baseChangeZero_snd p z hz t) =
      1 := by
  show picRelProj p z hz t _ = 1
  rw [mul_inv_cancel, map_one]

end Assembly

end ModularCurves
