/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.CartierDivisor
import ModularCurves.Picard.GlueTrivialization
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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Divisors with isomorphic ideal modules have the same Picard class. This is the form in
which the descent theorems (`Picard/GlueTrivialization.lean`,
`Picard/RigidDescent.lean`) are consumed: they produce an isomorphism of modules, and what
is needed downstream is an equality in the group `Pic C`. -/
theorem picClass_eq_of_nonempty_iso [IsSeparated π] {D D' : RelEffCartierDiv π}
    (h : IsOfficialCartier π D.ideal) (h' : IsOfficialCartier π D'.ideal)
    (e : Nonempty (idealModule D.ideal ≅ idealModule D'.ideal)) :
    D.picClass h = D'.picClass h' := by
  letI := Modules.monoidalCategory C
  letI := Modules.symmetricCategory C
  exact congrArg Inv.inv
    (Modules.IsInvertible.unit_eq_unit_of_iso (D.isInvertible_idealModule h)
      (D'.isInvertible_idealModule h') e)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Multiplicativity.** A tensor isomorphism between ideal modules gives an equality of
*products* of Picard classes. This is the shape the theorem of the square takes:
`I(D_Q) ⊗ I(D_{Q'}) ≅ I(D_{Q+Q'}) ⊗ I(D_0)`. -/
theorem picClass_mul_eq_of_nonempty_tensor_iso [IsSeparated π]
    {D₁ D₂ D₃ D₄ : RelEffCartierDiv π}
    (h₁ : IsOfficialCartier π D₁.ideal) (h₂ : IsOfficialCartier π D₂.ideal)
    (h₃ : IsOfficialCartier π D₃.ideal) (h₄ : IsOfficialCartier π D₄.ideal)
    (e : Nonempty (Modules.tensorObj (idealModule D₁.ideal) (idealModule D₂.ideal) ≅
      Modules.tensorObj (idealModule D₃.ideal) (idealModule D₄.ideal))) :
    D₁.picClass h₁ * D₂.picClass h₂ = D₃.picClass h₃ * D₄.picClass h₄ := by
  letI := Modules.monoidalCategory C
  letI := Modules.symmetricCategory C
  have key : ∀ (Da Db : RelEffCartierDiv π) (ha : IsOfficialCartier π Da.ideal)
      (hb : IsOfficialCartier π Db.ideal),
      (((Da.isInvertible_idealModule ha).isUnit_toSkeleton.unit *
          (Db.isInvertible_idealModule hb).isUnit_toSkeleton.unit :
        (Skeleton C.Modules)ˣ) : Skeleton C.Modules)
        = toSkeleton (Modules.tensorObj (idealModule Da.ideal) (idealModule Db.ideal)) := by
    intro Da Db ha hb
    rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, ← Skeleton.toSkeleton_tensorObj]
    exact (toSkeleton_eq_toSkeleton_iff.mpr (Modules.nonempty_tensorObj_iso_tensor _ _)).symm
  have hu : ((D₁.isInvertible_idealModule h₁).isUnit_toSkeleton.unit *
        (D₂.isInvertible_idealModule h₂).isUnit_toSkeleton.unit)
      = ((D₃.isInvertible_idealModule h₃).isUnit_toSkeleton.unit *
        (D₄.isInvertible_idealModule h₄).isUnit_toSkeleton.unit) := by
    refine Units.ext ?_
    rw [key D₁ D₂ h₁ h₂, key D₃ D₄ h₃ h₄]
    exact toSkeleton_eq_toSkeleton_iff.mpr e
  calc D₁.picClass h₁ * D₂.picClass h₂
      = ((D₁.isInvertible_idealModule h₁).isUnit_toSkeleton.unit *
          (D₂.isInvertible_idealModule h₂).isUnit_toSkeleton.unit)⁻¹ := (mul_inv _ _).symm
    _ = ((D₃.isInvertible_idealModule h₃).isUnit_toSkeleton.unit *
          (D₄.isInvertible_idealModule h₄).isUnit_toSkeleton.unit)⁻¹ := by rw [hu]
    _ = D₃.picClass h₃ * D₄.picClass h₄ := mul_inv _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The weakened multiplicativity — "differs by a class from the base".**

`picClass_mul_eq_of_nonempty_tensor_iso` asks for an exact tensor isomorphism, which for
the theorem of the square is *false*: `𝒪(D_Q) ⊗ 𝒪(D_{Q'})` and `𝒪(D_{Q+Q'}) ⊗ 𝒪(D_0)`
differ by the pullback of the normal bundle `0^*𝒪(D_0) ≅ ω⁻¹` of the zero section. This is
the form that survives: a tensor isomorphism up to `π^*N` gives an equality of class
products up to `Pic.map π [N]`.

Everything downstream only needs the *existence* of such an `M`, because
`Ker(0^*) ∩ Im(π^*) = 1` kills it (`eq_of_mul_inv_eq_picMap_snd`). -/
theorem exists_pic_map_of_nonempty_tensor_pullback_iso [IsSeparated π]
    {D₁ D₂ D₃ D₄ : RelEffCartierDiv π}
    (h₁ : IsOfficialCartier π D₁.ideal) (h₂ : IsOfficialCartier π D₂.ideal)
    (h₃ : IsOfficialCartier π D₃.ideal) (h₄ : IsOfficialCartier π D₄.ideal)
    {N : S.Modules} (hN : IsInvertible N)
    (e : Nonempty (Modules.tensorObj (idealModule D₁.ideal) (idealModule D₂.ideal) ≅
      Modules.tensorObj (Modules.tensorObj (idealModule D₃.ideal) (idealModule D₄.ideal))
        ((Modules.pullback π).obj N))) :
    ∃ M : Pic S,
      (D₃.picClass h₃ * D₄.picClass h₄) * (D₁.picClass h₁ * D₂.picClass h₂)⁻¹
        = Pic.map π M := by
  letI := Modules.monoidalCategory C
  letI := Modules.symmetricCategory C
  letI := Modules.monoidalCategory S
  letI := Modules.symmetricCategory S
  refine ⟨hN.isUnit_toSkeleton.unit, ?_⟩
  -- the inverse of a product of classes is the class of the tensor product of the ideals
  have key : ∀ (Da Db : RelEffCartierDiv π) (ha : IsOfficialCartier π Da.ideal)
      (hb : IsOfficialCartier π Db.ideal),
      ((Da.picClass ha * Db.picClass hb)⁻¹ : Pic C).val
        = toSkeleton (Modules.tensorObj (idealModule Da.ideal) (idealModule Db.ideal)) := by
    intro Da Db ha hb
    show (((Da.isInvertible_idealModule ha).isUnit_toSkeleton.unit⁻¹ *
      (Db.isInvertible_idealModule hb).isUnit_toSkeleton.unit⁻¹)⁻¹).val = _
    rw [← mul_inv, inv_inv, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
      ← Skeleton.toSkeleton_tensorObj]
    exact (toSkeleton_eq_toSkeleton_iff.mpr (Modules.nonempty_tensorObj_iso_tensor _ _)).symm
  -- the class of `π^*N` is `Pic.map π [N]`
  have hpull : (Pic.map π hN.isUnit_toSkeleton.unit).val
      = toSkeleton ((Modules.pullback π).obj N) := by
    rw [Scheme.Pic.map_val, IsUnit.unit_spec]
    exact Functor.mapSkeleton_obj_toSkeleton (Modules.pullback π) N
  -- `e`, read in the group of classes
  have hmain : ((D₁.picClass h₁ * D₂.picClass h₂)⁻¹ : Pic C)
      = (D₃.picClass h₃ * D₄.picClass h₄)⁻¹ * Pic.map π hN.isUnit_toSkeleton.unit := by
    refine Units.ext ?_
    rw [key D₁ D₂ h₁ h₂, Units.val_mul, key D₃ D₄ h₃ h₄, hpull,
      ← Skeleton.toSkeleton_tensorObj]
    exact (toSkeleton_eq_toSkeleton_iff.mpr e).trans
      (toSkeleton_eq_toSkeleton_iff.mpr (Modules.nonempty_tensorObj_iso_tensor _ _))
  rw [hmain, mul_inv_cancel_left]

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
