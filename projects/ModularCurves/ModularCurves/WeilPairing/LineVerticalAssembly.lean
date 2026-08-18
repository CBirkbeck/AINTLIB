/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.IteratedTwist
import ModularCurves.Picard.PicComparison

/-!
# From the line and the vertical to the theorem of the square (GAP-A-5c)

The two trivializations produced by the line and the vertical,

* `I(P) ⊗ I(Q) ⊗ I(R⁻) ⊗ 𝒪(3[0]) ≅ 𝒪` (the chord through `P`, `Q` and `R⁻ = -(P+Q)`),
* `I(R) ⊗ I(R⁻) ⊗ 𝒪(2[0]) ≅ 𝒪` (the vertical through `R = P+Q` and `R⁻`),

combine into `I(P) ⊗ I(Q) ≅ I(R) ⊗ I(0)`: the residual factor `I(R⁻)` cancels and the
pole sheaves contribute `𝒪(2[0]) ⊗ 𝒪(3[0])⁻¹ = 𝒪(-[0]) = I(0)`. All of this happens in
the Picard skeleton, where the classes of invertible modules form a commutative monoid
whose invertible elements are exactly the classes of invertible modules
(`Picard/PicComparison.lean`), so the argument is group algebra with no geometry.

The two inputs are the outputs of `WeilPairing/IteratedTwist.lean`; the chord–tangent
identity that produces them (that the third zero of the chord is `-(P+Q)`) is the
remaining mathematical input of the prong.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {C : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Skeleton form of a trivialization.** -/
theorem toSkeleton_eq_one_of_iso_unitObj {M : C.Modules}
    (h : Nonempty (M ≅ unitObj C)) :
    letI := Modules.monoidalCategory C
    toSkeleton M = 1 := by
  letI := Modules.monoidalCategory C
  rw [← toSkeleton_unitObj (X := C)]
  exact toSkeleton_eq_toSkeleton_iff.mpr h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[GAP-A-5c] The theorem of the square from the chord and the vertical.**

Given a trivialization of the chord twist `A ⊗ (B ⊗ (Rm ⊗ P₃))` and of the vertical
twist `Rp ⊗ (Rm ⊗ P₂)`, together with the pole-sheaf relation `P₃ ≅ P₂ ⊗ P₁` and the
duality `P₁ ⊗ Z ≅ 𝒪` (the degree-one pole sheaf inverts the ideal of the zero section),
the two divisor products agree: `A ⊗ B ≅ Rp ⊗ Z`. -/
theorem nonempty_tensorObj_iso_of_chord_vertical
    {A B Rp Rm Z P₁ P₂ P₃ : C.Modules}
    (hA : IsInvertible A) (hB : IsInvertible B) (hRp : IsInvertible Rp)
    (hRm : IsInvertible Rm) (hZ : IsInvertible Z)
    (hP₁ : IsInvertible P₁) (hP₂ : IsInvertible P₂) (hP₃ : IsInvertible P₃)
    (hchord : Nonempty (tensorObj A (tensorObj B (tensorObj Rm P₃)) ≅ unitObj C))
    (hvert : Nonempty (tensorObj Rp (tensorObj Rm P₂) ≅ unitObj C))
    (hpow : Nonempty (P₃ ≅ tensorObj P₂ P₁))
    (hdual : Nonempty (tensorObj P₁ Z ≅ unitObj C)) :
    Nonempty (tensorObj A B ≅ tensorObj Rp Z) := by
  letI := Modules.monoidalCategory C
  letI := Modules.symmetricCategory C
  classical
  -- transport everything into the skeleton
  set a := toSkeleton A with ha
  set b := toSkeleton B with hb
  set rp := toSkeleton Rp with hrp
  set rm := toSkeleton Rm with hrm
  set z := toSkeleton Z with hz
  set p₁ := toSkeleton P₁ with hp₁
  set p₂ := toSkeleton P₂ with hp₂
  set p₃ := toSkeleton P₃ with hp₃
  have hchord' : a * (b * (rm * p₃)) = 1 := by
    rw [ha, hb, hrm, hp₃, ← toSkeleton_tensorObj_eq, ← toSkeleton_tensorObj_eq,
      ← toSkeleton_tensorObj_eq]
    exact toSkeleton_eq_one_of_iso_unitObj hchord
  have hvert' : rp * (rm * p₂) = 1 := by
    rw [hrp, hrm, hp₂, ← toSkeleton_tensorObj_eq, ← toSkeleton_tensorObj_eq]
    exact toSkeleton_eq_one_of_iso_unitObj hvert
  have hpow' : p₃ = p₂ * p₁ := by
    rw [hp₃, hp₂, hp₁, ← toSkeleton_tensorObj_eq]
    exact toSkeleton_eq_toSkeleton_iff.mpr hpow
  have hdual' : p₁ * z = 1 := by
    rw [hp₁, hz, ← toSkeleton_tensorObj_eq]
    exact toSkeleton_eq_one_of_iso_unitObj hdual
  -- the units we cancel against
  obtain ⟨urm, hurm⟩ := hRm.isUnit_toSkeleton
  obtain ⟨up₂, hup₂⟩ := hP₂.isUnit_toSkeleton
  obtain ⟨up₁, hup₁⟩ := hP₁.isUnit_toSkeleton
  -- group algebra: (a*b) * (rm*p₂*p₁) = 1 = (rp*z) * (rm*p₂*p₁)
  have hleft : (a * b) * ((rm * p₂) * p₁) = 1 := by
    calc (a * b) * ((rm * p₂) * p₁)
        = a * (b * (rm * (p₂ * p₁))) := by
          simp only [mul_assoc]
      _ = a * (b * (rm * p₃)) := by rw [hpow']
      _ = 1 := hchord'
  have hright : (rp * z) * ((rm * p₂) * p₁) = 1 := by
    calc (rp * z) * ((rm * p₂) * p₁)
        = (rp * (rm * p₂)) * (p₁ * z) := by
          simp only [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 * 1 := by rw [hvert', hdual']
      _ = 1 := one_mul 1
  have hunit : IsUnit ((rm * p₂) * p₁) := by
    refine IsUnit.mul (IsUnit.mul ?_ ?_) ?_
    · exact ⟨urm, hurm⟩
    · exact ⟨up₂, hup₂⟩
    · exact ⟨up₁, hup₁⟩
  obtain ⟨u, hu⟩ := hunit
  have hcancel : a * b = rp * z := by
    have h1 : (a * b) * (u : Skeleton C.Modules) =
        (rp * z) * (u : Skeleton C.Modules) := by
      rw [hu, hleft, hright]
    exact u.mul_left_inj.mp h1
  refine toSkeleton_eq_toSkeleton_iff.mp ?_
  rw [toSkeleton_tensorObj_eq, toSkeleton_tensorObj_eq, ← ha, ← hb, ← hrp, ← hz]
  exact hcancel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The pole/ideal duality**: the degree-one pole sheaf inverts the ideal module of
the zero section. -/
theorem nonempty_tensorObj_sectionPoleSheaf_iso
    {S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) :
    Nonempty (tensorObj (ModularCurves.sectionPoleSheaf π z hz)
      (ModularCurves.sectionIdealModule π z hz) ≅ unitObj C) := by
  obtain ⟨e⟩ := nonempty_eval_iso
    (ModularCurves.sectionIdealModule_isInvertible hsm z hz)
  obtain ⟨ec⟩ := nonempty_tensorObj_comm
    (ModularCurves.sectionPoleSheaf π z hz)
    (ModularCurves.sectionIdealModule π z hz)
  exact ⟨ec ≪≫ e⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The pole ladder**: one more pole order is one more tensor factor. -/
theorem nonempty_sectionPoleSheafPower_succ_iso
    {S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S) (n : ℕ) :
    Nonempty (ModularCurves.sectionPoleSheafPower π z hz (n + 1) ≅
      tensorObj (ModularCurves.sectionPoleSheafPower π z hz n)
        (ModularCurves.sectionPoleSheaf π z hz)) := by
  letI := Modules.monoidalCategory C
  exact ⟨(nonempty_tensorObj_iso_tensor
    (ModularCurves.sectionPoleSheafPower π z hz n)
    (ModularCurves.sectionPoleSheaf π z hz)).some.symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[GAP-A-5c at the pole sheaves]** The theorem of the square from the chord and
the vertical, with the pole-sheaf inputs discharged. -/
theorem nonempty_tensorObj_iso_of_chord_vertical_poleSheaf
    {S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    {A B Rp Rm : C.Modules}
    (hA : IsInvertible A) (hB : IsInvertible B) (hRp : IsInvertible Rp)
    (hRm : IsInvertible Rm)
    (hchord : Nonempty (tensorObj A (tensorObj B (tensorObj Rm
      (ModularCurves.sectionPoleSheafPower π z hz 3))) ≅ unitObj C))
    (hvert : Nonempty (tensorObj Rp (tensorObj Rm
      (ModularCurves.sectionPoleSheafPower π z hz 2)) ≅ unitObj C)) :
    Nonempty (tensorObj A B ≅
      tensorObj Rp (ModularCurves.sectionIdealModule π z hz)) := by
  refine nonempty_tensorObj_iso_of_chord_vertical hA hB hRp hRm
    (ModularCurves.sectionIdealModule_isInvertible hsm z hz)
    (ModularCurves.sectionPoleSheaf_isInvertible hsm z hz)
    (ModularCurves.sectionPoleSheafPower_isInvertible hsm z hz 2)
    (ModularCurves.sectionPoleSheafPower_isInvertible hsm z hz 3)
    hchord hvert
    (nonempty_sectionPoleSheafPower_succ_iso z hz 2)
    (nonempty_tensorObj_sectionPoleSheaf_iso hsm z hz)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[WP PRONG, local form] The theorem of the square from two chart identities.**

`ℓ` is the chord — a section of `π_*𝒪(3[0])` whose chart multiplier is a unit times
`g_P · g_Q · g_{R⁻}` — and `v` the vertical — a section of `π_*𝒪(2[0])` whose chart
multiplier is a unit times `g_R · g_{R⁻}`. Then the divisor products agree:
`I(P) ⊗ I(Q) ≅ I(R) ⊗ I(0)`.

Everything between the two chart identities and this conclusion is discharged: the
lifts are isomorphisms by the exact-order criterion, and the Picard skeleton cancels
the residual factor and the pole sheaves. Over a general base the two identities hold
only Zariski-locally on the base — which is exactly why the descent step
(`Picard/RigidDescent.lean`) contributes the base bundle `N`. -/
theorem nonempty_tensorObj_iso_of_exact_order_chart_identities
    {S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (JP JQ JR JRm : C.IdealSheafData)
    (hJP : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JP.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hJQ : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JQ.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hJR : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JR.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hJRm : ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      JRm.ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1))
    (hchord : Nonempty (tensorObj (idealModule JP) (tensorObj (idealModule JQ)
      (tensorObj (idealModule JRm)
        (ModularCurves.sectionPoleSheafPower π z hz 3))) ≅ unitObj C))
    (hvert : Nonempty (tensorObj (idealModule JR) (tensorObj (idealModule JRm)
      (ModularCurves.sectionPoleSheafPower π z hz 2)) ≅ unitObj C)) :
    Nonempty (tensorObj (idealModule JP) (idealModule JQ) ≅
      tensorObj (idealModule JR) (ModularCurves.sectionIdealModule π z hz)) := by
  have hchord' : Nonempty (tensorObj (idealModule JP) (tensorObj (idealModule JQ)
      (tensorObj (idealModule JRm)
        (ModularCurves.sectionPoleSheafPower π z hz 3))) ≅ unitObj C) := hchord
  exact nonempty_tensorObj_iso_of_chord_vertical_poleSheaf hsm z hz
    (isInvertible_idealModule (J := JP) hJP)
    (isInvertible_idealModule (J := JQ) hJQ)
    (isInvertible_idealModule (J := JR) hJR)
    (isInvertible_idealModule (J := JRm) hJRm)
    hchord' hvert

end AlgebraicGeometry.Scheme.Modules
