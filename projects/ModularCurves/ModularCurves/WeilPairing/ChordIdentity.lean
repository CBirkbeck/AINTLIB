/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.LineVerticalAssembly

/-!
# The chord identity (W1) — statement and downstream wiring

Everything in the Weil-pairing prong upstream of the theorem of the square is proved:
the line and the vertical are rank-one kernels, a section vanishing to exactly the
divisor order trivializes the twist, and the two trivializations combine into
`I(P) ⊗ I(Q) ≅ I(P+Q) ⊗ I(0)` (`WeilPairing/LineVerticalAssembly.lean`).

What is left is one geometric input, isolated here:

**the chord identity** — on a Weierstrass chart, the chord through `P` and `Q` vanishes
exactly on `[P] + [Q] + [-(P+Q)]`, and the vertical through `R` vanishes exactly on
`[R] + [-R]`.

`ChordDatum` below packages the two statements in the form the machinery consumes (a
trivialization of each twisted module), and `nonempty_tensorObj_iso_of_chordDatum`
derives the theorem of the square from it — so the interface is compile-verified and
the remaining work is exactly the construction of a `ChordDatum`.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {C S : Scheme.{u}} {π : C ⟶ S}

/-- **The chord datum of a pair of sections.** The two trivializations that the
chord and the vertical produce on a base where a Weierstrass chart is available:
the chord through `P`, `Q` cuts out `[P] + [Q] + [R⁻]` on `𝒪(3[0])`, and the vertical
through `R` cuts out `[R] + [R⁻]` on `𝒪(2[0])`, where `R = P + Q` and `R⁻ = -(P+Q)`. -/
structure ChordDatum [IsSeparated π] (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (P Q R Rm : { w : S ⟶ C // w ≫ π = 𝟙 S }) : Prop where
  /-- The kernel ideal of each of the four sections is locally principal on a
  nonzerodivisor (automatic for sections of a smooth relative curve). -/
  principal : ∀ Z : { w : S ⟶ C // w ≫ π = 𝟙 S }, Z = P ∨ Z = Q ∨ Z = R ∨ Z = Rm →
    ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
      (Scheme.Hom.ker Z.1).ideal V = Ideal.span {g} ∧ g ∈ nonZeroDivisors Γ(C, V.1)
  /-- The chord trivializes the triple twist of `𝒪(3[0])`. -/
  chord : Nonempty (tensorObj (idealModule (Scheme.Hom.ker P.1))
    (tensorObj (idealModule (Scheme.Hom.ker Q.1))
      (tensorObj (idealModule (Scheme.Hom.ker Rm.1))
        (ModularCurves.sectionPoleSheafPower π z hz 3))) ≅ unitObj C)
  /-- The vertical trivializes the double twist of `𝒪(2[0])`. -/
  vertical : Nonempty (tensorObj (idealModule (Scheme.Hom.ker R.1))
    (tensorObj (idealModule (Scheme.Hom.ker Rm.1))
      (ModularCurves.sectionPoleSheafPower π z hz 2)) ≅ unitObj C)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The theorem of the square from a chord datum.** Every step between the chord
identity and the divisor identity is discharged. -/
theorem nonempty_tensorObj_iso_of_chordDatum [IsSeparated π]
    (hsm : SmoothOfRelativeDimension 1 π)
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (P Q R Rm : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (h : ChordDatum z hz P Q R Rm) :
    Nonempty (tensorObj (idealModule (Scheme.Hom.ker P.1))
        (idealModule (Scheme.Hom.ker Q.1)) ≅
      tensorObj (idealModule (Scheme.Hom.ker R.1))
        (ModularCurves.sectionIdealModule π z hz)) :=
  nonempty_tensorObj_iso_of_exact_order_chart_identities hsm z hz
    (Scheme.Hom.ker P.1) (Scheme.Hom.ker Q.1) (Scheme.Hom.ker R.1)
    (Scheme.Hom.ker Rm.1)
    (h.principal P (Or.inl rfl)) (h.principal Q (Or.inr (Or.inl rfl)))
    (h.principal R (Or.inr (Or.inr (Or.inl rfl))))
    (h.principal Rm (Or.inr (Or.inr (Or.inr rfl))))
    h.chord h.vertical

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d2] Vanishing at a section, in chart coordinates.** A chart section lies in
the kernel ideal of a section of `π` exactly when the corresponding evaluation
retraction kills it; the kernel is the principal ideal of the transported generator.
This is the algebraic form in which the chord–tangent condition will be checked. -/
theorem mem_span_iff_algHom_eq_zero_of_section [IsSeparated π]
    (Z : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens) (hZU : Z.1 ⁻¹ᵁ U.1 = ⊤)
    (rZ : Γ(C, U.1)) (hZ : (Scheme.Hom.ker Z.1).ideal U = Ideal.span {rZ})
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r) :
    ∃ σ : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) →ₐ[Γ(S, (⊤ : S.Opens))]
        Γ(S, (⊤ : S.Opens)),
      ∀ c : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)),
        (c ∈ Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rZ} ↔
          σ c = 0) := by
  obtain ⟨σ, hσ⟩ := exists_algHom_ker_eq_span_of_section Z.1 Z.2 U hZU rZ hZ halg
  refine ⟨σ, fun c => ?_⟩
  constructor
  · intro hc
    rw [← hσ] at hc
    exact hc
  · intro hc
    rw [← hσ]
    exact hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d2] Divisibility by a product of three generators, in evaluation form.**
The exact-order hypothesis of `nonempty_iso_unitObj_of_exact_order₃` asks for the chart
multiplier to be a unit multiple of `g_P·g_Q·g_R`. In a chart where the three
evaluations are available, the divisibility half of that statement is exactly the
simultaneous vanishing of the three evaluations of the successive quotients — the form
the chord–tangent computation produces. -/
theorem mul_dvd_of_evaluations_vanish
    {A B : Type*} [CommRing A] [CommRing B]
    (σ : A →+* B) (g c : A) (hker : RingHom.ker σ = Ideal.span {g})
    (hc : σ c = 0) : ∃ c' : A, c = g * c' := by
  have hmem : c ∈ Ideal.span {g} := by
    rw [← hker]
    exact hc
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨a, by rw [← ha, mul_comm]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d4] The exact-order identity from three evaluations and one unit.**
If a chart element is killed by three evaluation retractions whose kernels are the
principal ideals of `g₁, g₂, g₃`, the successive quotients being taken in the same
chart, and the final quotient is a unit, then the element is a unit multiple of the
product — the hypothesis shape of `nonempty_iso_unitObj_of_exact_order₃`. -/
theorem eq_unit_mul_of_three_divisions {A : Type*} [CommRing A]
    (c g₁ g₂ g₃ : A) (c₁ c₂ : A) (u : Aˣ)
    (h₁ : c = g₁ * c₁) (h₂ : c₁ = g₂ * c₂) (h₃ : c₂ = g₃ * (u : A)) :
    c = (u : A) * (g₁ * (g₂ * g₃)) := by
  rw [h₁, h₂, h₃]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The two-factor version, for the vertical. -/
theorem eq_unit_mul_of_two_divisions {A : Type*} [CommRing A]
    (c g₁ g₂ : A) (c₁ : A) (u : Aˣ)
    (h₁ : c = g₁ * c₁) (h₂ : c₁ = g₂ * (u : A)) :
    c = (u : A) * (g₁ * g₂) := by
  rw [h₁, h₂]
  ring

end AlgebraicGeometry.Scheme.Modules
