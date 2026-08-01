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

end AlgebraicGeometry.Scheme.Modules
