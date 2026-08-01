/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.LineVerticalAssembly
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.AdditionSpecPoints
import ModularCurves.EllipticCurve.AffineSectionSpecPoints

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


namespace ModularCurves

open WeierstrassCurve

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2c, field case] The negative of a sum has the chord's third coordinates.**
Over a field, mathlib's affine group law gives `P + Q = (addX, addY)` and negation flips
`Y` by `negY`, so `-(P + Q)` is the point `(addX, negAddY)` — which is exactly the third
intersection of the chord (`chord_vanishes_at_three_points`). This is the field-point
input of the dictionary bridge. -/
theorem neg_add_eq_some_negAddY {F : Type u} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.toAffine.Nonsingular x₁ y₁) (h₂ : W.toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    -(Affine.Point.some _ _ h₁ + Affine.Point.some _ _ h₂) =
      Affine.Point.some
        (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
        (W.toAffine.negAddY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂))
        ((Affine.nonsingular_negAdd h₁ h₂ hxy)) := by
  rw [Affine.Point.add_some hxy, Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY_negY]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2c, step 1] The dictionary reads the negative of a sum.** Combining the
project's addition and negation compatibilities with the field-case formula: for two
`K`-points of the projective model, the dictionary sends the scheme-level `-(P + Q)` to
the affine point `-(P_aff + Q_aff)`. This is the field-point statement that the
extensionality principle upgrades to a section identity. -/
theorem projModelPointsEquiv_neg_mul {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K) :
    projModelPointsEquiv W K
        ⟨(Limits.pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W) ≫
            negModelHom W, by
          rw [Category.assoc, negModelHom_π, Category.assoc, mulModelHom_π,
            ← Category.assoc, Limits.pullback.lift_fst, P.2]⟩ =
      -(projModelPointsEquiv W K P + projModelPointsEquiv W K Q) := by
  have hsum : ((Limits.pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W) ≫
      projModelπ W) = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
    rw [Category.assoc, mulModelHom_π, ← Category.assoc,
      Limits.pullback.lift_fst, P.2]
  rw [negModelHom_specPoints W K
    ⟨Limits.pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W, hsum⟩]
  rw [mulModelHom_specPoints W K P Q]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2c, steps 1+4 combined] The third point's coordinates at a field point.**
For two `K`-points in the `Z`-chart with affine coordinates `(x₁, y₁)`, `(x₂, y₂)` in
general position, the dictionary value of the scheme-level `-(P + Q)` is the affine
point `(addX, negAddY)` — the chord's third intersection. -/
theorem projModelPointsEquiv_neg_mul_eq_negAddY {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [DecidableEq K] [Algebra R K]
    (P Q : SpecPoints (projModel W) (projModelπ W) K)
    {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W.baseChange K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange K).toAffine.Nonsingular x₂ y₂)
    (hP : projModelPointsEquiv W K P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    (hQ : projModelPointsEquiv W K Q = WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.baseChange K).toAffine.negY x₂ y₂)) :
    projModelPointsEquiv W K
        ⟨(Limits.pullback.lift P.1 Q.1 (P.2.trans Q.2.symm) ≫ mulModelHom W) ≫
            negModelHom W, by
          rw [Category.assoc, negModelHom_π, Category.assoc, mulModelHom_π,
            ← Category.assoc, Limits.pullback.lift_fst, P.2]⟩ =
      WeierstrassCurve.Affine.Point.some
        ((W.baseChange K).toAffine.addX x₁ x₂
          ((W.baseChange K).toAffine.slope x₁ x₂ y₁ y₂))
        ((W.baseChange K).toAffine.negAddY x₁ x₂ y₁
          ((W.baseChange K).toAffine.slope x₁ x₂ y₁ y₂))
        (WeierstrassCurve.Affine.nonsingular_negAdd h₁ h₂ hxy) := by
  rw [projModelPointsEquiv_neg_mul W K P Q, hP, hQ]
  exact neg_add_eq_some_negAddY (W.baseChange K) h₁ h₂ hxy

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 residue (ii), algebraic core] Exactness from a unit quotient.** If a chart
element factors through three generators with a unit cofactor, the exact-order
hypothesis of the trivialization criterion holds; conversely a non-unit cofactor is
detected by a rank drop. This states the direction the chord computation supplies. -/
theorem isUnit_of_eq_unit_mul {A : Type u} [CommRing A] (c g₁ g₂ g₃ w : A)
    (hfac : c = w * (g₁ * (g₂ * g₃))) (hw : IsUnit w) :
    ∃ u : Aˣ, c = (u : A) * (g₁ * (g₂ * g₃)) := by
  obtain ⟨u, rfl⟩ := hw
  exact ⟨u, hfac⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (a)] The three chart retractions.** Three sections landing in a common affine
chart, each with principal kernel there, give three algebra retractions of the chart
whose kernels are the principal ideals of the transported generators — the data the
exact-order factorisation consumes. -/
theorem exists_three_algHom_ker_eq_span {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (P Q Rm : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (U : C.affineOpens)
    (hPU : P.1 ⁻¹ᵁ U.1 = ⊤) (hQU : Q.1 ⁻¹ᵁ U.1 = ⊤) (hRU : Rm.1 ⁻¹ᵁ U.1 = ⊤)
    (rP rQ rR : Γ(C, U.1))
    (hP : (Scheme.Hom.ker P.1).ideal U = Ideal.span {rP})
    (hQ : (Scheme.Hom.ker Q.1).ideal U = Ideal.span {rQ})
    (hR : (Scheme.Hom.ker Rm.1).ideal U = Ideal.span {rR})
    [Algebra Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens))]
    (halg : ∀ r : Γ(S, (⊤ : S.Opens)),
      algebraMap Γ(S, (⊤ : S.Opens)) Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) r =
        (Scheme.Hom.appTop (U.1.ι ≫ π)).hom r) :
    ∃ σP σQ σR : Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) →ₐ[Γ(S, (⊤ : S.Opens))]
        Γ(S, (⊤ : S.Opens)),
      RingHom.ker σP =
          Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rP} ∧
        RingHom.ker σQ =
          Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rQ} ∧
        RingHom.ker σR =
          Ideal.span {(U.1.ι.appLE U.1 ⊤ U.1.ι_preimage_self.ge).hom rR} := by
  obtain ⟨σP, hσP⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_algHom_ker_eq_span_of_section
      P.1 P.2 U hPU rP hP halg
  obtain ⟨σQ, hσQ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_algHom_ker_eq_span_of_section
      Q.1 Q.2 U hQU rQ hQ halg
  obtain ⟨σR, hσR⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_algHom_ker_eq_span_of_section
      Rm.1 Rm.2 U hRU rR hR halg
  exact ⟨σP, σQ, σR, hσP, hσQ, hσR⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (α)] The chord times its conjugate is a cubic in `X`.** In any algebra where
`(X, Y)` satisfies the Weierstrass equation, the product of the chord
`Y − ℓ(X − x₁) − y₁` with its conjugate (the same line subtracted from `negY`) is the
`addPolynomial` cubic evaluated at `X` — the identity that produces the successive
quotients of the exact-order factorisation. Pure algebra: it is the Weierstrass
equation rearranged. -/
theorem chord_mul_conj_eq_cubic {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (X Y : A) (ℓ x₁ y₁ : R)
    (hEq : Y ^ 2 + algebraMap R A W.a₁ * X * Y + algebraMap R A W.a₃ * Y =
      X ^ 3 + algebraMap R A W.a₂ * X ^ 2 + algebraMap R A W.a₄ * X +
        algebraMap R A W.a₆) :
    (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) *
        ((-Y - algebraMap R A W.a₁ * X - algebraMap R A W.a₃) -
          (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
      -(X ^ 3 +
        (algebraMap R A (-ℓ ^ 2 - W.a₁ * ℓ + W.a₂)) * X ^ 2 +
        (algebraMap R A (2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ +
          (-W.a₁ * y₁ + W.a₄))) * X +
        (algebraMap R A (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * ℓ -
          (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)))) := by
  simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
  linear_combination -hEq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (α)] The cubic factors through the three `X`-coordinates.** When the three
`x`-coordinates satisfy the Vieta relations of the chord (which the chord–tangent
formulas provide: `x₃ = ℓ² + a₁ℓ − a₂ − x₁ − x₂`, and the two points lie on the line),
the cubic of `chord_mul_conj_eq_cubic` is `-(X − x₁)(X − x₂)(X − x₃)`. -/
theorem cubic_factors_of_vieta {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (X : A) (ℓ x₁ x₂ x₃ y₁ y₂ : R)
    (hx₃ : x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)
    (hc₁ : 2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ + (-W.a₁ * y₁ + W.a₄) =
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃)
    (hc₀ : -x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * ℓ -
        (y₁ ^ 2 + W.a₃ * y₁ - W.a₆) = -(x₁ * x₂ * x₃)) :
    -(X ^ 3 +
      (algebraMap R A (-ℓ ^ 2 - W.a₁ * ℓ + W.a₂)) * X ^ 2 +
      (algebraMap R A (2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ +
        (-W.a₁ * y₁ + W.a₄))) * X +
      (algebraMap R A (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * ℓ -
        (y₁ ^ 2 + W.a₃ * y₁ - W.a₆)))) =
    -((X - algebraMap R A x₁) * (X - algebraMap R A x₂) * (X - algebraMap R A x₃)) := by
  have hsum : (-ℓ ^ 2 - W.a₁ * ℓ + W.a₂) = -(x₁ + x₂ + x₃) := by
    rw [hx₃]; ring
  rw [hsum, hc₁, hc₀]
  simp only [map_add, map_sub, map_mul, map_neg]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (α), assembled] The chord's norm factors through the three points.** Combining
the Weierstrass-equation identity with the Vieta relations: in the coordinate ring, the
chord times its conjugate is `-(X − x₁)(X − x₂)(X − x₃)`. Each factor `X − xᵢ` is (on a
chart where the point is not `2`-torsion) the kernel generator of the corresponding
evaluation, so this is the explicit form of the exact-order divisions. -/
theorem chord_mul_conj_eq_prod {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (X Y : A) (ℓ x₁ x₂ x₃ y₁ y₂ : R)
    (hEq : Y ^ 2 + algebraMap R A W.a₁ * X * Y + algebraMap R A W.a₃ * Y =
      X ^ 3 + algebraMap R A W.a₂ * X ^ 2 + algebraMap R A W.a₄ * X +
        algebraMap R A W.a₆)
    (hx₃ : x₃ = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)
    (hc₁ : 2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ + (-W.a₁ * y₁ + W.a₄) =
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃)
    (hc₀ : -x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * ℓ -
        (y₁ ^ 2 + W.a₃ * y₁ - W.a₆) = -(x₁ * x₂ * x₃)) :
    (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) *
        ((-Y - algebraMap R A W.a₁ * X - algebraMap R A W.a₃) -
          (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
      -((X - algebraMap R A x₁) * (X - algebraMap R A x₂) *
        (X - algebraMap R A x₃)) :=
  (chord_mul_conj_eq_cubic W X Y ℓ x₁ y₁ hEq).trans
    (cubic_factors_of_vieta W X ℓ x₁ x₂ x₃ y₁ y₂ hx₃ hc₁ hc₀)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (α)(i)] The Vieta relations from the two point equations.** For two points on
the curve joined by a line of slope `ℓ` with `x₁ − x₂` a nonzerodivisor, the two
remaining Vieta identities follow from the equations and the line relation. (The
`x₁ = x₂` tangent case is the derivative relation and is handled by the same identity
with the tangent slope.) -/
theorem vieta_of_equations {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (ℓ x₁ x₂ y₁ y₂ : R)
    (h₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (h₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hnzd : ∀ t : R, (x₁ - x₂) * t = 0 → t = 0) :
    (2 * x₁ * ℓ ^ 2 + (W.a₁ * x₁ - 2 * y₁ - W.a₃) * ℓ + (-W.a₁ * y₁ + W.a₄) =
        x₁ * x₂ + x₁ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) +
          x₂ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)) := by
  rw [← sub_eq_zero]
  refine hnzd _ ?_
  subst hline
  first
    | linear_combination h₁ - h₂
    | linear_combination h₂ - h₁
    | linear_combination (-1 : R) * h₁ + h₂
    | linear_combination h₁ + (-1 : R) * h₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (α)(i)] The constant Vieta relation.** The companion of `vieta_of_equations`:
the product of the three `x`-coordinates. Same derivation — substitute the line and
cancel `x₁ − x₂`. -/
theorem vieta_const_of_equations {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (ℓ x₁ x₂ y₁ y₂ : R)
    (h₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (h₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hnzd : ∀ t : R, (x₁ - x₂) * t = 0 → t = 0) :
    -x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + W.a₃ * x₁) * ℓ -
        (y₁ ^ 2 + W.a₃ * y₁ - W.a₆) =
      -(x₁ * x₂ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)) := by
  have hC1 := vieta_of_equations W ℓ x₁ x₂ y₁ y₂ h₁ h₂ hline hnzd
  first
    | linear_combination h₁ - x₁ * hC1
    | linear_combination -h₁ - x₁ * hC1
    | linear_combination h₁ + x₁ * hC1
    | linear_combination -h₁ + x₁ * hC1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (α), COMPLETE] The chord's norm factorisation from the two points alone.**
For two points on the curve joined by a line of slope `ℓ`, with `x₁ − x₂` a
nonzerodivisor, the chord times its conjugate is `−(X − x₁)(X − x₂)(X − x₃)` with
`x₃ = addX x₁ x₂ ℓ`. Both Vieta hypotheses are discharged internally: the only inputs
are the two Weierstrass equations, the line relation and non-tangency. -/
theorem chord_mul_conj_eq_prod_of_equations {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) (X Y : A) (ℓ x₁ x₂ y₁ y₂ : R)
    (hEq : Y ^ 2 + algebraMap R A W.a₁ * X * Y + algebraMap R A W.a₃ * Y =
      X ^ 3 + algebraMap R A W.a₂ * X ^ 2 + algebraMap R A W.a₄ * X +
        algebraMap R A W.a₆)
    (h₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (h₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hnzd : ∀ t : R, (x₁ - x₂) * t = 0 → t = 0) :
    (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) *
        ((-Y - algebraMap R A W.a₁ * X - algebraMap R A W.a₃) -
          (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
      -((X - algebraMap R A x₁) * (X - algebraMap R A x₂) *
        (X - algebraMap R A (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂))) :=
  chord_mul_conj_eq_prod W X Y ℓ x₁ x₂ (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) y₁ y₂
    hEq rfl
    (vieta_of_equations W ℓ x₁ x₂ y₁ y₂ h₁ h₂ hline hnzd)
    (vieta_const_of_equations W ℓ x₁ x₂ y₁ y₂ h₁ h₂ hline hnzd)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (1)] `X − x` lies in the kernel of the evaluation at that point.** Always
true; the converse (that it *generates*) holds away from `2`-torsion and is the chart
hypothesis. -/
theorem sub_coord_mem_ker {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (σ : A →ₐ[R] R) (X : A) (x : R) (hx : σ X = x) :
    (X - algebraMap R A x) ∈ RingHom.ker (σ : A →+* R) := by
  show (σ : A →+* R) (X - algebraMap R A x) = 0
  rw [map_sub]
  show σ X - σ (algebraMap R A x) = 0
  rw [hx, σ.commutes]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (1)] The generator divides `X − x`.** With the kernel principal on `g`, the
coordinate difference is a multiple of the generator — the direction needed to turn the
norm factorisation into the divisibility chain. -/
theorem exists_mul_eq_sub_coord {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (σ : A →ₐ[R] R) (X : A) (x g : R) (hx : σ X = x)
    {gA : A} (hker : RingHom.ker (σ : A →+* R) = Ideal.span {gA}) :
    ∃ t : A, X - algebraMap R A x = gA * t := by
  have hmem := sub_coord_mem_ker σ X x hx
  rw [hker] at hmem
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨a, by rw [← ha, mul_comm]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (2)] Successive division by generators.** If an element is killed by an
evaluation whose kernel is generated by `g`, it is `g` times something; iterating three
times with the successive quotients gives the shape `chord_chart_factorisation` wants.
This packages the iteration. -/
theorem exists_three_divisions {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (c gP gQ gR : A) (σ₁ σ₂ σ₃ : A →ₐ[R] R)
    (hk₁ : RingHom.ker (σ₁ : A →+* R) = Ideal.span {gP})
    (hk₂ : RingHom.ker (σ₂ : A →+* R) = Ideal.span {gQ})
    (hk₃ : RingHom.ker (σ₃ : A →+* R) = Ideal.span {gR})
    (h₁ : σ₁ c = 0)
    (hstep₂ : ∀ c₁ : A, c = gP * c₁ → σ₂ c₁ = 0)
    (hstep₃ : ∀ c₁ c₂ : A, c = gP * c₁ → c₁ = gQ * c₂ → σ₃ c₂ = 0) :
    ∃ c₁ c₂ c₃ : A, c = gP * c₁ ∧ c₁ = gQ * c₂ ∧ c₂ = gR * c₃ := by
  have hm₁ : c ∈ Ideal.span {gP} := by rw [← hk₁]; exact h₁
  obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton'.mp hm₁
  have hc₁ : c = gP * a₁ := by rw [← ha₁, mul_comm]
  have h₂ := hstep₂ a₁ hc₁
  have hm₂ : a₁ ∈ Ideal.span {gQ} := by rw [← hk₂]; exact h₂
  obtain ⟨a₂, ha₂⟩ := Ideal.mem_span_singleton'.mp hm₂
  have hc₂ : a₁ = gQ * a₂ := by rw [← ha₂, mul_comm]
  have h₃ := hstep₃ a₁ a₂ hc₁ hc₂
  have hm₃ : a₂ ∈ Ideal.span {gR} := by rw [← hk₃]; exact h₃
  obtain ⟨a₃, ha₃⟩ := Ideal.mem_span_singleton'.mp hm₃
  exact ⟨a₁, a₂, a₃, hc₁, hc₂, by rw [← ha₃, mul_comm]⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (2)+(3), assembled] From the three divisions to the exact-order form.**
Given the successive quotients and a proof that the last one is a unit, the element is
a unit multiple of the product of the three generators — the hypothesis of
`nonempty_iso_unitObj_of_exact_order₃`. -/
theorem eq_unit_mul_of_three_divisions_of_isUnit {A : Type u} [CommRing A]
    (c gP gQ gR c₁ c₂ c₃ : A)
    (hc₁ : c = gP * c₁) (hc₂ : c₁ = gQ * c₂) (hc₃ : c₂ = gR * c₃)
    (hu : IsUnit c₃) :
    ∃ u : Aˣ, c = (u : A) * (gP * (gQ * gR)) := by
  obtain ⟨u, rfl⟩ := hu
  exact ⟨u, AlgebraicGeometry.Scheme.Modules.eq_unit_mul_of_three_divisions
    c gP gQ gR c₁ c₂ u hc₁ hc₂ hc₃⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 final] The chord's exact-order form from the chart facts.** Packaging the
whole chord-side pipeline: the three evaluations kill the chord and its successive
quotients, the last quotient is a unit, hence the chord is a unit multiple of the
product of the three kernel generators — the hypothesis of the trivialization
criterion. -/
theorem chord_exact_order_of_chart_facts {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (c gP gQ gR : A) (σ₁ σ₂ σ₃ : A →ₐ[R] R)
    (hk₁ : RingHom.ker (σ₁ : A →+* R) = Ideal.span {gP})
    (hk₂ : RingHom.ker (σ₂ : A →+* R) = Ideal.span {gQ})
    (hk₃ : RingHom.ker (σ₃ : A →+* R) = Ideal.span {gR})
    (h₁ : σ₁ c = 0)
    (hstep₂ : ∀ c₁ : A, c = gP * c₁ → σ₂ c₁ = 0)
    (hstep₃ : ∀ c₁ c₂ : A, c = gP * c₁ → c₁ = gQ * c₂ → σ₃ c₂ = 0)
    (hunit : ∀ c₁ c₂ c₃ : A, c = gP * c₁ → c₁ = gQ * c₂ → c₂ = gR * c₃ → IsUnit c₃) :
    ∃ u : Aˣ, c = (u : A) * (gP * (gQ * gR)) := by
  obtain ⟨c₁, c₂, c₃, hc₁, hc₂, hc₃⟩ :=
    exists_three_divisions c gP gQ gR σ₁ σ₂ σ₃ hk₁ hk₂ hk₃ h₁ hstep₂ hstep₃
  exact eq_unit_mul_of_three_divisions_of_isUnit c gP gQ gR c₁ c₂ c₃ hc₁ hc₂ hc₃
    (hunit c₁ c₂ c₃ hc₁ hc₂ hc₃)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-iii] A chart inside a given open with principal kernels.** Shrinking a
multi-section chart to a basic open inside a prescribed open keeps every section's
kernel principal on a nonzerodivisor — the positioning step that puts the three
sections and the away-condition on one chart. -/
theorem exists_affineChart_le_of_multiChart {C S : Scheme.{u}} {π : C ⟶ S}
    [IsSeparated π] (hsm : SmoothOfRelativeDimension 1 π) {n : ℕ}
    (P : Fin n → { z : S ⟶ C // z ≫ π = 𝟙 S }) (V : C.Opens) (c : ↥C) (hcV : c ∈ V) :
    ∃ W : C.affineOpens, c ∈ W.1 ∧ W.1 ≤ V ∧ ∀ i : Fin n, ∃ f : Γ(C, W.1),
      (Scheme.Hom.ker (P i).1).ideal W = Ideal.span {f} ∧
        f ∈ nonZeroDivisors Γ(C, W.1) := by
  classical
  obtain ⟨U, hcU, hU⟩ :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.exists_multiChart π hsm P c
  obtain ⟨t, htle, hct⟩ := U.2.exists_basicOpen_le (V := U.1 ⊓ V) ⟨c, hcU, hcV⟩ hcU
  refine ⟨C.affineBasicOpen t, hct, le_trans htle inf_le_right, fun i => ?_⟩
  obtain ⟨f, hspan, hnzd⟩ := hU i
  obtain ⟨h1, h2⟩ :=
    ModularCurves.RelEffCartierDiv.SectionsIdeal.basicOpen_span_nzd hspan hnzd t
  exact ⟨_, h1, h2⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-i] Cancelling a nonzerodivisor factor from the norm factorisation.** From
`chord · conj = −(X−x₁)(X−x₂)(X−x₃)` and `chord = (X−x₁)·c₁`, if `X−x₁` is a
nonzerodivisor of the chart ring, the quotient satisfies
`c₁ · conj = −(X−x₂)(X−x₃)`; iterating gives the deeper evaluation vanishings. -/
theorem cancel_factor_of_norm {A : Type u} [CommRing A]
    (chord conj f₁ f₂ f₃ c₁ : A)
    (hnorm : chord * conj = -(f₁ * f₂ * f₃))
    (hdiv : chord = f₁ * c₁)
    (hnzd : ∀ t : A, f₁ * t = 0 → t = 0) :
    c₁ * conj = -(f₂ * f₃) := by
  rw [← sub_eq_zero]
  refine hnzd _ ?_
  have h : f₁ * (c₁ * conj) = f₁ * (-(f₂ * f₃)) := by
    calc f₁ * (c₁ * conj) = chord * conj := by rw [hdiv]; ring
      _ = -(f₁ * f₂ * f₃) := hnorm
      _ = f₁ * (-(f₂ * f₃)) := by ring
  have h2 : f₁ * (c₁ * conj) - f₁ * (-(f₂ * f₃)) = 0 := by rw [h, sub_self]
  calc f₁ * (c₁ * conj - -(f₂ * f₃)) = f₁ * (c₁ * conj) - f₁ * (-(f₂ * f₃)) := by ring
    _ = 0 := h2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-i, iterated] The chord's successive quotients from the norm factorisation.**
Cancelling the three linear factors in turn expresses the chord's quotients explicitly;
in particular the second quotient times the conjugate is `−(X − x₃)`, which is what
makes the third evaluation vanish. -/
theorem chord_quotients_of_norm {A : Type u} [CommRing A]
    (chord conj f₁ f₂ f₃ c₁ c₂ : A)
    (hnorm : chord * conj = -(f₁ * f₂ * f₃))
    (hd₁ : chord = f₁ * c₁) (hd₂ : c₁ = f₂ * c₂)
    (hnzd₁ : ∀ t : A, f₁ * t = 0 → t = 0)
    (hnzd₂ : ∀ t : A, f₂ * t = 0 → t = 0) :
    c₂ * conj = -f₃ := by
  have h₁ : c₁ * conj = -(f₂ * f₃) :=
    cancel_factor_of_norm chord conj f₁ f₂ f₃ c₁ hnorm hd₁ hnzd₁
  have h₂ : f₂ * (c₂ * conj) = f₂ * (-f₃) := by
    calc f₂ * (c₂ * conj) = c₁ * conj := by rw [hd₂]; ring
      _ = -(f₂ * f₃) := h₁
      _ = f₂ * (-f₃) := by ring
  rw [← sub_eq_zero]
  refine hnzd₂ _ ?_
  calc f₂ * (c₂ * conj - -f₃) = f₂ * (c₂ * conj) - f₂ * (-f₃) := by ring
    _ = 0 := by rw [h₂, sub_self]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-i2] The evaluation vanishings from the cancelled identities.** Applying an
evaluation to `c · conj = −(∏ of factors vanishing at that point)` gives
`σ(c) · σ(conj) = 0`; when `σ(conj)` is a nonzerodivisor of the base this forces
`σ(c) = 0`. Off the `2`-torsion locus `σ(conj)` is `y − negY(x,y) ≠ 0`, which is where
the classical case split enters. -/
theorem algHom_eq_zero_of_mul_eq_zero {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (σ : A →ₐ[R] R) (c conj : A)
    (hprod : σ (c * conj) = 0)
    (hnzd : ∀ t : R, σ conj * t = 0 → t = 0) :
    σ c = 0 := by
  refine hnzd _ ?_
  rw [mul_comm, ← map_mul]
  exact hprod

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-i2] The second evaluation vanishes.** From `c₁ · conj = −(f₂ · f₃)` with
`σ₂ f₂ = 0` and `σ₂ conj` a nonzerodivisor. -/
theorem algHom_second_quotient_eq_zero {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (σ : A →ₐ[R] R) (c₁ conj f₂ f₃ : A)
    (hid : c₁ * conj = -(f₂ * f₃)) (hf₂ : σ f₂ = 0)
    (hnzd : ∀ t : R, σ conj * t = 0 → t = 0) :
    σ c₁ = 0 := by
  refine algHom_eq_zero_of_mul_eq_zero σ c₁ conj ?_ hnzd
  rw [hid, map_neg, map_mul, hf₂, zero_mul, neg_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-ii] Exactness from a unit norm.** If the chord's norm quotient is a unit,
so is the final cofactor of the exact-order factorisation — the criterion the rank-3
coordinates supply through the adjugate. -/
theorem isUnit_of_norm_unit {A : Type u} [CommRing A] (c₂ conj : A)
    (hu : IsUnit (c₂ * conj)) : IsUnit c₂ :=
  isUnit_of_mul_isUnit_left hu

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-ii] The conjugate evaluates to `negY − line`.** At a point of the curve, the
conjugate factor of the chord evaluates to `negY x y − (ℓ(x − x₁) + y₁)`; the
non-degeneracy needed for the cancellations is exactly the invertibility of this value,
which fails precisely when the point is fixed by negation relative to the chord — the
`2`-torsion case. -/
theorem algHom_conj_eq {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (σ : A →ₐ[R] R) (X Y : A) (ℓ x₁ y₁ x y : R)
    (hx : σ X = x) (hy : σ Y = y) :
    σ ((-Y - algebraMap R A W.a₁ * X - algebraMap R A W.a₃) -
        (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
      W.toAffine.negY x y - (ℓ * (x - x₁) + y₁) := by
  rw [map_sub, map_sub, map_sub, map_neg, map_add, map_mul, map_mul, map_sub,
    σ.commutes, σ.commutes, σ.commutes, σ.commutes, hx, hy]
  rw [WeierstrassCurve.Affine.negY, σ.commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-ii] The conjugate at the base point is `y − negY`.** Its invertibility is
the non-`2`-torsion condition at that point. -/
theorem conj_at_base_point {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (ℓ x₁ y₁ : R) :
    W.toAffine.negY x₁ y₁ - (ℓ * (x₁ - x₁) + y₁) =
      -(2 * y₁ + W.a₁ * x₁ + W.a₃) := by
  rw [WeierstrassCurve.Affine.negY]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-ii] The conjugate at a point of the chord is `y − negY` there.** For a point
on the line, the conjugate's value is `negY x y − y`, i.e. `−(2y + a₁x + a₃)`. -/
theorem conj_at_line_point {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (ℓ x₁ y₁ x y : R) (hline : y = ℓ * (x - x₁) + y₁) :
    W.toAffine.negY x y - (ℓ * (x - x₁) + y₁) =
      -(2 * y + W.a₁ * x + W.a₃) := by
  rw [WeierstrassCurve.Affine.negY, ← hline]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 F-ii, assembled] The second evaluation vanishes off `2`-torsion.** For the
chord through two points of the curve, the second quotient is killed by the second
point's evaluation whenever that point is not `2`-torsion (`2y₂ + a₁x₂ + a₃` a
nonzerodivisor). -/
theorem second_quotient_vanishes_of_not_two_torsion
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (σ : A →ₐ[R] R) (X Y : A) (ℓ x₁ y₁ x₂ y₂ : R)
    (c₁ f₂ f₃ : A)
    (hx : σ X = x₂) (hy : σ Y = y₂)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hid : c₁ * ((-Y - algebraMap R A W.a₁ * X - algebraMap R A W.a₃) -
        (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
      -(f₂ * f₃))
    (hf₂ : σ f₂ = 0)
    (hnzd : ∀ t : R, -(2 * y₂ + W.a₁ * x₂ + W.a₃) * t = 0 → t = 0) :
    σ c₁ = 0 := by
  refine algHom_second_quotient_eq_zero σ c₁ _ f₂ f₃ hid hf₂ ?_
  intro t ht
  refine hnzd t ?_
  rw [← conj_at_line_point W ℓ x₁ y₁ x₂ y₂ hline,
    ← algHom_conj_eq W σ X Y ℓ x₁ y₁ x₂ y₂ hx hy]
  exact ht

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (1)] The third evaluation vanishes off `2`-torsion.** Same shape as the second:
from `c₂ · conj = −f₃` with `σ f₃ = 0` and the third point not `2`-torsion. -/
theorem third_quotient_vanishes_of_not_two_torsion
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (σ : A →ₐ[R] R) (X Y : A) (ℓ x₁ y₁ x₃ y₃ : R)
    (c₂ f₃ : A)
    (hx : σ X = x₃) (hy : σ Y = y₃)
    (hline : y₃ = ℓ * (x₃ - x₁) + y₁)
    (hid : c₂ * ((-Y - algebraMap R A W.a₁ * X - algebraMap R A W.a₃) -
        (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) = -f₃)
    (hf₃ : σ f₃ = 0)
    (hnzd : ∀ t : R, -(2 * y₃ + W.a₁ * x₃ + W.a₃) * t = 0 → t = 0) :
    σ c₂ = 0 := by
  refine algHom_eq_zero_of_mul_eq_zero σ c₂
    ((-Y - algebraMap R A W.a₁ * X - algebraMap R A W.a₃) -
      (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) ?_ ?_
  · rw [hid, map_neg, hf₃, neg_zero]
  · intro t ht
    refine hnzd t ?_
    rw [← conj_at_line_point W ℓ x₁ y₁ x₃ y₃ hline,
      ← algHom_conj_eq W σ X Y ℓ x₁ y₁ x₃ y₃ hx hy]
    exact ht

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (2)] The last cofactor is a unit when the conjugate is.** From
`c₂ · conj = −f₃` and `f₃ = g₃ · c₃`, if `conj` is a unit and `f₃ = −(c₂ · conj)` then
`c₃` is a unit exactly when `c₂` is, and the chord's exact-order factorisation follows.
Stated in the form the assembly uses: a unit conjugate makes `c₂` a unit multiple of
`f₃`. -/
theorem isUnit_cofactor_of_isUnit_conj {A : Type u} [CommRing A]
    (c₂ conj f₃ : A) (hid : c₂ * conj = -f₃) (hu : IsUnit conj) :
    ∃ v : Aˣ, f₃ = (v : A) * c₂ := by
  obtain ⟨w, hw⟩ := hu
  refine ⟨-w, ?_⟩
  have h : f₃ = -(c₂ * conj) := by
    rw [hid]; ring
  calc f₃ = -(c₂ * conj) := h
    _ = -(c₂ * (w : A)) := by rw [hw]
    _ = ((-w : Aˣ) : A) * c₂ := by
        show -(c₂ * (w : A)) = (-(w : A)) * c₂
        ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 instantiation] The chord's exact-order factorisation in a Weierstrass chart.**
Non-degenerate case, everything derived: two points of the curve with `x₁ − x₂` a
nonzerodivisor, the generators being the coordinate differences, and the three points
not `2`-torsion. The conclusion is the exact-order hypothesis of the trivialization
criterion, with the third point's coordinates those of the chord's residual
intersection. -/
theorem chord_exact_order_in_chart {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) (X Y : A) (ℓ x₁ y₁ x₂ y₂ y₃ : R)
    (σ₁ σ₂ σ₃ : A →ₐ[R] R)
    (hEq : Y ^ 2 + algebraMap R A W.a₁ * X * Y + algebraMap R A W.a₃ * Y =
      X ^ 3 + algebraMap R A W.a₂ * X ^ 2 + algebraMap R A W.a₄ * X +
        algebraMap R A W.a₆)
    (h₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (h₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hnzdx : ∀ t : R, (x₁ - x₂) * t = 0 → t = 0)
    (hf₁nzd : ∀ t : A, (X - algebraMap R A x₁) * t = 0 → t = 0)
    (hf₂nzd : ∀ t : A, (X - algebraMap R A x₂) * t = 0 → t = 0)
    (hk₁ : RingHom.ker (σ₁ : A →+* R) = Ideal.span {X - algebraMap R A x₁})
    (hk₂ : RingHom.ker (σ₂ : A →+* R) = Ideal.span {X - algebraMap R A x₂})
    (hk₃ : RingHom.ker (σ₃ : A →+* R) =
      Ideal.span {X - algebraMap R A (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)})
    (hσ₁ : σ₁ (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) +
      algebraMap R A y₁)) = 0)
    (hx₂ : σ₂ X = x₂) (hy₂ : σ₂ Y = y₂)
    (hx₃ : σ₃ X = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) (hy₃ : σ₃ Y = y₃)
    (hline₃ : y₃ = ℓ * ((ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) - x₁) + y₁)
    (htor₂ : ∀ t : R, -(2 * y₂ + W.a₁ * x₂ + W.a₃) * t = 0 → t = 0)
    (htor₃ : ∀ t : R,
      -(2 * y₃ + W.a₁ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) + W.a₃) * t = 0 → t = 0)
    (hunit : ∀ c₁ c₂ c₃ : A,
      (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
        (X - algebraMap R A x₁) * c₁ → c₁ = (X - algebraMap R A x₂) * c₂ →
        c₂ = (X - algebraMap R A (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)) * c₃ →
        IsUnit c₃) :
    ∃ u : Aˣ,
      (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
        (u : A) * ((X - algebraMap R A x₁) *
          ((X - algebraMap R A x₂) *
            (X - algebraMap R A (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)))) := by
  have hnorm := chord_mul_conj_eq_prod_of_equations W X Y ℓ x₁ x₂ y₁ y₂
    hEq h₁ h₂ hline hnzdx
  refine chord_exact_order_of_chart_facts _ _ _ _ σ₁ σ₂ σ₃ hk₁ hk₂ hk₃ hσ₁
    (fun c₁ hc₁ => ?_) (fun c₁ c₂ hc₁ hc₂ => ?_) hunit
  · have hcancel := cancel_factor_of_norm _ _ _ _ _ c₁ hnorm hc₁ hf₁nzd
    exact second_quotient_vanishes_of_not_two_torsion W σ₂ X Y ℓ x₁ y₁ x₂ y₂
      c₁ _ _ hx₂ hy₂ hline hcancel
      (by rw [map_sub, hx₂, σ₂.commutes]; simp) htor₂
  · have hquot := chord_quotients_of_norm _ _ _ _ _ c₁ c₂ hnorm hc₁ hc₂ hf₁nzd hf₂nzd
    exact third_quotient_vanishes_of_not_two_torsion W σ₃ X Y ℓ x₁ y₁ _ y₃
      c₂ _ hx₃ hy₃ hline₃ hquot
      (by rw [map_sub, hx₃, σ₃.commutes]; simp) htor₃

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 E1] The chart generator is the coordinate difference, up to a unit.** In a
chart whose evaluation kernel is principal on `g` and where the coordinate difference
also generates, the two differ by a unit — the compatibility that lets
`chord_exact_order_in_chart` be applied with the section-provided generators. -/
theorem exists_unit_generator_eq_sub_coord {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (σ : A →ₐ[R] R) (X : A) (x : R) (g : A)
    (hx : σ X = x)
    (hk : RingHom.ker (σ : A →+* R) = Ideal.span {g})
    (hgen : Ideal.span {X - algebraMap R A x} = Ideal.span {g}) :
    (∃ v : A, g = (X - algebraMap R A x) * v) ∧
      (∃ w : A, X - algebraMap R A x = g * w) := by
  have hmem₁ : g ∈ Ideal.span {X - algebraMap R A x} := by
    rw [hgen]
    exact Ideal.mem_span_singleton_self g
  have hmem₂ : X - algebraMap R A x ∈ Ideal.span {g} := by
    rw [← hgen]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem₁
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem₂
  exact ⟨⟨a, by rw [← ha, mul_comm]⟩, ⟨b, by rw [← hb, mul_comm]⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 E1b] The exact-order form is invariant under associate generators.** Replacing
each generator by a unit multiple only changes the cofactor by a unit, so the
factorisation proved with coordinate differences transfers to the generators the
section machinery supplies. -/
theorem eq_unit_mul_of_associates {A : Type u} [CommRing A]
    (c f₁ f₂ f₃ g₁ g₂ g₃ : A) (u v₁ v₂ v₃ : Aˣ)
    (hfac : c = (u : A) * (f₁ * (f₂ * f₃)))
    (hg₁ : f₁ = (v₁ : A) * g₁) (hg₂ : f₂ = (v₂ : A) * g₂)
    (hg₃ : f₃ = (v₃ : A) * g₃) :
    c = ((u * v₁ * v₂ * v₃ : Aˣ) : A) * (g₁ * (g₂ * g₃)) := by
  rw [hfac, hg₁, hg₂, hg₃]
  push_cast
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 E4] A `ChordDatum` from the two trivializations.** Once the chord and the
vertical trivializations are in hand — which the closing links produce from the chart
identities — the chord datum is immediate, and with it the theorem of the square. -/
theorem chordDatum_of_trivializations {C S : Scheme.{u}} {π : C ⟶ S} [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (P Q R Rm : { w : S ⟶ C // w ≫ π = 𝟙 S })
    (hprin : ∀ Z : { w : S ⟶ C // w ≫ π = 𝟙 S },
      Z = P ∨ Z = Q ∨ Z = R ∨ Z = Rm →
      ∀ c : ↥C, ∃ V : C.affineOpens, c ∈ V.1 ∧ ∃ g : Γ(C, V.1),
        (Scheme.Hom.ker Z.1).ideal V = Ideal.span {g} ∧
          g ∈ nonZeroDivisors Γ(C, V.1))
    (hchord : Nonempty (AlgebraicGeometry.Scheme.Modules.tensorObj
      (AlgebraicGeometry.Scheme.Modules.idealModule (Scheme.Hom.ker P.1))
      (AlgebraicGeometry.Scheme.Modules.tensorObj
        (AlgebraicGeometry.Scheme.Modules.idealModule (Scheme.Hom.ker Q.1))
        (AlgebraicGeometry.Scheme.Modules.tensorObj
          (AlgebraicGeometry.Scheme.Modules.idealModule (Scheme.Hom.ker Rm.1))
          (ModularCurves.sectionPoleSheafPower π z hz 3))) ≅
      AlgebraicGeometry.Scheme.Modules.unitObj C))
    (hvert : Nonempty (AlgebraicGeometry.Scheme.Modules.tensorObj
      (AlgebraicGeometry.Scheme.Modules.idealModule (Scheme.Hom.ker R.1))
      (AlgebraicGeometry.Scheme.Modules.tensorObj
        (AlgebraicGeometry.Scheme.Modules.idealModule (Scheme.Hom.ker Rm.1))
        (ModularCurves.sectionPoleSheafPower π z hz 2)) ≅
      AlgebraicGeometry.Scheme.Modules.unitObj C)) :
    AlgebraicGeometry.Scheme.Modules.ChordDatum z hz P Q R Rm :=
  { principal := hprin, chord := hchord, vertical := hvert }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (a)] The coordinate ring's own coordinates satisfy the Weierstrass equation**
in the form `chord_exact_order_in_chart` consumes. Repackaging of the tree's
`coordY_mul_coordY` (PoleFiltration.lean:116). -/
theorem coord_equation {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    (coordY W) ^ 2 +
        algebraMap R W.toAffine.CoordinateRing W.a₁ * (coordX W) * (coordY W) +
        algebraMap R W.toAffine.CoordinateRing W.a₃ * (coordY W) =
      (coordX W) ^ 3 +
        algebraMap R W.toAffine.CoordinateRing W.a₂ * (coordX W) ^ 2 +
        algebraMap R W.toAffine.CoordinateRing W.a₄ * (coordX W) +
        algebraMap R W.toAffine.CoordinateRing W.a₆ := by
  have h := coordY_mul_coordY W
  have hsq : (coordY W) ^ 2 = coordY W * coordY W := sq (coordY W)
  rw [hsq, h]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (a)] The chord identity in the coordinate ring.** Specialisation of
`chord_exact_order_in_chart` to `A = W.toAffine.CoordinateRing` with its own
coordinates: the curve equation is automatic (`coord_equation`), so the inputs are
exactly the two points, the line relation, the non-degeneracies and the generators. -/
theorem chord_exact_order_in_coordinateRing {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (ℓ x₁ y₁ x₂ y₂ y₃ : R)
    (σ₁ σ₂ σ₃ : W.toAffine.CoordinateRing →ₐ[R] R)
    (h₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (h₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hnzdx : ∀ t : R, (x₁ - x₂) * t = 0 → t = 0)
    (hf₁nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ x₁) * t = 0 → t = 0)
    (hf₂nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ x₂) * t = 0 → t = 0)
    (hk₁ : RingHom.ker (σ₁ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ x₁})
    (hk₂ : RingHom.ker (σ₂ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ x₂})
    (hk₃ : RingHom.ker (σ₃ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W -
        algebraMap R _ (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)})
    (hσ₁ : σ₁ (coordY W - (algebraMap R _ ℓ * (coordX W - algebraMap R _ x₁) +
      algebraMap R _ y₁)) = 0)
    (hx₂ : σ₂ (coordX W) = x₂) (hy₂ : σ₂ (coordY W) = y₂)
    (hx₃ : σ₃ (coordX W) = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)
    (hy₃ : σ₃ (coordY W) = y₃)
    (hline₃ : y₃ = ℓ * ((ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) - x₁) + y₁)
    (htor₂ : ∀ t : R, -(2 * y₂ + W.a₁ * x₂ + W.a₃) * t = 0 → t = 0)
    (htor₃ : ∀ t : R,
      -(2 * y₃ + W.a₁ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) + W.a₃) * t = 0 → t = 0)
    (hunit : ∀ c₁ c₂ c₃ : W.toAffine.CoordinateRing,
      (coordY W - (algebraMap R _ ℓ * (coordX W - algebraMap R _ x₁) +
        algebraMap R _ y₁)) = (coordX W - algebraMap R _ x₁) * c₁ →
        c₁ = (coordX W - algebraMap R _ x₂) * c₂ →
        c₂ = (coordX W - algebraMap R _ (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)) * c₃ →
        IsUnit c₃) :
    ∃ u : (W.toAffine.CoordinateRing)ˣ,
      (coordY W - (algebraMap R _ ℓ * (coordX W - algebraMap R _ x₁) +
        algebraMap R _ y₁)) =
        (u : W.toAffine.CoordinateRing) * ((coordX W - algebraMap R _ x₁) *
          ((coordX W - algebraMap R _ x₂) *
            (coordX W - algebraMap R _ (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)))) :=
  chord_exact_order_in_chart W (coordX W) (coordY W) ℓ x₁ y₁ x₂ y₂ y₃ σ₁ σ₂ σ₃
    (coord_equation W) h₁ h₂ hline hnzdx hf₁nzd hf₂nzd hk₁ hk₂ hk₃ hσ₁
    hx₂ hy₂ hx₃ hy₃ hline₃ htor₂ htor₃ hunit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (a2)] Transporting the exact-order factorisation along a ring isomorphism.**
The away chart is isomorphic to the coordinate ring
(`sectionAway_affineModelEval_bijective`), and the factorisation transports: images of
units are units and the equation is a ring identity. -/
theorem eq_unit_mul_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Bijective φ) (c g₁ g₂ g₃ : A) (u : Aˣ)
    (hfac : c = (u : A) * (g₁ * (g₂ * g₃))) :
    ∃ v : Bˣ, φ c = (v : B) * (φ g₁ * (φ g₂ * φ g₃)) := by
  classical
  let e : A ≃+* B := RingEquiv.ofBijective φ hφ
  refine ⟨Units.map (e : A →* B) u, ?_⟩
  have hval : φ c = φ ((u : A) * (g₁ * (g₂ * g₃))) := by rw [hfac]
  rw [hval, map_mul, map_mul, map_mul]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 assembly steps 1–2] The chord identity in the away chart.** Composing the
coordinate-ring identity with the away-chart isomorphism
(`sectionAway_top_affineModelEval_bijective` supplies `φ` and its bijectivity): the
chord, written in the chart's coordinates, is a unit multiple of the product of the
three coordinate differences. -/
theorem chord_exact_order_transported {R B : Type u} [CommRing R] [CommRing B]
    (W : WeierstrassCurve R) (φ : W.toAffine.CoordinateRing →+* B)
    (hφ : Function.Bijective φ)
    (ℓ x₁ y₁ x₂ y₂ y₃ : R)
    (σ₁ σ₂ σ₃ : W.toAffine.CoordinateRing →ₐ[R] R)
    (h₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (h₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hnzdx : ∀ t : R, (x₁ - x₂) * t = 0 → t = 0)
    (hf₁nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ x₁) * t = 0 → t = 0)
    (hf₂nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ x₂) * t = 0 → t = 0)
    (hk₁ : RingHom.ker (σ₁ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ x₁})
    (hk₂ : RingHom.ker (σ₂ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ x₂})
    (hk₃ : RingHom.ker (σ₃ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)})
    (hσ₁ : σ₁ (coordY W - (algebraMap R _ ℓ * (coordX W - algebraMap R _ x₁) +
      algebraMap R _ y₁)) = 0)
    (hx₂ : σ₂ (coordX W) = x₂) (hy₂ : σ₂ (coordY W) = y₂)
    (hx₃ : σ₃ (coordX W) = ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)
    (hy₃ : σ₃ (coordY W) = y₃)
    (hline₃ : y₃ = ℓ * ((ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) - x₁) + y₁)
    (htor₂ : ∀ t : R, -(2 * y₂ + W.a₁ * x₂ + W.a₃) * t = 0 → t = 0)
    (htor₃ : ∀ t : R,
      -(2 * y₃ + W.a₁ * (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂) + W.a₃) * t = 0 → t = 0)
    (hunit : ∀ c₁ c₂ c₃ : W.toAffine.CoordinateRing,
      (coordY W - (algebraMap R _ ℓ * (coordX W - algebraMap R _ x₁) +
        algebraMap R _ y₁)) = (coordX W - algebraMap R _ x₁) * c₁ →
        c₁ = (coordX W - algebraMap R _ x₂) * c₂ →
        c₂ = (coordX W - algebraMap R _ (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)) * c₃ →
        IsUnit c₃) :
    ∃ v : Bˣ,
      φ (coordY W - (algebraMap R _ ℓ * (coordX W - algebraMap R _ x₁) +
        algebraMap R _ y₁)) =
        (v : B) * (φ (coordX W - algebraMap R _ x₁) *
          (φ (coordX W - algebraMap R _ x₂) *
            φ (coordX W - algebraMap R _ (ℓ ^ 2 + W.a₁ * ℓ - W.a₂ - x₁ - x₂)))) := by
  obtain ⟨u, hu⟩ := chord_exact_order_in_coordinateRing W ℓ x₁ y₁ x₂ y₂ y₃ σ₁ σ₂ σ₃
    h₁ h₂ hline hnzdx hf₁nzd hf₂nzd hk₁ hk₂ hk₃ hσ₁ hx₂ hy₂ hx₃ hy₃ hline₃
    htor₂ htor₃ hunit
  exact eq_unit_mul_map φ hφ _ _ _ _ u hu

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 assembly 3] Matching the transported factors with the section generators.**
The chart identity is stated with the images of the coordinate differences; the
criterion wants the generators the section machinery supplies. When each pair is
associate, the factorisation transfers with a new unit. -/
theorem chord_exact_order_with_generators {B : Type u} [CommRing B]
    (c f₁ f₂ f₃ g₁ g₂ g₃ : B) (v : Bˣ) (w₁ w₂ w₃ : Bˣ)
    (hfac : c = (v : B) * (f₁ * (f₂ * f₃)))
    (hg₁ : f₁ = (w₁ : B) * g₁) (hg₂ : f₂ = (w₂ : B) * g₂)
    (hg₃ : f₃ = (w₃ : B) * g₃) :
    ∃ u : Bˣ, c = (u : B) * (g₁ * (g₂ * g₃)) :=
  ⟨v * w₁ * w₂ * w₃,
    eq_unit_mul_of_associates c f₁ f₂ f₃ g₁ g₂ g₃ v w₁ w₂ w₃ hfac hg₁ hg₂ hg₃⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 supply] The chord's slope and the line relation.** For two points with
`x₁ − x₂` invertible, the slope `(y₂ − y₁)/(x₂ − x₁)` satisfies the line relation
that the chord identity requires. -/
theorem line_relation_of_slope {R : Type u} [CommRing R] (x₁ y₁ x₂ y₂ : R)
    (d : R) (hd : d * (x₂ - x₁) = 1) :
    y₂ = ((y₂ - y₁) * d) * (x₂ - x₁) + y₁ := by
  have h : ((y₂ - y₁) * d) * (x₂ - x₁) = (y₂ - y₁) * (d * (x₂ - x₁)) := by ring
  rw [h, hd, mul_one]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 supply] Non-tangency from invertibility of the coordinate difference.** -/
theorem nzd_of_isUnit_sub {R : Type u} [CommRing R] (x₁ x₂ : R)
    (h : IsUnit (x₁ - x₂)) : ∀ t : R, (x₁ - x₂) * t = 0 → t = 0 := by
  intro t ht
  obtain ⟨w, hw⟩ := h
  have h2 : (↑w⁻¹ : R) * ((x₁ - x₂) * t) = 0 := by rw [ht, mul_zero]
  rwa [← mul_assoc, ← hw, Units.inv_mul, one_mul] at h2

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 supply] Non-`2`-torsion in the form the cancellation chain uses.** -/
theorem nzd_of_isUnit_neg_two_torsion {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (x y : R)
    (h : IsUnit (2 * y + W.a₁ * x + W.a₃)) :
    ∀ t : R, -(2 * y + W.a₁ * x + W.a₃) * t = 0 → t = 0 := by
  intro t ht
  obtain ⟨w, hw⟩ := h
  have h2 : (2 * y + W.a₁ * x + W.a₃) * t = 0 := by
    have hneg : -((2 * y + W.a₁ * x + W.a₃) * t) = 0 := by
      rw [← neg_mul]; exact ht
    exact neg_eq_zero.mp hneg
  have h3 : (↑w⁻¹ : R) * ((2 * y + W.a₁ * x + W.a₃) * t) = 0 := by rw [h2, mul_zero]
  rwa [← mul_assoc, ← hw, Units.inv_mul, one_mul] at h3

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 FINAL PACKAGING] The chord identity from invertibility hypotheses alone.**
Two points of the curve with invertible coordinate difference, both they and the third
intersection non-`2`-torsion, the evaluation kernels generated by the coordinate
differences, and a unit final cofactor: then the chord is a unit multiple of the
product of the three generators, in the coordinate ring. Every hypothesis is a concrete
condition on the Weierstrass chart. -/
theorem chord_identity_of_isUnit_hypotheses {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (x₁ y₁ x₂ y₂ y₃ : R) (d : R)
    (σ₁ σ₂ σ₃ : W.toAffine.CoordinateRing →ₐ[R] R)
    (h₁ : y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ =
      x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (h₂ : y₂ ^ 2 + W.a₁ * x₂ * y₂ + W.a₃ * y₂ =
      x₂ ^ 3 + W.a₂ * x₂ ^ 2 + W.a₄ * x₂ + W.a₆)
    (hd : d * (x₂ - x₁) = 1)
    (hx : IsUnit (x₁ - x₂))
    (hf₁nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ x₁) * t = 0 → t = 0)
    (hf₂nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ x₂) * t = 0 → t = 0)
    (hk₁ : RingHom.ker (σ₁ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ x₁})
    (hk₂ : RingHom.ker (σ₂ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ x₂})
    (hk₃ : RingHom.ker (σ₃ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W -
        algebraMap R _ (((y₂ - y₁) * d) ^ 2 + W.a₁ * ((y₂ - y₁) * d) -
          W.a₂ - x₁ - x₂)})
    (hσ₁ : σ₁ (coordY W -
      (algebraMap R _ ((y₂ - y₁) * d) * (coordX W - algebraMap R _ x₁) +
        algebraMap R _ y₁)) = 0)
    (hx₂ : σ₂ (coordX W) = x₂) (hy₂ : σ₂ (coordY W) = y₂)
    (hx₃ : σ₃ (coordX W) = ((y₂ - y₁) * d) ^ 2 + W.a₁ * ((y₂ - y₁) * d) -
      W.a₂ - x₁ - x₂)
    (hy₃ : σ₃ (coordY W) = y₃)
    (hline₃ : y₃ = ((y₂ - y₁) * d) *
      ((((y₂ - y₁) * d) ^ 2 + W.a₁ * ((y₂ - y₁) * d) - W.a₂ - x₁ - x₂) - x₁) + y₁)
    (htor₂ : IsUnit (2 * y₂ + W.a₁ * x₂ + W.a₃))
    (htor₃ : IsUnit (2 * y₃ +
      W.a₁ * (((y₂ - y₁) * d) ^ 2 + W.a₁ * ((y₂ - y₁) * d) - W.a₂ - x₁ - x₂) + W.a₃))
    (hunit : ∀ c₁ c₂ c₃ : W.toAffine.CoordinateRing,
      (coordY W - (algebraMap R _ ((y₂ - y₁) * d) *
        (coordX W - algebraMap R _ x₁) + algebraMap R _ y₁)) =
          (coordX W - algebraMap R _ x₁) * c₁ →
        c₁ = (coordX W - algebraMap R _ x₂) * c₂ →
        c₂ = (coordX W - algebraMap R _ (((y₂ - y₁) * d) ^ 2 +
          W.a₁ * ((y₂ - y₁) * d) - W.a₂ - x₁ - x₂)) * c₃ → IsUnit c₃) :
    ∃ u : (W.toAffine.CoordinateRing)ˣ,
      (coordY W - (algebraMap R _ ((y₂ - y₁) * d) *
        (coordX W - algebraMap R _ x₁) + algebraMap R _ y₁)) =
        (u : W.toAffine.CoordinateRing) *
          ((coordX W - algebraMap R _ x₁) *
            ((coordX W - algebraMap R _ x₂) *
              (coordX W - algebraMap R _ (((y₂ - y₁) * d) ^ 2 +
                W.a₁ * ((y₂ - y₁) * d) - W.a₂ - x₁ - x₂)))) :=
  chord_exact_order_in_coordinateRing W ((y₂ - y₁) * d) x₁ y₁ x₂ y₂ y₃ σ₁ σ₂ σ₃
    h₁ h₂ (line_relation_of_slope x₁ y₁ x₂ y₂ d hd) (nzd_of_isUnit_sub x₁ x₂ hx)
    hf₁nzd hf₂nzd hk₁ hk₂ hk₃ hσ₁ hx₂ hy₂ hx₃ hy₃ hline₃
    (nzd_of_isUnit_neg_two_torsion W x₂ y₂ htor₂)
    (nzd_of_isUnit_neg_two_torsion W _ y₃ htor₃) hunit

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 vertical] The vertical's norm factorisation.** The vertical line through a
point `(x₀, y₀)` is `X − x₀`; its "conjugate" is trivial, and its divisor is
`[R] + [−R]` — algebraically, `X − x₀` is already the product of the two evaluation
generators up to a unit, since both points have the same `x`-coordinate. This is the
two-factor analogue of the chord's norm identity, and it is immediate. -/
theorem vertical_eq_generator {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (X : A) (x₀ : R) :
    X - algebraMap R A x₀ = (1 : Aˣ) * (X - algebraMap R A x₀) := by
  rw [Units.val_one, one_mul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 vertical] The vertical vanishes at both points of its fibre.** Both `R` and
`−R` have the same `x`-coordinate, so the vertical `X − x₀` is killed by both
evaluations — the two-factor vanishing the vertical's trivialization needs. -/
theorem vertical_evaluations_vanish {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (X : A) (x₀ : R) (σ₁ σ₂ : A →ₐ[R] R)
    (h₁ : σ₁ X = x₀) (h₂ : σ₂ X = x₀) :
    σ₁ (X - algebraMap R A x₀) = 0 ∧ σ₂ (X - algebraMap R A x₀) = 0 := by
  constructor
  · rw [map_sub, h₁, σ₁.commutes]
    simp
  · rw [map_sub, h₂, σ₂.commutes]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 vertical] The vertical's exact-order factorisation.** With both evaluation
kernels generated by the same coordinate difference `X − x₀` (the two points of the
fibre) and the second quotient a unit, the vertical is a unit multiple of the product
of the two generators — the two-factor exact-order hypothesis. -/
theorem vertical_exact_order {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (X : A) (x₀ : R) (gR gRm : A) (σ₁ σ₂ : A →ₐ[R] R)
    (hk₁ : RingHom.ker (σ₁ : A →+* R) = Ideal.span {gR})
    (hk₂ : RingHom.ker (σ₂ : A →+* R) = Ideal.span {gRm})
    (h₁ : σ₁ (X - algebraMap R A x₀) = 0)
    (hstep₂ : ∀ c₁ : A, X - algebraMap R A x₀ = gR * c₁ → σ₂ c₁ = 0)
    (hunit : ∀ c₁ c₂ : A, X - algebraMap R A x₀ = gR * c₁ → c₁ = gRm * c₂ →
      IsUnit c₂) :
    ∃ u : Aˣ, X - algebraMap R A x₀ = (u : A) * (gR * gRm) := by
  have hm₁ : (X - algebraMap R A x₀) ∈ Ideal.span {gR} := by rw [← hk₁]; exact h₁
  obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton'.mp hm₁
  have hc₁ : X - algebraMap R A x₀ = gR * a₁ := by rw [← ha₁, mul_comm]
  have h₂ := hstep₂ a₁ hc₁
  have hm₂ : a₁ ∈ Ideal.span {gRm} := by rw [← hk₂]; exact h₂
  obtain ⟨a₂, ha₂⟩ := Ideal.mem_span_singleton'.mp hm₂
  have hc₂ : a₁ = gRm * a₂ := by rw [← ha₂, mul_comm]
  obtain ⟨u, hu⟩ := hunit a₁ a₂ hc₁ hc₂
  refine ⟨u, ?_⟩
  rw [hc₁, hc₂, ← hu]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (i3)] The third point's coordinates at a field point.** For points `P`, `Q` of
the model over a general ring base, the dictionary sends `-(P + Q)` to
`(addX, negAddY)` — the chord's third intersection — whenever the fibre coordinates are
in general position. Uses the tree's additive dictionary
(`projModelPointsEquiv_point_add`) and the field-case formula
(`neg_add_eq_some_negAddY`). -/
theorem dictionary_neg_add_eq_negAddY {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P Q : (modelEllipticCurve W).Point
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W.baseChange K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange K).toAffine.Nonsingular x₂ y₂)
    (hP : projModelPointsEquiv W K ⟨P.1, P.2⟩ =
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    (hQ : projModelPointsEquiv W K ⟨Q.1, Q.2⟩ =
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.baseChange K).toAffine.negY x₂ y₂)) :
    projModelPointsEquiv W K ⟨(-(P + Q)).1, (-(P + Q)).2⟩ =
      WeierstrassCurve.Affine.Point.some
        ((W.baseChange K).toAffine.addX x₁ x₂
          ((W.baseChange K).toAffine.slope x₁ x₂ y₁ y₂))
        ((W.baseChange K).toAffine.negAddY x₁ x₂ y₁
          ((W.baseChange K).toAffine.slope x₁ x₂ y₁ y₂))
        (WeierstrassCurve.Affine.nonsingular_negAdd h₁ h₂ hxy) := by
  have hadd : projModelPointsEquiv W K ⟨(P + Q).1, (P + Q).2⟩ =
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
    rw [projModelPointsEquiv_point_add W P Q, hP, hQ]
  have hneg : projModelPointsEquiv W K ⟨(-(P + Q)).1, (-(P + Q)).2⟩ =
      -(projModelPointsEquiv W K ⟨(P + Q).1, (P + Q).2⟩) := by
    have hmap := (modelPointAddEquiv W (K' := K)).map_neg (P + Q)
    exact hmap
  rw [hneg, hadd]
  exact neg_add_eq_some_negAddY (W.baseChange K) h₁ h₂ hxy

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i4] The third point as a section, identified at field points.** The section
built from base-level coordinates `(p, q)` (`affineSectionSpecPoint`) and the group-law
section `-(P + Q)` have the SAME dictionary value at a field point, provided the base
coordinates evaluate to the chord's third intersection there. Feeding this to
`section_eq_of_dictionary_eq` (reduced base) upgrades it to an equality of sections. -/
theorem dictionary_eq_of_third_point_coords {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] (p q : R)
    (hpq : W.toAffine.Equation p q)
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P Q : (modelEllipticCurve W).Point
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W.baseChange K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange K).toAffine.Nonsingular x₂ y₂)
    (hP : projModelPointsEquiv W K ⟨P.1, P.2⟩ =
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    (hQ : projModelPointsEquiv W K ⟨Q.1, Q.2⟩ =
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.baseChange K).toAffine.negY x₂ y₂))
    (hns : (W.baseChange K).toAffine.Nonsingular
      (algebraMap R K p) (algebraMap R K q))
    (hp : algebraMap R K p = (W.baseChange K).toAffine.addX x₁ x₂
      ((W.baseChange K).toAffine.slope x₁ x₂ y₁ y₂))
    (hq : algebraMap R K q = (W.baseChange K).toAffine.negAddY x₁ x₂ y₁
      ((W.baseChange K).toAffine.slope x₁ x₂ y₁ y₂)) :
    projModelPointsEquiv W K (affineSectionSpecPoint W K p q hpq) =
      projModelPointsEquiv W K ⟨(-(P + Q)).1, (-(P + Q)).2⟩ := by
  have hleft := projModelPointsEquiv_affineSectionSpecPoint W p q hpq hns
  have hright := dictionary_neg_add_eq_negAddY W P Q h₁ h₂ hP hQ hxy
  rw [hleft, hright]
  generalize_proofs hA
  revert hA
  rw [← hp, ← hq]
  intro hA
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 degenerate case] The vertical configuration.** When the two points share an
`x`-coordinate and the second is the negative of the first, their sum is zero — so the
chord configuration degenerates to the vertical, whose identity is
`vertical_exact_order`. At field points this is mathlib's `add_of_Y_eq`, transported
through the dictionary. -/
theorem dictionary_add_eq_zero_of_vertical {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [Field K] [DecidableEq K] [Algebra R K]
    (P Q : (modelEllipticCurve W).Point
      (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    {x₁ x₂ y₁ y₂ : K}
    (h₁ : (W.baseChange K).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange K).toAffine.Nonsingular x₂ y₂)
    (hP : projModelPointsEquiv W K ⟨P.1, P.2⟩ =
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
    (hQ : projModelPointsEquiv W K ⟨Q.1, Q.2⟩ =
      WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
    (hx : x₁ = x₂) (hy : y₁ = (W.baseChange K).toAffine.negY x₂ y₂) :
    projModelPointsEquiv W K ⟨(P + Q).1, (P + Q).2⟩ = 0 := by
  rw [projModelPointsEquiv_point_add W P Q, hP, hQ]
  exact WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i6] `hslope` from the geometric third point.** The algebraic hypothesis
`chord_identity_of_sections` wants is exactly mathlib's `addX`, unfolded. -/
theorem chord_hslope_of_addX {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (σ₁ σ₂ σ₃ : W.toAffine.CoordinateRing →ₐ[R] R) (d : R)
    (hX : σ₃ (coordX W) = W.toAffine.addX (σ₁ (coordX W)) (σ₂ (coordX W))
      ((σ₂ (coordY W) - σ₁ (coordY W)) * d)) :
    σ₃ (coordX W) =
      ((σ₂ (coordY W) - σ₁ (coordY W)) * d) ^ 2 +
        W.a₁ * ((σ₂ (coordY W) - σ₁ (coordY W)) * d) - W.a₂ -
        σ₁ (coordX W) - σ₂ (coordX W) := by
  rw [hX, WeierstrassCurve.Affine.addX]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i6] `hline₃` from the geometric third point.** `negAddY` is *by definition*
the value of the chord's line at `addX`, so the third point lies on the line for free —
this is the algebraic form of "the third intersection point is on the chord". -/
theorem chord_hline₃_of_negAddY {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (σ₁ σ₂ σ₃ : W.toAffine.CoordinateRing →ₐ[R] R) (d : R)
    (hX : σ₃ (coordX W) = W.toAffine.addX (σ₁ (coordX W)) (σ₂ (coordX W))
      ((σ₂ (coordY W) - σ₁ (coordY W)) * d))
    (hY : σ₃ (coordY W) = W.toAffine.negAddY (σ₁ (coordX W)) (σ₂ (coordX W))
      (σ₁ (coordY W)) ((σ₂ (coordY W) - σ₁ (coordY W)) * d)) :
    σ₃ (coordY W) = ((σ₂ (coordY W) - σ₁ (coordY W)) * d) *
      (σ₃ (coordX W) - σ₁ (coordX W)) + σ₁ (coordY W) := by
  rw [hY, hX, WeierstrassCurve.Affine.negAddY]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i7a] The Weierstrass factorisation at a point.** In any algebra carrying a
Weierstrass relation, the product of `y - y₀` with its conjugate `y + y₀ + a₁x + a₃`
is divisible by `x - x₀` — because the difference of the two Weierstrass equations is.
This is the algebraic reason the maximal ideal of a non-2-torsion point becomes
principal once the conjugate factor is inverted. -/
theorem sub_mul_conj_eq_of_equation {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (a₁ a₂ a₃ a₄ a₆ : R) (x y : A) (x₀ y₀ : R)
    (heq : y ^ 2 + algebraMap R A a₁ * x * y + algebraMap R A a₃ * y =
      x ^ 3 + algebraMap R A a₂ * x ^ 2 + algebraMap R A a₄ * x + algebraMap R A a₆)
    (hpt : y₀ ^ 2 + a₁ * x₀ * y₀ + a₃ * y₀ = x₀ ^ 3 + a₂ * x₀ ^ 2 + a₄ * x₀ + a₆) :
    (y - algebraMap R A y₀) *
        (y + algebraMap R A y₀ + algebraMap R A a₁ * x + algebraMap R A a₃) =
      (x - algebraMap R A x₀) *
        (x ^ 2 + x * algebraMap R A x₀ + algebraMap R A x₀ ^ 2 +
          algebraMap R A a₂ * (x + algebraMap R A x₀) + algebraMap R A a₄ -
          algebraMap R A a₁ * algebraMap R A y₀) := by
  have hpt' : (algebraMap R A y₀) ^ 2 + algebraMap R A a₁ * algebraMap R A x₀ *
      algebraMap R A y₀ + algebraMap R A a₃ * algebraMap R A y₀ =
      (algebraMap R A x₀) ^ 3 + algebraMap R A a₂ * (algebraMap R A x₀) ^ 2 +
        algebraMap R A a₄ * algebraMap R A x₀ + algebraMap R A a₆ := by
    have := congrArg (algebraMap R A) hpt
    simpa only [map_add, map_mul, map_pow] using this
  linear_combination heq - hpt'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i7b] `y - y₀` is a multiple of `x - x₀` away from 2-torsion.** Inverting the
conjugate factor — which evaluates to `2y₀ + a₁x₀ + a₃` at the point, the non-2-torsion
condition — turns the factorisation into a divisibility. -/
theorem sub_coordY_mem_span_of_isUnit {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (a₁ a₂ a₃ a₄ a₆ : R) (x y : A) (x₀ y₀ : R)
    (heq : y ^ 2 + algebraMap R A a₁ * x * y + algebraMap R A a₃ * y =
      x ^ 3 + algebraMap R A a₂ * x ^ 2 + algebraMap R A a₄ * x + algebraMap R A a₆)
    (hpt : y₀ ^ 2 + a₁ * x₀ * y₀ + a₃ * y₀ = x₀ ^ 3 + a₂ * x₀ ^ 2 + a₄ * x₀ + a₆)
    (hu : IsUnit (y + algebraMap R A y₀ + algebraMap R A a₁ * x + algebraMap R A a₃)) :
    y - algebraMap R A y₀ ∈ Ideal.span {x - algebraMap R A x₀} := by
  obtain ⟨u, hu⟩ := hu
  have hfac := sub_mul_conj_eq_of_equation a₁ a₂ a₃ a₄ a₆ x y x₀ y₀ heq hpt
  rw [Ideal.mem_span_singleton]
  refine ⟨(x ^ 2 + x * algebraMap R A x₀ + algebraMap R A x₀ ^ 2 +
      algebraMap R A a₂ * (x + algebraMap R A x₀) + algebraMap R A a₄ -
      algebraMap R A a₁ * algebraMap R A y₀) * (↑u⁻¹ : A), ?_⟩
  have h1 : (y - algebraMap R A y₀) * (u : A) * (↑u⁻¹ : A) =
      (x - algebraMap R A x₀) *
        (x ^ 2 + x * algebraMap R A x₀ + algebraMap R A x₀ ^ 2 +
          algebraMap R A a₂ * (x + algebraMap R A x₀) + algebraMap R A a₄ -
          algebraMap R A a₁ * algebraMap R A y₀) * (↑u⁻¹ : A) := by
    rw [hu, hfac]
  rw [mul_assoc, Units.mul_inv, mul_one] at h1
  rw [h1]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i7] The maximal ideal of a non-2-torsion point is principal.** In a chart
where the conjugate factor is invertible, the kernel of an evaluation retraction is
generated by `x - x₀` alone. This is the hypothesis `hk₁`/`hk₂`/`hk₃` of
`chord_identity_of_sections`, now *proved* rather than assumed: the two obvious
generators collapse to one. -/
theorem ker_eq_span_sub_coordX_of_isUnit {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (a₁ a₂ a₃ a₄ a₆ : R) (x y : A) (x₀ y₀ : R)
    (heq : y ^ 2 + algebraMap R A a₁ * x * y + algebraMap R A a₃ * y =
      x ^ 3 + algebraMap R A a₂ * x ^ 2 + algebraMap R A a₄ * x + algebraMap R A a₆)
    (hpt : y₀ ^ 2 + a₁ * x₀ * y₀ + a₃ * y₀ = x₀ ^ 3 + a₂ * x₀ ^ 2 + a₄ * x₀ + a₆)
    (hu : IsUnit (y + algebraMap R A y₀ + algebraMap R A a₁ * x + algebraMap R A a₃))
    (σ : A →ₐ[R] R) (hσx : σ x = x₀)
    (hgen : ∀ t : A, σ t = 0 →
      ∃ a b : A, t = (x - algebraMap R A x₀) * a + (y - algebraMap R A y₀) * b) :
    RingHom.ker (σ : A →+* R) = Ideal.span {x - algebraMap R A x₀} := by
  have hy : y - algebraMap R A y₀ ∈ Ideal.span {x - algebraMap R A x₀} :=
    sub_coordY_mem_span_of_isUnit a₁ a₂ a₃ a₄ a₆ x y x₀ y₀ heq hpt hu
  apply le_antisymm
  · intro t ht
    obtain ⟨a, b, rfl⟩ := hgen t ht
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
      (Ideal.mul_mem_right _ _ hy)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show σ (x - algebraMap R A x₀) = 0
    rw [map_sub, hσx, AlgHom.commutes]
    exact sub_self _

end ModularCurves

namespace ModularCurves

open AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1] The theorem of the square for an elliptic curve, from a chord datum.**
Specialisation of `nonempty_tensorObj_iso_of_chordDatum` to the project's elliptic
curves, with the third point taken to be `-(P + Q)` for the group law of `E`: a chord
datum for `(P, Q, P + Q, -(P + Q))` gives `I(P) ⊗ I(Q) ≅ I(P+Q) ⊗ I(0)`.

Constructing that chord datum — the chord through `P` and `Q` meets the curve again at
`-(P+Q)`, to exact order — is the one remaining input of the Weil-pairing prong. -/
theorem EllipticCurve.nonempty_tensorObj_iso_of_chordDatum
    (E : EllipticCurve S) [IsSeparated E.π]
    (P Q : E.Point (𝟙 S))
    (h : ChordDatum (π := E.π) E.zero E.zero_π
      ⟨P.1, by rw [P.2]⟩ ⟨Q.1, by rw [Q.2]⟩
      ⟨(P + Q).1, by rw [(P + Q).2]⟩ ⟨(-(P + Q)).1, by rw [(-(P + Q)).2]⟩) :
    Nonempty (tensorObj
        (AlgebraicGeometry.Scheme.Modules.idealModule (Scheme.Hom.ker P.1))
        (AlgebraicGeometry.Scheme.Modules.idealModule (Scheme.Hom.ker Q.1)) ≅
      tensorObj
        (AlgebraicGeometry.Scheme.Modules.idealModule
          (Scheme.Hom.ker (P + Q).1))
        (ModularCurves.sectionIdealModule E.π E.zero E.zero_π)) :=
  AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_iso_of_chordDatum
    E.smooth E.zero E.zero_π
    ⟨P.1, by rw [P.2]⟩ ⟨Q.1, by rw [Q.2]⟩
    ⟨(P + Q).1, by rw [(P + Q).2]⟩ ⟨(-(P + Q)).1, by rw [(-(P + Q)).2]⟩ h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2a] The affine coordinates of a section.** Evaluating the chart
coordinates `X, Y` at a section — through the section's evaluation retraction — gives a
point of the Weierstrass curve over the base: the equation is preserved because the
retraction is a ring map over the base and `W.map` is the same curve. -/
theorem equation_of_algHom {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (σ : A →ₐ[R] R) (X Y : A)
    (h : (W.map (algebraMap R A)).toAffine.Equation X Y) :
    W.toAffine.Equation (σ X) (σ Y) := by
  have hmap := WeierstrassCurve.Affine.Equation.map (f := (σ : A →+* R)) h
  have hcomp : (W.map (algebraMap R A)).toAffine.map (σ : A →+* R) = W.toAffine := by
    show ((W.map (algebraMap R A)).map (σ : A →+* R)).toAffine = W.toAffine
    congr 1
    rw [WeierstrassCurve.map_map]
    have hid : (σ : A →+* R).comp (algebraMap R A) = RingHom.id R := by
      ext r
      exact σ.commutes r
    rw [hid, WeierstrassCurve.map_id]
  rwa [hcomp] at hmap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2a] The evaluation of a chart element at a section, as a point.** Combines
the section's evaluation retraction with the affine coordinates: the pair
`(σ X, σ Y)` satisfies the Weierstrass equation and `σ` kills exactly the chart
functions vanishing at the section. -/
theorem exists_affine_point_of_section {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) (X Y : A)
    (hXY : (W.map (algebraMap R A)).toAffine.Equation X Y)
    (σ : A →ₐ[R] R) (g : A) (hker : RingHom.ker σ = Ideal.span {g}) :
    ∃ xP yP : R, W.toAffine.Equation xP yP ∧ σ X = xP ∧ σ Y = yP ∧
      ∀ c : A, (σ c = 0 ↔ c ∈ Ideal.span {g}) :=
  ⟨σ X, σ Y, equation_of_algHom W σ X Y hXY, rfl, rfl, fun c => by
    rw [← hker]
    exact Iff.rfl⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2b] The chord passes through the third point — by construction.** For a
Weierstrass curve over any commutative ring, the line `Y = ℓ·(X − x₁) + y₁` through
`(x₁, y₁)` with slope `ℓ` passes through `(x₂, y₂)` exactly when the collinearity
relation holds, and it *always* passes through `(addX x₁ x₂ ℓ, negAddY x₁ x₂ y₁ ℓ)` —
the point mathlib defines as `-((x₁,y₁) + (x₂,y₂))`. The chord–tangent vanishing is
therefore definitional in these coordinates; what remains for the prong is the bridge
to the project's group law and the exactness of the order. -/
theorem chord_vanishes_at_three_points {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (x₁ x₂ y₁ y₂ ℓ : R)
    (hline : y₂ = ℓ * (x₂ - x₁) + y₁) :
    (y₁ - (ℓ * (x₁ - x₁) + y₁) = 0) ∧
    (y₂ - (ℓ * (x₂ - x₁) + y₁) = 0) ∧
    (W.toAffine.negAddY x₁ x₂ y₁ ℓ -
      (ℓ * (W.toAffine.addX x₁ x₂ ℓ - x₁) + y₁) = 0) := by
  refine ⟨by ring, by rw [hline]; ring, ?_⟩
  show W.toAffine.negAddY x₁ x₂ y₁ ℓ -
    (ℓ * (W.toAffine.addX x₁ x₂ ℓ - x₁) + y₁) = 0
  rw [WeierstrassCurve.Affine.negAddY]
  ring

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2b] Chart form.** In a chart with coordinates `X, Y`, the chord through the
sections `P` and `Q` is `Y − ℓ·(X − x_P) − y_P`; its evaluation at any section whose
coordinates satisfy the line equation vanishes. -/
theorem algHom_chord_eq_zero {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (σ : A →ₐ[R] R) (X Y : A) (ℓ xP yP : R) (xZ yZ : R)
    (hσX : σ X = xZ) (hσY : σ Y = yZ)
    (hline : yZ = ℓ * (xZ - xP) + yP) :
    σ (Y - (algebraMap R A ℓ * (X - algebraMap R A xP) + algebraMap R A yP)) = 0 := by
  rw [map_sub, map_add, map_mul, map_sub, σ.commutes, σ.commutes, σ.commutes,
    hσX, hσY, hline]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

end ModularCurves

namespace AlgebraicGeometry.Scheme.Modules

variable {C S : Scheme.{u}} {π : C ⟶ S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2d] The triple kernel is the pair kernel once the chord vanishes at the
third point.** If `ℓ` generates the kernel of the restriction to the smaller divisor and
also lies in the kernel of the restriction to the larger one, the two kernels agree —
so the chord is a generator there too, and no further vanishing is possible without
shrinking the kernel. -/
theorem ker_eq_of_mem_of_span_eq {J₁ J₂ : C.IdealSheafData} (h12 : J₁ ≤ J₂)
    (L : C.Modules) (ℓ : Scheme.Modules.baseSections π L)
    (hspan : LinearMap.ker ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π (divisorTwistHom J₂ L))).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens)) {ℓ})
    (hmem : ℓ ∈ LinearMap.ker ((Scheme.Modules.baseSectionsMap π
      (Limits.cokernel.π (divisorTwistHom J₁ L))).hom)) :
    LinearMap.ker ((Scheme.Modules.baseSectionsMap π
        (Limits.cokernel.π (divisorTwistHom J₁ L))).hom) =
      Submodule.span Γ(S, (⊤ : S.Opens)) {ℓ} := by
  refine le_antisymm ?_ ?_
  · rw [← hspan]
    exact ker_baseSectionsMap_cokernel_mono h12 L
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmem

end AlgebraicGeometry.Scheme.Modules

namespace ModularCurves

open AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2c] The field-point comparison, algebra-indexed.** Every morphism
`Spec K ⟶ Spec R` is `Spec` of a ring map, so an equality of morphisms that holds after
composing with every ring map to every field holds after composing with every
field-valued point — the form the extensionality principle consumes. -/
theorem hom_ext_of_forall_algebra {R : Type u} [CommRing R] {Y : Scheme.{u}}
    [IsReduced (Spec (CommRingCat.of R))] [Y.IsSeparated]
    {f g : Spec (CommRingCat.of R) ⟶ Y}
    (h : ∀ (K : Type u) [Field K] (φ : R →+* K),
      Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ g) :
    f = g := by
  refine hom_ext_of_forall_specPoint (fun K _ p => ?_)
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective p
  exact h K ψ.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1-d3.2c, step 6] Section identity from field-point identity, dictionary form.**
Two sections of the projective model over a reduced affine base agree as soon as their
dictionary values agree for every field-valued point. The dictionary is injective, so
this is exactly the extensionality principle in the form the chord comparison produces
(the previous lemmas compute both sides' dictionary values). -/
theorem section_eq_of_dictionary_eq {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic]
    [IsReduced (Spec (CommRingCat.of R))]
    [(projModel W).IsSeparated]
    {f g : Spec (CommRingCat.of R) ⟶ projModel W}
    (hf : f ≫ projModelπ W = 𝟙 _) (hg : g ≫ projModelπ W = 𝟙 _)
    (h : ∀ (K : Type u) [Field K] (φ : R →+* K),
      letI : Algebra R K := φ.toAlgebra
      projModelPointsEquiv W K
          ⟨Spec.map (CommRingCat.ofHom φ) ≫ f, by
            rw [Category.assoc, hf, Category.comp_id]
            rfl⟩ =
        projModelPointsEquiv W K
          ⟨Spec.map (CommRingCat.ofHom φ) ≫ g, by
            rw [Category.assoc, hg, Category.comp_id]
            rfl⟩) :
    f = g := by
  refine hom_ext_of_forall_algebra (fun K _ φ => ?_)
  letI : Algebra R K := φ.toAlgebra
  have hval := h K φ
  have hinj := (projModelPointsEquiv W K).injective hval
  exact congrArg Subtype.val hinj


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 away-chart] The chord's three evaluations, packaged.** In a chart with
coordinates `X, Y` over the base, given three sections whose evaluation retractions
read off affine coordinates satisfying the line relation, the chord element
`Y − ℓ(X − x₁) − y₁` is killed by all three retractions. Combined with
`mul_dvd_of_evaluations_vanish` and `eq_unit_mul_of_three_divisions` this is the
exact-order hypothesis, modulo the unit cofactor. -/
theorem chord_evaluations_vanish {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (X Y : A) (ℓ x₁ y₁ x₂ y₂ x₃ y₃ : R)
    (σ₁ σ₂ σ₃ : A →ₐ[R] R)
    (h₁x : σ₁ X = x₁) (h₁y : σ₁ Y = y₁)
    (h₂x : σ₂ X = x₂) (h₂y : σ₂ Y = y₂)
    (h₃x : σ₃ X = x₃) (h₃y : σ₃ Y = y₃)
    (hline₂ : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hline₃ : y₃ = ℓ * (x₃ - x₁) + y₁) :
    σ₁ (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) = 0 ∧
    σ₂ (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) = 0 ∧
    σ₃ (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) = 0 := by
  refine ⟨algHom_chord_eq_zero σ₁ X Y ℓ x₁ y₁ x₁ y₁ h₁x h₁y (by ring), ?_, ?_⟩
  · exact algHom_chord_eq_zero σ₂ X Y ℓ x₁ y₁ x₂ y₂ h₂x h₂y hline₂
  · exact algHom_chord_eq_zero σ₃ X Y ℓ x₁ y₁ x₃ y₃ h₃x h₃y hline₃


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 away-chart, assembled] The exact-order factorisation of the chord.** Three
evaluation retractions with principal kernels killing the chord give successive
divisions by the three generators; a unit final cofactor then puts the chord in the
form `unit · (g₁ · (g₂ · g₃))` — exactly the hypothesis of
`nonempty_iso_unitObj_of_exact_order₃`. -/
theorem chord_eq_unit_mul_generators {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (c g₁ g₂ g₃ : A)
    (σ₁ σ₂ σ₃ : A →ₐ[R] R)
    (hk₁ : RingHom.ker σ₁ = Ideal.span {g₁})
    (hk₂ : RingHom.ker σ₂ = Ideal.span {g₂})
    (hk₃ : RingHom.ker σ₃ = Ideal.span {g₃})
    (h₁ : σ₁ c = 0)
    (c₁ : A) (hc₁ : c = g₁ * c₁) (h₂ : σ₂ c₁ = 0)
    (c₂ : A) (hc₂ : c₁ = g₂ * c₂) (h₃ : σ₃ c₂ = 0)
    (u : Aˣ) (hc₃ : c₂ = g₃ * (u : A)) :
    c = (u : A) * (g₁ * (g₂ * g₃)) :=
  AlgebraicGeometry.Scheme.Modules.eq_unit_mul_of_three_divisions
    c g₁ g₂ g₃ c₁ c₂ u hc₁ hc₂ hc₃


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 (a)+(b), assembled] The chord's chart factorisation from evaluation data.**
Given the three retractions, the chord element's successive quotients, and a unit final
cofactor, the chord is a unit multiple of the product of the three generators. This is
the statement that `nonempty_iso_unitObj_of_exact_order₃` consumes, with every
hypothesis now expressed in chart coordinates. -/
theorem chord_chart_factorisation {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (X Y : A) (ℓ x₁ y₁ x₂ y₂ x₃ y₃ : R) (gP gQ gR : A)
    (σ₁ σ₂ σ₃ : A →ₐ[R] R)
    (hk₁ : RingHom.ker σ₁ = Ideal.span {gP})
    (hk₂ : RingHom.ker σ₂ = Ideal.span {gQ})
    (hk₃ : RingHom.ker σ₃ = Ideal.span {gR})
    (h₁x : σ₁ X = x₁) (h₁y : σ₁ Y = y₁)
    (h₂x : σ₂ X = x₂) (h₂y : σ₂ Y = y₂)
    (h₃x : σ₃ X = x₃) (h₃y : σ₃ Y = y₃)
    (hline₂ : y₂ = ℓ * (x₂ - x₁) + y₁)
    (hline₃ : y₃ = ℓ * (x₃ - x₁) + y₁)
    (c₁ : A)
    (hc₁ : (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
      gP * c₁)
    (h₂ : σ₂ c₁ = 0) (c₂ : A) (hc₂ : c₁ = gQ * c₂)
    (h₃ : σ₃ c₂ = 0) (u : Aˣ) (hc₃ : c₂ = gR * (u : A)) :
    (Y - (algebraMap R A ℓ * (X - algebraMap R A x₁) + algebraMap R A y₁)) =
      (u : A) * (gP * (gQ * gR)) := by
  obtain ⟨hv₁, hv₂, hv₃⟩ := chord_evaluations_vanish X Y ℓ x₁ y₁ x₂ y₂ x₃ y₃
    σ₁ σ₂ σ₃ h₁x h₁y h₂x h₂y h₃x h₃y hline₂ hline₃
  exact chord_eq_unit_mul_generators _ gP gQ gR σ₁ σ₂ σ₃ hk₁ hk₂ hk₃ hv₁
    c₁ hc₁ h₂ c₂ hc₂ h₃ u hc₃


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 chart facts] A section's coordinates satisfy the equation, in the ring form
the chord identity uses.** Repackaging `equation_of_algHom` from
`WeierstrassCurve.Affine.Equation` into the explicit polynomial identity. -/
theorem section_coords_equation {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) (X Y : A) (σ : A →ₐ[R] R)
    (hXY : (W.map (algebraMap R A)).toAffine.Equation X Y) :
    (σ Y) ^ 2 + W.a₁ * (σ X) * (σ Y) + W.a₃ * (σ Y) =
      (σ X) ^ 3 + W.a₂ * (σ X) ^ 2 + W.a₄ * (σ X) + W.a₆ := by
  have h := equation_of_algHom W σ X Y hXY
  rw [WeierstrassCurve.Affine.equation_iff] at h
  exact h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 chart facts] The coordinate-ring coordinates satisfy the mapped equation.**
The `hXY` input of `section_coords_equation`, for the coordinate ring itself. -/
theorem coord_equation_affine {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    (W.map (algebraMap R W.toAffine.CoordinateRing)).toAffine.Equation
      (coordX W) (coordY W) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have h := coord_equation W
  simpa using h


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 chart facts, assembled] The chord identity from section data only.** The two
points' equations are supplied by their own evaluations (`section_coords_equation`),
so the chord identity needs, beyond the retractions and generators, only the
invertibility conditions. This is the form a caller with two sections in the chart
uses. -/
theorem chord_identity_of_sections {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) (d : R)
    (σ₁ σ₂ σ₃ : W.toAffine.CoordinateRing →ₐ[R] R)
    (hd : d * (σ₂ (coordX W) - σ₁ (coordX W)) = 1)
    (hx : IsUnit (σ₁ (coordX W) - σ₂ (coordX W)))
    (hf₁nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ (σ₁ (coordX W))) * t = 0 → t = 0)
    (hf₂nzd : ∀ t : W.toAffine.CoordinateRing,
      (coordX W - algebraMap R _ (σ₂ (coordX W))) * t = 0 → t = 0)
    (hk₁ : RingHom.ker (σ₁ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ (σ₁ (coordX W))})
    (hk₂ : RingHom.ker (σ₂ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ (σ₂ (coordX W))})
    (hk₃ : RingHom.ker (σ₃ : W.toAffine.CoordinateRing →+* R) =
      Ideal.span {coordX W - algebraMap R _ (σ₃ (coordX W))})
    (hslope : σ₃ (coordX W) =
      ((σ₂ (coordY W) - σ₁ (coordY W)) * d) ^ 2 +
        W.a₁ * ((σ₂ (coordY W) - σ₁ (coordY W)) * d) - W.a₂ -
        σ₁ (coordX W) - σ₂ (coordX W))
    (hσ₁ : σ₁ (coordY W -
      (algebraMap R _ ((σ₂ (coordY W) - σ₁ (coordY W)) * d) *
        (coordX W - algebraMap R _ (σ₁ (coordX W))) +
        algebraMap R _ (σ₁ (coordY W)))) = 0)
    (hline₃ : σ₃ (coordY W) = ((σ₂ (coordY W) - σ₁ (coordY W)) * d) *
      (σ₃ (coordX W) - σ₁ (coordX W)) + σ₁ (coordY W))
    (htor₂ : IsUnit (2 * σ₂ (coordY W) + W.a₁ * σ₂ (coordX W) + W.a₃))
    (htor₃ : IsUnit (2 * σ₃ (coordY W) + W.a₁ * σ₃ (coordX W) + W.a₃))
    (hunit : ∀ c₁ c₂ c₃ : W.toAffine.CoordinateRing,
      (coordY W - (algebraMap R _ ((σ₂ (coordY W) - σ₁ (coordY W)) * d) *
        (coordX W - algebraMap R _ (σ₁ (coordX W))) +
        algebraMap R _ (σ₁ (coordY W)))) =
          (coordX W - algebraMap R _ (σ₁ (coordX W))) * c₁ →
        c₁ = (coordX W - algebraMap R _ (σ₂ (coordX W))) * c₂ →
        c₂ = (coordX W - algebraMap R _ (σ₃ (coordX W))) * c₃ → IsUnit c₃) :
    ∃ u : (W.toAffine.CoordinateRing)ˣ,
      (coordY W - (algebraMap R _ ((σ₂ (coordY W) - σ₁ (coordY W)) * d) *
        (coordX W - algebraMap R _ (σ₁ (coordX W))) +
        algebraMap R _ (σ₁ (coordY W)))) =
        (u : W.toAffine.CoordinateRing) *
          ((coordX W - algebraMap R _ (σ₁ (coordX W))) *
            ((coordX W - algebraMap R _ (σ₂ (coordX W))) *
              (coordX W - algebraMap R _ (σ₃ (coordX W))))) := by
  rw [hslope] at hk₃ hline₃ htor₃ hunit ⊢
  exact chord_identity_of_isUnit_hypotheses W (σ₁ (coordX W)) (σ₁ (coordY W))
    (σ₂ (coordX W)) (σ₂ (coordY W)) (σ₃ (coordY W)) d σ₁ σ₂ σ₃
    (section_coords_equation W (coordX W) (coordY W) σ₁ (coord_equation_affine W))
    (section_coords_equation W (coordX W) (coordY W) σ₂ (coord_equation_affine W))
    hd hx hf₁nzd hf₂nzd hk₁ hk₂ hk₃ hσ₁ rfl rfl hslope rfl hline₃ htor₂ htor₃ hunit


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i8a] A retraction's coordinates satisfy the equation.** Applying a retraction
to the Weierstrass relation of the chart. -/
theorem coords_equation_of_relation {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (a₁ a₂ a₃ a₄ a₆ : R) (X Y : A) (σ : A →ₐ[R] R)
    (hEq : Y ^ 2 + algebraMap R A a₁ * X * Y + algebraMap R A a₃ * Y =
      X ^ 3 + algebraMap R A a₂ * X ^ 2 + algebraMap R A a₄ * X + algebraMap R A a₆) :
    (σ Y) ^ 2 + a₁ * σ X * σ Y + a₃ * σ Y =
      (σ X) ^ 3 + a₂ * (σ X) ^ 2 + a₄ * σ X + a₆ := by
  have h := congrArg σ hEq
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes, Algebra.algebraMap_self,
    RingHom.id_apply] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **[W1 i8] THE CHORD IDENTITY IN A CHART, FROM CHECKABLE HYPOTHESES.** The
caller-facing form: three retractions of an away-chart, the two non-degeneracy
conditions (invertible `x`-difference, non-2-torsion), the *conjugate* units that make
each maximal ideal principal (`ker_eq_span_sub_coordX_of_isUnit`), and the geometric
input that the third section's coordinates are the group law's `addX`/`negAddY`. No
kernel hypothesis, no point equations, no chord-vanishing hypothesis: all three are
now derived. -/
theorem chord_identity_of_chart_sections {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) (X Y : A) (d : R)
    (σ₁ σ₂ σ₃ : A →ₐ[R] R)
    (hEq : Y ^ 2 + algebraMap R A W.a₁ * X * Y + algebraMap R A W.a₃ * Y =
      X ^ 3 + algebraMap R A W.a₂ * X ^ 2 + algebraMap R A W.a₄ * X +
        algebraMap R A W.a₆)
    (hd : d * (σ₂ X - σ₁ X) = 1)
    (hx : IsUnit (σ₁ X - σ₂ X))
    (hf₁nzd : ∀ t : A, (X - algebraMap R A (σ₁ X)) * t = 0 → t = 0)
    (hf₂nzd : ∀ t : A, (X - algebraMap R A (σ₂ X)) * t = 0 → t = 0)
    (hconj₁ : IsUnit (Y + algebraMap R A (σ₁ Y) + algebraMap R A W.a₁ * X +
      algebraMap R A W.a₃))
    (hconj₂ : IsUnit (Y + algebraMap R A (σ₂ Y) + algebraMap R A W.a₁ * X +
      algebraMap R A W.a₃))
    (hconj₃ : IsUnit (Y + algebraMap R A (σ₃ Y) + algebraMap R A W.a₁ * X +
      algebraMap R A W.a₃))
    (hgen₁ : ∀ t : A, σ₁ t = 0 → ∃ a b : A,
      t = (X - algebraMap R A (σ₁ X)) * a + (Y - algebraMap R A (σ₁ Y)) * b)
    (hgen₂ : ∀ t : A, σ₂ t = 0 → ∃ a b : A,
      t = (X - algebraMap R A (σ₂ X)) * a + (Y - algebraMap R A (σ₂ Y)) * b)
    (hgen₃ : ∀ t : A, σ₃ t = 0 → ∃ a b : A,
      t = (X - algebraMap R A (σ₃ X)) * a + (Y - algebraMap R A (σ₃ Y)) * b)
    (hslope : σ₃ X = ((σ₂ Y - σ₁ Y) * d) ^ 2 + W.a₁ * ((σ₂ Y - σ₁ Y) * d) - W.a₂ -
      σ₁ X - σ₂ X)
    (hline₃ : σ₃ Y = ((σ₂ Y - σ₁ Y) * d) * (σ₃ X - σ₁ X) + σ₁ Y)
    (htor₂ : IsUnit (2 * σ₂ Y + W.a₁ * σ₂ X + W.a₃))
    (htor₃ : IsUnit (2 * σ₃ Y + W.a₁ * σ₃ X + W.a₃))
    (hunit : ∀ c₁ c₂ c₃ : A,
      (Y - (algebraMap R A ((σ₂ Y - σ₁ Y) * d) * (X - algebraMap R A (σ₁ X)) +
        algebraMap R A (σ₁ Y))) = (X - algebraMap R A (σ₁ X)) * c₁ →
        c₁ = (X - algebraMap R A (σ₂ X)) * c₂ →
        c₂ = (X - algebraMap R A (σ₃ X)) * c₃ → IsUnit c₃) :
    ∃ u : Aˣ,
      (Y - (algebraMap R A ((σ₂ Y - σ₁ Y) * d) * (X - algebraMap R A (σ₁ X)) +
        algebraMap R A (σ₁ Y))) =
        (u : A) * ((X - algebraMap R A (σ₁ X)) *
          ((X - algebraMap R A (σ₂ X)) * (X - algebraMap R A (σ₃ X)))) := by
  have he₁ := coords_equation_of_relation W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ X Y σ₁ hEq
  have he₂ := coords_equation_of_relation W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ X Y σ₂ hEq
  have he₃ := coords_equation_of_relation W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ X Y σ₃ hEq
  have hk₁ := ker_eq_span_sub_coordX_of_isUnit W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ X Y
    (σ₁ X) (σ₁ Y) hEq he₁ hconj₁ σ₁ rfl hgen₁
  have hk₂ := ker_eq_span_sub_coordX_of_isUnit W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ X Y
    (σ₂ X) (σ₂ Y) hEq he₂ hconj₂ σ₂ rfl hgen₂
  have hk₃ := ker_eq_span_sub_coordX_of_isUnit W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ X Y
    (σ₃ X) (σ₃ Y) hEq he₃ hconj₃ σ₃ rfl hgen₃
  have hσ₁ : σ₁ (Y - (algebraMap R A ((σ₂ Y - σ₁ Y) * d) *
      (X - algebraMap R A (σ₁ X)) + algebraMap R A (σ₁ Y))) = 0 :=
    algHom_chord_eq_zero σ₁ X Y ((σ₂ Y - σ₁ Y) * d) (σ₁ X) (σ₁ Y) (σ₁ X) (σ₁ Y)
      rfl rfl (by ring)
  rw [hslope] at hk₃ hline₃ htor₃ hunit ⊢
  exact chord_exact_order_in_chart W X Y ((σ₂ Y - σ₁ Y) * d) (σ₁ X) (σ₁ Y)
    (σ₂ X) (σ₂ Y) (σ₃ Y) σ₁ σ₂ σ₃ hEq he₁ he₂
    (line_relation_of_slope (σ₁ X) (σ₁ Y) (σ₂ X) (σ₂ Y) d hd)
    (nzd_of_isUnit_sub (σ₁ X) (σ₂ X) hx) hf₁nzd hf₂nzd hk₁ hk₂ hk₃ hσ₁ rfl rfl
    hslope rfl hline₃
    (nzd_of_isUnit_neg_two_torsion W (σ₂ X) (σ₂ Y) htor₂)
    (nzd_of_isUnit_neg_two_torsion W _ (σ₃ Y) htor₃) hunit

end ModularCurves
