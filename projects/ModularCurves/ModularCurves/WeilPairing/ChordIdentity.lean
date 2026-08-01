/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.WeilPairing.LineVerticalAssembly
import ModularCurves.EllipticCurve.PointsDictionary
import ModularCurves.EllipticCurve.AdditionSpecPoints

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


end ModularCurves
