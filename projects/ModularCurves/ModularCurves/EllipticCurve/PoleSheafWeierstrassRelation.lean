/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafMonomialBasis

/-!
# The Weierstrass relation from the pole filtration

The rank-six pole basis makes the square of a normalized pole-order-three
section monic over the cube of a normalized pole-order-two section.
-/

namespace Module.Basis

/-- An element with final coordinate one in a six-element basis satisfies a
linear relation in generalized Weierstrass form. -/
theorem exists_fin_six_weierstrass_relation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis (Fin 6) R M) (q : M)
    (hq : b.repr q (Fin.last 5) = 1) :
    ∃ a₁ a₂ a₃ a₄ a₆ : R,
      q + a₁ • b 4 + a₃ • b 2 =
        b 5 + a₂ • b 3 + a₄ • b 1 + a₆ • b 0 := by
  let c := b.repr q
  refine ⟨-c 4, c 3, -c 2, c 1, c 0, ?_⟩
  have hq5 : b.repr q (5 : Fin 6) = 1 := hq
  apply b.ext_elem
  intro i
  fin_cases i <;> simp [c, hq5]

end Module.Basis

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

/-- In a compatible sixth-pole basis ending in `x³`, the final coordinate of
`y²` is one when `x` and `y` have normalized leading pole coordinates. -/
theorem sectionPoleSheafPower_six_baseSectionsBasis_repr_y_sq_last_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (b5 : Module.Basis (Fin 5) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 5)))
    (b6 : Module.Basis (Fin 6) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 6)))
    (hb6 : ∀ i : Fin 5,
      b6 (Fin.castAdd 1 i) =
        Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz 5) (b5 i))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (hb6x3 : b6 (Fin.last 5) =
      sectionPoleSheafPower_baseSectionsMul z hz 2 4
        (x ⊗ₜ sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))) :
    b6.repr (sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y))
        (Fin.last 5) = 1 := by
  let x2 := sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x)
  let x3 := sectionPoleSheafPower_baseSectionsMul z hz 2 4 (x ⊗ₜ x2)
  let y2 := sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y)
  have hx2 : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 3 x2 = 1 := by
    calc
      _ = sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
            hsm z hz U hU r hspan hnzd 1 x *
          sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
            hsm z hz U hU r hspan hnzd 1 x :=
        sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_mul
          hsm z hz U hU r hspan hnzd 1 1 x x
      _ = 1 := by rw [hx, one_mul]
  have hx3 : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 5 x3 = 1 := by
    calc
      _ = sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
            hsm z hz U hU r hspan hnzd 1 x *
          sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
            hsm z hz U hU r hspan hnzd 3 x2 :=
        sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_mul
          hsm z hz U hU r hspan hnzd 1 3 x x2
      _ = 1 := by rw [hx, hx2, one_mul]
  have hy2 : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 5 y2 = 1 := by
    calc
      _ = sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
            hsm z hz U hU r hspan hnzd 2 y *
          sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
            hsm z hz U hU r hspan hnzd 2 y :=
        sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_mul
          hsm z hz U hU r hspan hnzd 2 2 y y
      _ = 1 := by rw [hy, one_mul]
  change b6.repr y2 (Fin.last 5) = 1
  rw [sectionPoleSheafPower_succ_baseSectionsBasis_repr_last_of_CartierGenerator
    hsm z hz U hU r hspan hnzd 5 b5 b6 x3 hb6]
  · exact hy2
  · simpa only [x3, x2] using hb6x3
  · exact hx3

/-- Normalized pole-order-two and pole-order-three sections satisfy a generalized
Weierstrass relation in any compatible sixth-pole basis ending in `x³`. -/
theorem sectionPoleSheafPower_six_baseSectionsBasis_exists_weierstrass_relation_of_CartierGenerator
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (b5 : Module.Basis (Fin 5) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 5)))
    (b6 : Module.Basis (Fin 6) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π (sectionPoleSheafPower π z hz 6)))
    (hb6 : ∀ i : Fin 5,
      b6 (Fin.castAdd 1 i) =
        Scheme.Modules.baseSectionsMap π
          (sectionPoleSheafSuccHom π z hz 5) (b5 i))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (hb6x3 : b6 (Fin.last 5) =
      sectionPoleSheafPower_baseSectionsMul z hz 2 4
        (x ⊗ₜ sectionPoleSheafPower_baseSectionsMul z hz 2 2 (x ⊗ₜ x))) :
    ∃ a₁ a₂ a₃ a₄ a₆ : Γ(S, (⊤ : S.Opens)),
      sectionPoleSheafPower_baseSectionsMul z hz 3 3 (y ⊗ₜ y) +
          a₁ • b6 4 + a₃ • b6 2 =
        b6 5 + a₂ • b6 3 + a₄ • b6 1 + a₆ • b6 0 := by
  apply b6.exists_fin_six_weierstrass_relation
  exact sectionPoleSheafPower_six_baseSectionsBasis_repr_y_sq_last_of_CartierGenerator
    hsm z hz U hU r hspan hnzd b5 b6 hb6 x hx y hy hb6x3

end ModularCurves
