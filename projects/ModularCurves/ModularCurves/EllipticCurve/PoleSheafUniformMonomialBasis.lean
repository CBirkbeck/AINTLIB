/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafMonomialSequence
import ModularCurves.EllipticCurve.PoleSheafSuccessorBasis
import ModularCurves.EllipticCurve.PoleSheafSuccessorHOne

/-!
# Compatible monomial bases in every positive pole order

A basis of the first pole module and normalized sections of pole orders two
and three extend recursively to compatible bases of all positive pole modules.
The last vector in each successor basis is the corresponding normalized
monomial.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace ModularCurves

private theorem existsMonomialBasisStep
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (n : ℕ)
    (b : Module.Basis (Fin (n + 1)) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)))) :
    ∃ b' : Module.Basis (Fin ((n + 1) + 1)) Γ(S, (⊤ : S.Opens))
        (Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz ((n + 1) + 1))),
      (∀ i : Fin (n + 1),
        b' (Fin.castAdd 1 i) =
          Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz (n + 1)) (b i)) ∧
        b' (Fin.last (n + 1)) =
          sectionPoleSheafPower_normalizedMonomial z hz x y n := by
  have hH :=
    sectionPoleSheafPower_subsingleton_H_one_of_one_of_affine_neighborhood
      hsm z hz U hU hHOne (show 1 ≤ n + 1 by omega)
  exact sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator
    hsm z hz U hU r hspan hnzd (n + 1) hH b
      (sectionPoleSheafPower_normalizedMonomial z hz x y n)
      (sectionPoleSheafPower_normalizedMonomial_coordinate
        hsm z hz U hU r hspan hnzd x hx y hy n)

private noncomputable def monomialBasisStep
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (n : ℕ)
    (b : Module.Basis (Fin (n + 1)) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)))) :
    Module.Basis (Fin ((n + 1) + 1)) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz ((n + 1) + 1))) :=
  Classical.choose
    (existsMonomialBasisStep hsm z hz U hU r hspan hnzd
      hHOne x hx y hy n b)

/-- Compatible bases of all positive pole modules. The basis at order one is
the supplied basis; every later basis appends the next normalized monomial. -/
noncomputable def sectionPoleSheafPower_monomialBasis
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1)))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    (n : ℕ) → Module.Basis (Fin (n + 1)) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz (n + 1)))
  | 0 => bOne
  | n + 1 =>
      monomialBasisStep hsm z hz U hU r hspan hnzd hHOne
        x hx y hy n
        (sectionPoleSheafPower_monomialBasis
          hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n)

@[simp]
theorem sectionPoleSheafPower_monomialBasis_zero
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1)))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1) :
    sectionPoleSheafPower_monomialBasis
      hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy 0 = bOne :=
  rfl

/-- The inherited vectors in a successor monomial basis are the images of
the preceding basis under the pole-filtration inclusion. -/
theorem sectionPoleSheafPower_monomialBasis_succ_castAdd
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1)))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (n : ℕ) (i : Fin (n + 1)) :
    sectionPoleSheafPower_monomialBasis
        hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy
        (n + 1) (Fin.castAdd 1 i) =
      Scheme.Modules.baseSectionsMap π
        (sectionPoleSheafSuccHom π z hz (n + 1))
        (sectionPoleSheafPower_monomialBasis
          hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n i) := by
  exact (Classical.choose_spec
    (existsMonomialBasisStep hsm z hz U hU r hspan hnzd
      hHOne x hx y hy n
      (sectionPoleSheafPower_monomialBasis
        hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n))).1 i

/-- The last vector in a successor monomial basis is the normalized monomial
of that pole order. -/
theorem sectionPoleSheafPower_monomialBasis_succ_last
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1))
    (hHOne : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz 1).sheaf 1))
    (bOne : Module.Basis (Fin 1) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz 1)))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 2))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 1 x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz 3))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd 2 y = 1)
    (n : ℕ) :
    sectionPoleSheafPower_monomialBasis
        hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy
        (n + 1) (Fin.last (n + 1)) =
      sectionPoleSheafPower_normalizedMonomial z hz x y n := by
  exact (Classical.choose_spec
    (existsMonomialBasisStep hsm z hz U hU r hspan hnzd
      hHOne x hx y hy n
      (sectionPoleSheafPower_monomialBasis
        hsm z hz U hU r hspan hnzd hHOne bOne x hx y hy n))).2

end ModularCurves
