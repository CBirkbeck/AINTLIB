/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.PoleSheafSuccessorBasis
import ModularCurves.EllipticCurve.PoleSheafSuccessorCoordinateMul

/-!
# Successor bases from products of pole sections

The product of two normalized pole sections is a normalized lift of the next
rank-one pole quotient, so it extends a basis of the preceding pole module.
-/

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TensorProduct

universe u

namespace ModularCurves

/-- Two normalized pole sections multiply to the final vector of a compatible
basis of the corresponding successor pole module. -/
theorem sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator_mul
    {C S : Scheme.{u}} {π : C ⟶ S}
    (hsm : SmoothOfRelativeDimension 1 π) [IsSeparated π]
    (z : S ⟶ C) (hz : z ≫ π = 𝟙 S)
    (U : C.affineOpens) (hU : z ⁻¹ᵁ U.1 = ⊤)
    (r : Γ(C, U.1)) (hspan : z.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(C, U.1)) (m n : ℕ)
    (hH : Subsingleton (CategoryTheory.Sheaf.H
      (sectionPoleSheafPower π z hz ((m + 1) + n)).sheaf 1))
    (b : Module.Basis (Fin ((m + 1) + n)) Γ(S, (⊤ : S.Opens))
      (Scheme.Modules.baseSections π
        (sectionPoleSheafPower π z hz ((m + 1) + n))))
    (x : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (m + 1)))
    (hx : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd m x = 1)
    (y : Scheme.Modules.baseSections π
      (sectionPoleSheafPower π z hz (n + 1)))
    (hy : sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd n y = 1) :
    ∃ b' : Module.Basis (Fin (((m + 1) + n) + 1)) Γ(S, (⊤ : S.Opens))
        (Scheme.Modules.baseSections π
          (sectionPoleSheafPower π z hz (((m + 1) + n) + 1))),
      (∀ i : Fin ((m + 1) + n),
        b' (Fin.castAdd 1 i) =
          Scheme.Modules.baseSectionsMap π
            (sectionPoleSheafSuccHom π z hz ((m + 1) + n)) (b i)) ∧
        b' (Fin.last ((m + 1) + n)) =
          sectionPoleSheafPower_baseSectionsMul z hz
            (m + 1) (n + 1) (x ⊗ₜ y) := by
  apply sectionPoleSheafPower_succ_baseSectionsBasisOfCartierGenerator
    hsm z hz U hU r hspan hnzd ((m + 1) + n) hH b
      (sectionPoleSheafPower_baseSectionsMul z hz (m + 1) (n + 1) (x ⊗ₜ y))
  change sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator
      hsm z hz U hU r hspan hnzd ((m + 1) + n)
        (sectionPoleSheafPower_baseSectionsMul z hz
          (m + 1) (n + 1) (x ⊗ₜ y)) = 1
  rw [sectionPoleSheafPower_succ_baseSectionsCoordinateOfCartierGenerator_mul,
    hx, hy, one_mul]

end ModularCurves
